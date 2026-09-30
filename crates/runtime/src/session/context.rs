//! Scoped host invocations. Package acceptance continues to belong to the kernel.
//!
//! Object-store publication and `SQLite` writes never straddle an await here.
//! The root input of an invocation is published in the same critical section
//! as its invocation row, and a receipt's bytes in the same critical section
//! as its event row. The only orphan a crash can leave is the documented
//! synchronous straddle every commit shares: the object published, the row
//! write failed, and nothing references the blob.
use super::super::sqlite::context::{ContextWriteError, PreparedReceipt, link_submission};
use super::{
    ActivationProposal, Arc, ContentDigest, ContentId, Payload, ProposalDecision, Range,
    SessionCore, SessionError, SessionHandle, SessionState, SessionStatus, SubmissionCustody,
    require_readable,
};
use crate::context::{
    BoundTrigger, InvocationData, InvocationLease, member_descriptor, package_key, storage,
};
use crate::context::{
    ContextContribution, ContextError, ContextEvent, ContextMode, ContextPolicy, ContextResponse,
    InitialContext, InvocationHandle, InvocationId, InvocationRecord, InvocationStatus,
    InvocationTrigger, PackageGrant, ReceiptState, ViewGrant,
};
use ontography_calculus::{Emission, OutputAuthority, PackageId};
use ontography_content::package::{
    PackageEnvelope, PackageStore, ResolvedEntryKind, ResolvedPackage,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// The facts of one submission, in the canonical encoding whose digest is
/// the commitment an accepted retry must repeat.
struct SubmissionFacts<'a> {
    node_id: &'a str,
    trigger: &'a BoundTrigger,
    received: &'a [PackageId],
    result: &'a Payload,
    emissions: &'a [Emission],
    contents: &'a [ContentId],
}

impl SubmissionFacts<'_> {
    const ENCODING: &'static [u8] = b"ontography-submission/v1\0";

    /// Digests the facts: the bound node, the trigger (root authority and
    /// input digest, or the received packages), the result digest, every
    /// emission's destination, authority, and payload digest, and the declared
    /// content ids. Every variable-length field is length-prefixed and every
    /// sequence is count-prefixed, so distinct fact sets never share an
    /// encoding, and only digests of payloads are folded in, so the
    /// commitment is bounded in size.
    fn commitment(&self) -> ContentDigest {
        let mut out = Vec::new();
        push_bytes(&mut out, Self::ENCODING);
        push_bytes(&mut out, self.node_id.as_bytes());
        match self.trigger {
            BoundTrigger::Root {
                authority, input, ..
            } => {
                out.push(0);
                push_authority(&mut out, authority);
                out.extend_from_slice(input.as_bytes());
            }
            BoundTrigger::Packages => {
                out.push(1);
                let mut received: Vec<PackageId> = self.received.to_vec();
                received.sort_unstable();
                push_count(&mut out, received.len());
                for package in received {
                    out.extend_from_slice(&package.producer().as_u128().to_be_bytes());
                    out.extend_from_slice(&package.output().to_be_bytes());
                }
            }
        }
        out.extend_from_slice(ContentDigest::compute(self.result).as_bytes());
        push_count(&mut out, self.emissions.len());
        for emission in self.emissions {
            match (emission.edge_id(), emission.outbound_type()) {
                (Some(edge_id), _) => {
                    out.push(0);
                    push_bytes(&mut out, edge_id.as_bytes());
                }
                (None, object_type) => {
                    out.push(1);
                    push_bytes(&mut out, object_type.unwrap_or_default().as_bytes());
                }
            }
            match emission.authority() {
                OutputAuthority::Carry => out.push(0),
                OutputAuthority::Transition(authority) => {
                    out.push(1);
                    push_authority(&mut out, authority);
                }
            }
            out.extend_from_slice(ContentDigest::compute(emission.payload()).as_bytes());
        }
        push_count(&mut out, self.contents.len());
        for content in self.contents {
            out.extend_from_slice(content.hash().as_bytes());
            out.push(u8::from(
                content.format() != ontography_content::content::BlobFormat::Raw,
            ));
            out.extend_from_slice(&content.size().to_be_bytes());
        }
        ContentDigest::compute(&out)
    }
}

fn push_count(out: &mut Vec<u8>, count: usize) {
    out.extend_from_slice(&(count as u64).to_be_bytes());
}

fn push_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    push_count(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn push_authority(out: &mut Vec<u8>, authority: &ontography_calculus::Authority) {
    let tags = authority.tags();
    push_count(out, tags.len());
    for tag in tags {
        push_bytes(out, tag.id().as_bytes());
    }
}

fn active(
    inner: &SessionState,
    handle: &InvocationHandle,
) -> Result<super::super::sqlite::context::StoredInvocation, ContextError> {
    if inner.status != SessionStatus::Open
        || !inner.readable
        || handle
            .inner
            .custody
            .as_ref()
            .is_some_and(|c| c.is_revoked())
    {
        return Err(ContextError::Closed);
    }
    let stored = inner.facts.invocation(handle.id())?;
    if stored.status != InvocationStatus::Open {
        return Err(ContextError::Closed);
    }
    Ok(stored)
}
/// The session module's fault rule applied to a context-store or object
/// write: a failure once the write has begun faults the session, and the
/// caller receives the retained fault message as `ContextError::Storage`.
fn write_fault(
    core: &SessionCore,
    inner: &mut SessionState,
    error: impl std::fmt::Display,
) -> ContextError {
    ContextError::Storage(core.fault(inner, Arc::from(error.to_string())).to_string())
}
/// Classifies the outcome of one context-store write by the fault rule.
fn written<T>(
    core: &SessionCore,
    inner: &mut SessionState,
    outcome: Result<T, ContextWriteError>,
) -> Result<T, ContextError> {
    match outcome {
        Ok(value) => Ok(value),
        Err(ContextWriteError::Refused(error)) => Err(error),
        Err(ContextWriteError::Failed(error)) => Err(write_fault(core, inner, error)),
    }
}
fn budget(
    stored: &super::super::sqlite::context::StoredInvocation,
    policy: &ContextPolicy,
    size: u64,
) -> Result<(), ContextError> {
    if size > policy.max_bytes as u64
        || stored.returned_bytes.saturating_add(size) > policy.max_bytes as u64
    {
        return Err(ContextError::Budget("bytes".into()));
    }
    if stored.next_sequence > policy.max_events as u64 {
        return Err(ContextError::Budget("events".into()));
    }
    Ok(())
}
fn retain_event(
    core: &SessionCore,
    inner: &mut SessionState,
    handle: &InvocationHandle,
    operation: &str,
    payload: Payload,
    source: Value,
) -> Result<ContextResponse, ContextError> {
    let sequence = persist_event(
        core,
        inner,
        handle,
        operation,
        &payload,
        &source,
        payload.len() as u64,
    )?;
    let value = serde_json::from_slice(&payload).unwrap_or_else(|_| payload_value(&payload));
    Ok(ContextResponse { sequence, value })
}
fn persist_event(
    core: &SessionCore,
    inner: &mut SessionState,
    handle: &InvocationHandle,
    operation: &str,
    payload: &Payload,
    source: &Value,
    charge: u64,
) -> Result<u64, ContextError> {
    let stored = active(inner, handle)?;
    budget(&stored, handle.policy(), charge)?;
    let encoded_source = serde_json::to_vec(source).map_err(storage)?;
    let source = if encoded_source.len() <= 8192 {
        source.clone()
    } else {
        json!({"metadata_digest":ContentDigest::compute(&encoded_source).to_string(),"metadata_bytes":encoded_source.len(),"truncated":true})
    };
    let digest = ContentDigest::compute(payload);
    // The receipt's bytes and its row are the operation's writes: a failure
    // from here on faults the session.
    if let Err(error) = inner
        .objects
        .put_all(&BTreeMap::from([(digest, payload.clone())]))
    {
        return Err(write_fault(core, inner, error));
    }
    let appended = inner.facts.append_context_event(
        handle.id(),
        handle.policy(),
        PreparedReceipt {
            operation,
            digest,
            bytes: payload.len() as u64,
            source: &source,
        },
        charge,
    );
    written(core, inner, appended)
}
fn payload_value(payload: &[u8]) -> Value {
    match std::str::from_utf8(payload) {
        Ok(text) => json!({"text":text}),
        Err(_) => json!({"bytes":payload}),
    }
}
fn json_payload(value: &Value) -> Result<Payload, ContextError> {
    Ok(Arc::from(serde_json::to_vec(value).map_err(storage)?))
}
fn opaque() -> String {
    uuid::Uuid::new_v4().to_string()
}

impl SessionHandle {
    /// Issues a durable scoped handle without consuming its trigger packages.
    ///
    /// # Errors
    /// Returns an error for an invalid trigger or policy, unavailable source
    /// content, ended custody, or persistence failure.
    pub async fn begin_invocation(
        &self,
        node_id: impl Into<Arc<str>>,
        trigger: InvocationTrigger,
        policy: ContextPolicy,
    ) -> Result<InvocationHandle, ContextError> {
        self.begin_invocation_bound(node_id.into(), trigger, policy, Vec::new(), None)
            .await
    }
    /// Issues a root handle with explicit trusted package dependency declarations.
    ///
    /// # Errors
    /// Returns an error for an invalid root declaration, unavailable
    /// dependencies, invalid policy, or persistence failure.
    pub async fn begin_invocation_with_content(
        &self,
        node_id: impl Into<Arc<str>>,
        trigger: InvocationTrigger,
        policy: ContextPolicy,
        contents: Vec<ContentId>,
    ) -> Result<InvocationHandle, ContextError> {
        self.begin_invocation_bound(node_id.into(), trigger, policy, contents, None)
            .await
    }
    pub(crate) async fn begin_invocation_bound(
        &self,
        node_id: Arc<str>,
        trigger: InvocationTrigger,
        policy: ContextPolicy,
        contents: Vec<ContentId>,
        custody: Option<Arc<SubmissionCustody>>,
    ) -> Result<InvocationHandle, ContextError> {
        let inner = self.core.inner.lock().await;
        if inner.status != SessionStatus::Open
            || !inner.readable
            || custody.as_ref().is_some_and(|c| c.is_revoked())
        {
            return Err(ContextError::Closed);
        }
        if inner.kernel.node_definition(&node_id).is_none() {
            return Err(ContextError::Denied("unknown node".into()));
        }
        if policy.max_packages == 0
            || policy.max_members == 0
            || policy.max_events == 0
            || policy.max_bytes == 0
        {
            return Err(ContextError::Denied(
                "context budgets must be positive".into(),
            ));
        }
        if policy.initial == InitialContext::Ancestry && !policy.ancestor_payloads {
            return Err(ContextError::Denied(
                "ancestry preparation requires ancestor payload grants".into(),
            ));
        }
        let content_store = inner.objects.content_store();
        let package_store =
            PackageStore::new(content_store.clone()).with_limits(self.core.package_limits);
        let mut packages = Vec::new();
        let mut views = GrantedViews::default();
        let mut sources = Vec::new();
        // The root input stays in memory until the invocation row is written;
        // publishing it earlier would leave an unreferenced blob behind every
        // failure or cancellation across the awaits below.
        let mut root_input = None;
        // Root declarations may still have caller-owned temporary retention. Keep
        // them protected across asynchronous resolution until invocation commit.
        let _protected = inner.objects.protect_content(&contents).map_err(storage)?;
        let bound = match trigger {
            InvocationTrigger::Root { authority, input } => {
                let Some(ceiling) = inner.kernel.root_ceiling(&node_id) else {
                    return Err(ContextError::Denied(
                        "node is not an authorized root".into(),
                    ));
                };
                if !authority.is_subset_of(ceiling) {
                    return Err(ContextError::Denied(
                        "root authority exceeds ceiling".into(),
                    ));
                }
                if input.len() > policy.max_bytes {
                    return Err(ContextError::Budget("root input bytes".into()));
                }
                let digest = ContentDigest::compute(&input);
                let input_handle = opaque();
                sources.push((
                    digest,
                    ViewSource {
                        owner: input_handle.clone(),
                        producer: None,
                    },
                    Some(input.clone()),
                ));
                root_input = Some((digest, input));
                BoundTrigger::Root {
                    authority,
                    input: digest,
                    handle: input_handle,
                    dependencies: contents.clone(),
                }
            }
            InvocationTrigger::Packages(ids) => {
                if !contents.is_empty() {
                    return Err(ContextError::Denied(
                        "package invocations derive dependencies from producing activations".into(),
                    ));
                }
                let received: BTreeSet<_> = ids.iter().copied().collect();
                if received.is_empty() || received.len() != ids.len() {
                    return Err(ContextError::Denied(
                        "trigger needs distinct received packages".into(),
                    ));
                }
                for id in &received {
                    if !inner.facts.package_pending_at(*id, &node_id)? {
                        return Err(ContextError::Denied(
                            "trigger package is not pending at this node".into(),
                        ));
                    }
                }
                let include_ancestors = policy.ancestor_metadata || policy.ancestor_payloads;
                let mut seen = BTreeSet::new();
                let mut ordered = Vec::new();
                let mut visiting = BTreeSet::new();
                let mut stack = received
                    .iter()
                    .rev()
                    .map(|id| (*id, false))
                    .collect::<Vec<_>>();
                while let Some((id, done)) = stack.pop() {
                    if done {
                        visiting.remove(&id);
                        ordered.push(id);
                        continue;
                    }
                    if seen.contains(&id) {
                        if visiting.contains(&id) {
                            return Err(ContextError::Storage("package ancestry cycle".into()));
                        }
                        continue;
                    }
                    if seen.len() >= policy.max_packages {
                        return Err(ContextError::Budget("packages".into()));
                    }
                    seen.insert(id);
                    visiting.insert(id);
                    stack.push((id, true));
                    if include_ancestors {
                        let h = inner
                            .facts
                            .package_history(id)
                            .map_err(storage)?
                            .ok_or(ContextError::NotFound)?;
                        for parent in h.inputs().iter().rev() {
                            stack.push((*parent, false));
                        }
                    }
                }
                let handles: BTreeMap<_, _> = ordered.iter().map(|id| (*id, opaque())).collect();
                for id in ordered {
                    let history = inner
                        .facts
                        .package_history(id)
                        .map_err(storage)?
                        .ok_or(ContextError::NotFound)?;
                    let p = history.package();
                    let is_received = received.contains(&id);
                    let payload = is_received || policy.ancestor_payloads;
                    if payload {
                        sources.push((
                            p.content_digest(),
                            ViewSource {
                                owner: handles[&id].clone(),
                                producer: Some(id.producer()),
                            },
                            None,
                        ));
                    }
                    packages.push(PackageGrant {
                        handle: handles[&id].clone(),
                        package_id: id,
                        object_type: p.object_type().to_owned(),
                        content_digest: p.content_digest(),
                        metadata: is_received || policy.ancestor_metadata,
                        payload,
                        received: is_received,
                        parents: history
                            .inputs()
                            .iter()
                            .filter_map(|parent| handles.get(parent).cloned())
                            .collect(),
                    });
                }
                BoundTrigger::Packages
            }
        };
        drop(inner);
        for (digest, source, in_memory) in sources {
            let payload = if let Some(payload) = in_memory {
                payload
            } else {
                let size = content_store
                    .content_size(digest)
                    .await
                    .map_err(storage)?
                    .ok_or(ContextError::NotFound)?;
                if size > policy.max_bytes as u64 {
                    return Err(ContextError::Budget("package envelope bytes".into()));
                }
                Payload::from(
                    content_store
                        .read_digest_range(digest, 0..size)
                        .await
                        .map_err(storage)?
                        .ok_or(ContextError::NotFound)?
                        .as_ref(),
                )
            };
            let declared = if let Some(producer) = source.producer {
                self.core
                    .inner
                    .lock()
                    .await
                    .facts
                    .activation_content(producer)
                    .map_err(storage)?
            } else {
                contents.clone()
            };
            register_composition(
                &package_store,
                &payload,
                source,
                &declared,
                &mut views,
                policy.max_members,
            )
            .await?;
        }
        let mut inner = self.core.inner.lock().await;
        if inner.status != SessionStatus::Open
            || !inner.readable
            || custody.as_ref().is_some_and(|c| c.is_revoked())
        {
            return Err(ContextError::Closed);
        }
        match &bound {
            BoundTrigger::Root { authority, .. } => {
                if !inner
                    .kernel
                    .root_ceiling(&node_id)
                    .is_some_and(|ceiling| authority.is_subset_of(ceiling))
                {
                    return Err(ContextError::Denied(
                        "root authority changed during context preparation".into(),
                    ));
                }
            }
            BoundTrigger::Packages => {
                for package in packages.iter().filter(|package| package.received) {
                    if !inner
                        .facts
                        .package_pending_at(package.package_id, &node_id)?
                    {
                        return Err(ContextError::Denied(
                            "trigger is no longer pending at this node".into(),
                        ));
                    }
                }
            }
        }
        let data = InvocationData {
            id: InvocationId::fresh(),
            node_id: node_id.to_string(),
            owner: custody.as_ref().map(|c| c.owner_id.clone()),
            trigger: bound,
            policy,
            packages,
            views: views.grants,
        };
        // The root input, the dependency retention, and the invocation row are
        // written together under the lock with no await between them; a
        // failure once they begin faults the session.
        if let Some((digest, input)) = root_input
            && let Err(error) = inner.objects.put_all(&BTreeMap::from([(digest, input)]))
        {
            return Err(write_fault(&self.core, &mut inner, error));
        }
        if let Err(error) = inner.objects.retain_content(&contents) {
            return Err(write_fault(&self.core, &mut inner, error));
        }
        let created = inner.facts.create_invocation(&data);
        written(&self.core, &mut inner, created)?;
        Ok(InvocationHandle {
            inner: Arc::new(InvocationLease {
                session: self.invocation_session(),
                data: Arc::new(data),
                custody,
                views: views.resolved,
            }),
        })
    }

    pub(crate) async fn end_invocation(
        &self,
        id: InvocationId,
        state: InvocationStatus,
        reason: &str,
    ) -> Result<(), ContextError> {
        let mut inner = self.core.inner.lock().await;
        let ended = inner.facts.end_invocation(id, state, reason);
        written(&self.core, &mut inner, ended)
    }
    pub(crate) async fn interrupt_invocation_owner(
        &self,
        custody: &SubmissionCustody,
    ) -> Result<(), ContextError> {
        let mut inner = self.core.inner.lock().await;
        let interrupted = inner
            .facts
            .interrupt_invocations(Some(&custody.owner_id), "execution custody ended");
        written(&self.core, &mut inner, interrupted)
    }
    /// Lists durable invocations in insertion order using a previous
    /// invocation ID as cursor.
    ///
    /// # Errors
    /// Returns an error for invalid paging arguments or unreadable persistent state.
    pub async fn invocations_page(
        &self,
        node: Option<&str>,
        after: Option<&str>,
        limit: usize,
    ) -> Result<Vec<InvocationRecord>, ContextError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner).map_err(storage)?;
        inner.facts.invocation_page(node, after, limit)
    }
    /// Reads exact bytes retained for a receipt belonging to this invocation.
    /// This trusted inspection operation does not issue a worker read grant.
    ///
    /// # Errors
    /// Returns an error for invalid ranges, unavailable content, or
    /// unreadable persistent state.
    pub async fn invocation_content(
        &self,
        id: InvocationId,
        receipt_sequence: u64,
        range: Range<u64>,
    ) -> Result<Option<Payload>, ContextError> {
        let digest = {
            let inner = self.core.inner.lock().await;
            require_readable(&inner).map_err(storage)?;
            inner.facts.context_receipt_digest(id, receipt_sequence)?
        };
        let Some(digest) = digest else {
            return Ok(None);
        };
        self.content_range(digest, range).await.map_err(storage)
    }
    /// Lists append-only receipt events independently of the graph revision.
    ///
    /// # Errors
    /// Returns an error for invalid paging arguments or unreadable persistent state.
    pub async fn invocation_events(
        &self,
        id: InvocationId,
        after: u64,
        limit: usize,
    ) -> Result<Vec<ContextEvent>, ContextError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner).map_err(storage)?;
        inner.facts.context_events(id, after, limit)
    }
}
struct ViewSource {
    owner: String,
    producer: Option<ontography_calculus::ActivationId>,
}
/// Views granted as an invocation begins: one grant per composed payload,
/// each package evaluated once even when several sources name it.
#[derive(Default)]
struct GrantedViews {
    grants: Vec<ViewGrant>,
    resolved: BTreeMap<String, ResolvedPackage>,
    entries: usize,
}
async fn register_composition(
    store: &PackageStore,
    payload: &Payload,
    source: ViewSource,
    declared: &[ContentId],
    views: &mut GrantedViews,
    max_members: usize,
) -> Result<(), ContextError> {
    let Some(envelope) = PackageEnvelope::from_payload(payload).map_err(storage)? else {
        return Ok(());
    };
    let root = envelope.ontography_package;
    let declared = dependency_keys(declared);
    if !declared.contains(&dependency_key(root)) {
        return Err(ContextError::Denied(
            "composed package was not declared by its producer".into(),
        ));
    }
    let view = match views.resolved.values().find(|view| view.root() == root) {
        Some(view) => view.clone(),
        None => store.resolve(root).await.map_err(storage)?,
    };
    if view
        .dependencies()
        .iter()
        .any(|id| !declared.contains(&dependency_key(*id)))
    {
        return Err(ContextError::Denied(
            "package dependency was not declared by its producer".into(),
        ));
    }
    views.entries = views.entries.saturating_add(view.entry_count());
    if views.entries > max_members {
        return Err(ContextError::Budget("package members".into()));
    }
    views.grants.push(ViewGrant {
        owner: source.owner.clone(),
        root,
    });
    views.resolved.insert(source.owner, view);
    Ok(())
}
fn resolved_descriptor(owner: &str, view: &ResolvedPackage) -> Value {
    let entries = view
        .entries()
        .iter()
        .map(|entry| member_descriptor(owner, entry))
        .collect::<Vec<_>>();
    json!({"root":owner,"view":entries})
}

type DependencyKey = (
    ontography_content::content::Hash,
    ontography_content::content::BlobFormat,
    u64,
);
fn dependency_key(id: ContentId) -> DependencyKey {
    (id.hash(), id.format(), id.size())
}
fn dependency_keys(ids: &[ContentId]) -> HashSet<DependencyKey> {
    ids.iter().copied().map(dependency_key).collect()
}

fn accepted_retry(
    stored: &super::super::sqlite::context::StoredInvocation,
    commitment: ContentDigest,
) -> Result<Option<ProposalDecision>, ContextError> {
    if stored.status != InvocationStatus::Accepted {
        return Ok(None);
    }
    if stored.submission != Some(commitment) {
        return Err(ContextError::Denied(
            "invocation was already submitted with different output".into(),
        ));
    }
    Ok(Some(ProposalDecision::Committed(
        stored
            .activation
            .ok_or_else(|| ContextError::Storage("accepted invocation has no activation".into()))?,
    )))
}

async fn record_context_denial(
    session: &SessionHandle,
    handle: &InvocationHandle,
    operation: &str,
    args: &Value,
    error: &ContextError,
) -> Result<(), ContextError> {
    let mut inner = session.core.inner.lock().await;
    let stored = match active(&inner, handle) {
        Ok(stored) => stored,
        Err(ContextError::Closed) => return Ok(()),
        Err(error) => return Err(error),
    };
    if stored.next_sequence > handle.policy().max_events as u64 {
        let ended = inner.facts.end_invocation(
            handle.id(),
            InvocationStatus::Failed,
            "context event budget exhausted",
        );
        return written(&session.core, &mut inner, ended);
    }
    let request = serde_json::to_vec(args).map_err(storage)?;
    let request_digest = ContentDigest::compute(&request);
    let operation = operation.chars().take(256).collect::<String>();
    let detail = error.to_string().chars().take(512).collect::<String>();
    let source = json!({"operation":operation,"request_digest":request_digest.to_string(),"request":if request.len()<=4096{args.clone()}else{Value::Null},"error":detail});
    let payload = json_payload(&source)?;
    // A denial exposes no source bytes, but still consumes a bounded event slot.
    persist_event(
        &session.core,
        &mut inner,
        handle,
        "context_denied",
        &payload,
        &source,
        0,
    )?;
    Ok(())
}

impl InvocationHandle {
    /// Retains prepared receipts and returns the host-selected initial payloads.
    ///
    /// # Errors
    /// Returns an error for expired custody, unavailable bytes, or exhausted budgets.
    pub async fn prepare_context(&self) -> Result<Vec<ContextContribution>, ContextError> {
        let session = self.inner.session.upgrade()?;
        let inner = session.core.inner.lock().await;
        let stored = active(&inner, self)?;
        if self.inner.data.policy.initial == InitialContext::None {
            return Ok(Vec::new());
        }
        let sources = match &self.inner.data.trigger {
            BoundTrigger::Root {
                input,
                handle: root,
                ..
            } => vec![(None, *input, root.as_str())],
            BoundTrigger::Packages => self
                .inner
                .data
                .packages
                .iter()
                .filter(|p| p.received || self.policy().initial == InitialContext::Ancestry)
                .map(|p| (Some(p.package_id), p.content_digest, p.handle.as_str()))
                .collect(),
        };
        if stored
            .next_sequence
            .saturating_add(sources.len() as u64)
            .saturating_sub(1)
            > self.policy().max_events as u64
        {
            return Err(ContextError::Budget("events".into()));
        }
        let content_store = inner.objects.content_store();
        drop(inner);
        let mut contributions = Vec::new();
        let mut total = 0u64;
        for (package_id, source_digest, owner) in sources {
            let content = if let Some(view) = self.inner.views.get(owner) {
                match &view.root_entry().kind {
                    ResolvedEntryKind::File { content, .. } => {
                        total = total.saturating_add(content.size());
                        budget(&stored, self.policy(), total)?;
                        Payload::from(
                            content_store
                                .read_range(*content, 0..content.size())
                                .await
                                .map_err(storage)?
                                .as_ref(),
                        )
                    }
                    ResolvedEntryKind::Directory | ResolvedEntryKind::Symlink { .. } => {
                        // Refuse before writing out a view its paths alone would overflow.
                        budget(
                            &stored,
                            self.policy(),
                            total.saturating_add(view.view_bytes()),
                        )?;
                        let value = resolved_descriptor(owner, view);
                        let bytes = json_payload(&value)?;
                        total = total.saturating_add(bytes.len() as u64);
                        budget(&stored, self.policy(), total)?;
                        bytes
                    }
                }
            } else {
                let size = content_store
                    .content_size(source_digest)
                    .await
                    .map_err(storage)?
                    .ok_or(ContextError::NotFound)?;
                total = total.saturating_add(size);
                budget(&stored, self.policy(), total)?;
                Payload::from(
                    content_store
                        .read_digest_range(source_digest, 0..size)
                        .await
                        .map_err(storage)?
                        .ok_or(ContextError::NotFound)?
                        .as_ref(),
                )
            };
            contributions.push((
                ContextContribution {
                    package_id,
                    content_digest: ContentDigest::compute(&content),
                    content,
                },
                source_digest,
            ));
        }
        let mut inner = session.core.inner.lock().await;
        let current = active(&inner, self)?;
        budget(&current, self.policy(), total)?;
        if current
            .next_sequence
            .saturating_add(contributions.len() as u64)
            .saturating_sub(1)
            > self.policy().max_events as u64
        {
            return Err(ContextError::Budget("events".into()));
        }
        for (contribution, source_digest) in &contributions {
            retain_event(
                &session.core,
                &mut inner,
                self,
                "prepare_context",
                contribution.content.clone(),
                json!({"package_id":contribution.package_id.map(package_key),"source_digest":source_digest.to_string(),"projection":"delivered_resolved_view"}),
            )?;
        }
        Ok(contributions
            .into_iter()
            .map(|(contribution, _)| contribution)
            .collect())
    }
    /// Checks a worker-produced delivery and returns its required retention closure.
    ///
    /// Ordinary bytes need no dependencies. A package envelope may name only a
    /// package whose own view is exactly a subtree of a granted view. Retained
    /// historical bases do not authorize republication, and neither does a
    /// directory a save changed: it carries the save's ID, whose own view
    /// would expose files the granted view hides. Host-created outputs use
    /// `submit` directly.
    ///
    /// # Errors
    /// Rejects malformed envelopes, ungranted package identities, expired custody,
    /// or unavailable content.
    pub async fn validate_worker_output(
        &self,
        payload: &Payload,
    ) -> Result<Vec<ContentId>, ContextError> {
        let session = self.inner.session.upgrade()?;
        let validation = async {
            let inner = session.core.inner.lock().await;
            active(&inner, self)?;
            // The worker's own malformed output, refused as `submit` refuses it.
            let Some(envelope) = PackageEnvelope::from_payload(payload)
                .map_err(|error| ContextError::Denied(error.to_string()))?
            else {
                return Ok(Vec::new());
            };
            let id = envelope.ontography_package;
            if !self.inner.views.values().any(|view| view.publishes(id)) {
                return Err(ContextError::Denied(
                    "worker output is outside the granted package view".into(),
                ));
            }
            let store = PackageStore::new(inner.objects.content_store())
                .with_limits(session.core.package_limits);
            drop(inner);
            let dependencies = store.dependencies(id).await.map_err(storage)?;
            active(&*session.core.inner.lock().await, self)?;
            Ok(dependencies)
        }
        .await;
        if let Err(error) = &validation {
            record_context_denial(
                &session,
                self,
                "worker_output",
                &json!({"digest":ContentDigest::compute(payload).to_string()}),
                error,
            )
            .await?;
        }
        validation
    }
    /// Publishes through the bound trigger and atomically links acceptance;
    /// exact accepted retries return the original activation.
    ///
    /// # Errors
    /// Returns an error for ended custody, changed retry output, invalid
    /// content dependencies, a validator panic, or a runtime fault.
    pub async fn submit(
        &self,
        result: Payload,
        emissions: Vec<ontography_calculus::Emission>,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, ContextError> {
        let session = self.inner.session.upgrade()?;
        let mut inner = session.core.inner.lock().await;
        if self.inner.custody.as_ref().is_some_and(|c| c.is_revoked()) {
            return Err(ContextError::Closed);
        }
        let stored = inner.facts.invocation(self.id())?;
        let received = self
            .packages()
            .iter()
            .filter(|p| p.received)
            .map(|p| p.package_id)
            .collect::<Vec<_>>();
        // The context schema version binds this encoding to one runtime format.
        let commitment = SubmissionFacts {
            node_id: self.node_id(),
            trigger: &self.inner.data.trigger,
            received: &received,
            result: &result,
            emissions: &emissions,
            contents: &contents,
        }
        .commitment();
        let mut proposal = match &self.inner.data.trigger {
            BoundTrigger::Root { authority, .. } => {
                ActivationProposal::root(self.node_id(), authority.clone(), result)
            }
            BoundTrigger::Packages => ActivationProposal::join(received, result),
        };
        for emission in emissions {
            proposal.emit(emission);
        }
        if let Some(accepted) = accepted_retry(&stored, commitment)? {
            return Ok(accepted);
        }
        active(&inner, self)?;
        let envelopes = proposal
            .emission_payloads()
            .map(PackageEnvelope::from_payload)
            .collect::<Result<Vec<_>, _>>();
        let envelopes = match envelopes {
            Ok(values) => values.into_iter().flatten().collect::<Vec<_>>(),
            Err(error) => {
                let ended = inner.facts.end_invocation(
                    self.id(),
                    InvocationStatus::Failed,
                    &error.to_string(),
                );
                written(&session.core, &mut inner, ended)?;
                return Err(ContextError::Denied(error.to_string()));
            }
        };
        let _publication_protection = if envelopes.is_empty() {
            Vec::new()
        } else {
            match inner.objects.protect_content(&contents) {
                Ok(protection) => protection,
                Err(error) => {
                    let ended = inner.facts.end_invocation(
                        self.id(),
                        InvocationStatus::Failed,
                        &error.to_string(),
                    );
                    written(&session.core, &mut inner, ended)?;
                    return Err(ContextError::Submit(SessionError::Content(Arc::from(
                        error.to_string(),
                    ))));
                }
            }
        };
        let store = PackageStore::new(inner.objects.content_store())
            .with_limits(session.core.package_limits);
        drop(inner);
        let declared = dependency_keys(&contents);
        for envelope in envelopes {
            let validation = async {
                if !declared.contains(&dependency_key(envelope.ontography_package)) {
                    return Err(ContextError::Denied(
                        "output package must be declared as an activation dependency".into(),
                    ));
                }
                let view = store
                    .resolve(envelope.ontography_package)
                    .await
                    .map_err(storage)?;
                if view
                    .dependencies()
                    .iter()
                    .any(|id| !declared.contains(&dependency_key(*id)))
                {
                    return Err(ContextError::Denied(
                        "output package closure must be declared as activation dependencies".into(),
                    ));
                }
                Ok(())
            }
            .await;
            if let Err(error) = validation {
                let mut inner = session.core.inner.lock().await;
                let ended = inner.facts.end_invocation(
                    self.id(),
                    InvocationStatus::Failed,
                    &error.to_string(),
                );
                written(&session.core, &mut inner, ended)?;
                return Err(error);
            }
        }
        let mut inner = session.core.inner.lock().await;
        if self
            .inner
            .custody
            .as_ref()
            .is_some_and(|custody| custody.is_revoked())
        {
            return Err(ContextError::Closed);
        }
        if let Some(accepted) = accepted_retry(&inner.facts.invocation(self.id())?, commitment)? {
            return Ok(accepted);
        }
        active(&inner, self)?;
        let id = self.id();
        // The same fault ladder as an unlinked submission; the invocation's
        // accepted or rejected status is written inside the transaction.
        let decision = session.core.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            let SessionState { facts, objects, .. } = state;
            facts.submit(&kernel, objects, proposal, &contents, |tx, decision| {
                link_submission(tx, id, commitment, decision)
            })
        });
        match decision {
            Ok(Ok(activation_id)) => Ok(ProposalDecision::Committed(activation_id)),
            Ok(Err(reject)) => Ok(ProposalDecision::Rejected(reject)),
            Err(error @ (SessionError::Content(_) | SessionError::Panicked(_))) => {
                // Nothing was written and the session is open, but this
                // output cannot be published: the invocation ends failed.
                let ended =
                    inner
                        .facts
                        .end_invocation(id, InvocationStatus::Failed, &error.to_string());
                written(&session.core, &mut inner, ended)?;
                Err(ContextError::Submit(error))
            }
            Err(error) => Err(ContextError::Submit(error)),
        }
    }
    /// Runs one enabled context operation using invocation-local opaque handles.
    ///
    /// # Errors
    /// Returns an error for denied operations, invalid handles or ranges,
    /// exhausted budgets, or storage failure.
    pub async fn call(
        &self,
        operation: &str,
        args: Value,
    ) -> Result<ContextResponse, ContextError> {
        let session = self.inner.session.upgrade()?;
        let request = args.clone();
        let result = async {
            let mut inner = session.core.inner.lock().await;
            let stored = active(&inner, self)?;
            if self.inner.data.policy.mode != ContextMode::Explorable {
                return Err(ContextError::Denied(
                    "context tools are disabled in prepared mode".into(),
                ));
            }
            let key = args.get("handle").and_then(Value::as_str);
            match operation {
                "package.describe" => {
                    let value = if let Some((owner, _, member)) =
                        key.and_then(|key| self.find_member(key))
                    {
                        member_descriptor(owner, &member)
                    } else if let BoundTrigger::Root {
                        handle: root,
                        input,
                        ..
                    } = &self.inner.data.trigger
                        && Some(root.as_str()) == key
                    {
                        crate::context::root_input_descriptor(root, *input)
                    } else {
                        let p = self
                            .inner
                            .data
                            .packages
                            .iter()
                            .find(|p| Some(p.handle.as_str()) == key)
                            .ok_or(ContextError::NotFound)?;
                        if !p.metadata {
                            return Err(ContextError::Denied(
                                "package metadata is not granted".into(),
                            ));
                        }
                        crate::context::package_descriptor(p, &self.inner.data.policy)
                    };
                    retain_event(
                        &session.core,
                        &mut inner,
                        self,
                        operation,
                        json_payload(&value)?,
                        args,
                    )
                }
                "package.parents" => {
                    let p = self
                        .inner
                        .data
                        .packages
                        .iter()
                        .find(|p| Some(p.handle.as_str()) == key)
                        .ok_or(ContextError::NotFound)?;
                    if !p.metadata || !self.inner.data.policy.ancestor_metadata {
                        return Err(ContextError::Denied(
                            "causal ancestor metadata is not granted".into(),
                        ));
                    }
                    let value = json!({"parents":p.parents});
                    retain_event(
                        &session.core,
                        &mut inner,
                        self,
                        operation,
                        json_payload(&value)?,
                        args,
                    )
                }
                "package.list" => {
                    let (owner, view, member) = key
                        .and_then(|key| self.find_member(key))
                        .ok_or(ContextError::NotFound)?;
                    let Some(children) = view.children(&member.path) else {
                        return Err(ContextError::Denied("only a collection has members".into()));
                    };
                    let children = children
                        .iter()
                        .map(|child| member_descriptor(owner, child))
                        .collect::<Vec<_>>();
                    let value = json!({"handle":key,"members":children});
                    retain_event(
                        &session.core,
                        &mut inner,
                        self,
                        operation,
                        json_payload(&value)?,
                        args,
                    )
                }
                "package.read" => {
                    let (digest, content, size) = if let Some((_, _, member)) =
                        key.and_then(|key| self.find_member(key))
                    {
                        let ResolvedEntryKind::File { content, .. } = member.kind else {
                            return Err(ContextError::Denied("package.read requires a file; use package.list or package.describe for other members".into()));
                        };
                        (None, Some(content), content.size())
                    } else if let BoundTrigger::Root {
                        handle: root,
                        input,
                        ..
                    } = &self.inner.data.trigger
                        && Some(root.as_str()) == key
                    {
                        (
                            Some(*input),
                            None,
                            inner
                                .objects
                                .content_size(*input)
                                .map_err(storage)?
                                .ok_or(ContextError::NotFound)?,
                        )
                    } else {
                        let p = self
                            .inner
                            .data
                            .packages
                            .iter()
                            .find(|p| Some(p.handle.as_str()) == key)
                            .ok_or(ContextError::NotFound)?;
                        if !p.payload {
                            return Err(ContextError::Denied(
                                "package payload is not granted".into(),
                            ));
                        }
                        (
                            Some(p.content_digest),
                            None,
                            inner
                                .objects
                                .content_size(p.content_digest)
                                .map_err(storage)?
                                .ok_or(ContextError::NotFound)?,
                        )
                    };
                    let start = args
                        .get("start")
                        .map(|v| {
                            v.as_u64().ok_or_else(|| {
                                ContextError::Denied("start must be an unsigned integer".into())
                            })
                        })
                        .transpose()?
                        .unwrap_or(0);
                    let end = args
                        .get("end")
                        .map(|v| {
                            v.as_u64().ok_or_else(|| {
                                ContextError::Denied("end must be an unsigned integer".into())
                            })
                        })
                        .transpose()?
                        .unwrap_or(size);
                    if start > end || end > size {
                        return Err(ContextError::Denied("invalid byte range".into()));
                    }
                    budget(&stored, self.policy(), end - start)?;
                    let content_store = inner.objects.content_store();
                    drop(inner);
                    let bytes = if let Some(digest) = digest {
                        content_store
                            .read_digest_range(digest, start..end)
                            .await
                            .map_err(storage)?
                            .ok_or(ContextError::NotFound)?
                    } else {
                        content_store
                            .read_range(content.ok_or(ContextError::NotFound)?, start..end)
                            .await
                            .map_err(storage)?
                    };
                    let mut inner = session.core.inner.lock().await;
                    active(&inner, self)?;
                    let mut value = payload_value(&bytes);
                    value["start"] = json!(start);
                    value["end"] = json!(end);
                    value["handle"] = json!(key);
                    retain_event(
                        &session.core,
                        &mut inner,
                        self,
                        operation,
                        json_payload(&value)?,
                        args,
                    )
                }
                _ => Err(ContextError::Denied("unknown context operation".into())),
            }
        }
        .await;
        if let Err(error) = &result {
            record_context_denial(&session, self, operation, &request, error).await?;
        }
        result
    }
    /// Records exact host-generated dispatch bytes before transport sends them.
    ///
    /// # Errors
    /// Returns an error if custody ended, the evidence budget is exhausted, or persistence fails.
    pub async fn record_initial_input(
        &self,
        payload: Payload,
    ) -> Result<ContextResponse, ContextError> {
        self.record_context("initial_input", payload, Value::Null)
            .await
    }
    /// Records exact tool-response bytes observed by the trusted host.
    ///
    /// # Errors
    /// Returns an error if custody ended, the evidence budget is exhausted, or persistence fails.
    pub async fn record_tool_response(
        &self,
        tool: &str,
        payload: Payload,
    ) -> Result<ContextResponse, ContextError> {
        self.record_context("tool_response", payload, json!({"tool":tool}))
            .await
    }
    /// Appends transport-send evidence for an existing prepared receipt.
    ///
    /// # Errors
    /// Returns an error for expired custody, an unknown receipt, exhausted
    /// event budget, or storage failure.
    pub async fn mark_sent(&self, sequence: u64) -> Result<(), ContextError> {
        self.advance_receipt(sequence, ReceiptState::Sent).await
    }
    /// Appends acknowledgement evidence after send; it does not attest model use.
    ///
    /// # Errors
    /// Returns an error unless the receipt was sent, or if custody, budget,
    /// or persistence checks fail.
    pub async fn acknowledge(&self, sequence: u64) -> Result<(), ContextError> {
        self.advance_receipt(sequence, ReceiptState::Acknowledged)
            .await
    }
    /// Terminates an unfinished invocation while retaining its evidence.
    ///
    /// # Errors
    /// Returns an error if the owning session ended or the lifecycle update cannot be persisted.
    pub async fn interrupt(&self, reason: &str) -> Result<(), ContextError> {
        self.inner
            .session
            .upgrade()?
            .end_invocation(self.id(), InvocationStatus::Interrupted, reason)
            .await
    }
    /// Records operational failure without discarding prepared or sent evidence.
    ///
    /// # Errors
    /// Returns an error if the owning session ended or the lifecycle update cannot be persisted.
    pub async fn fail(&self, reason: &str) -> Result<(), ContextError> {
        self.inner
            .session
            .upgrade()?
            .end_invocation(self.id(), InvocationStatus::Failed, reason)
            .await
    }
    async fn record_context(
        &self,
        operation: &str,
        payload: Payload,
        source: Value,
    ) -> Result<ContextResponse, ContextError> {
        let session = self.inner.session.upgrade()?;
        let mut inner = session.core.inner.lock().await;
        retain_event(&session.core, &mut inner, self, operation, payload, source)
    }
    async fn advance_receipt(
        &self,
        sequence: u64,
        state: ReceiptState,
    ) -> Result<(), ContextError> {
        let session = self.inner.session.upgrade()?;
        let mut inner = session.core.inner.lock().await;
        active(&inner, self)?;
        let advanced =
            inner
                .facts
                .advance_receipt(self.id(), sequence, state, self.policy().max_events);
        written(&session.core, &mut inner, advanced)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ontography_calculus::{ActivationId, Authority, AuthorityTag};

    fn tag(id: &str) -> AuthorityTag {
        AuthorityTag::new(id).unwrap()
    }

    fn bytes(value: &[u8]) -> Payload {
        Arc::from(value)
    }

    fn content(size: u64) -> ContentId {
        serde_json::from_value(json!({
            "hash": ontography_content::content::Hash::new(b"content").to_string(),
            "format": "Raw",
            "size": size,
        }))
        .unwrap()
    }

    fn root(authority: &[&str], input: &[u8]) -> BoundTrigger {
        BoundTrigger::Root {
            authority: Authority::new(authority.iter().map(|id| tag(id))),
            input: ContentDigest::compute(input),
            handle: "handle".into(),
            dependencies: Vec::new(),
        }
    }

    fn package(producer: u128, output: u128) -> PackageId {
        PackageId::from_parts(ActivationId::from_u128(producer), output)
    }

    /// Two submissions with equal facts commit to one digest; changing any
    /// single fact, including the order of emissions, changes it.
    #[test]
    fn commitment_is_canonical_over_every_submission_fact() {
        let trigger = root(&["route"], b"input");
        let emissions = vec![
            Emission::new("ab", OutputAuthority::Carry, bytes(b"one")),
            Emission::outbound("Item", OutputAuthority::Carry, bytes(b"two")),
        ];
        let contents = vec![content(3)];
        let facts = |trigger: &BoundTrigger,
                     received: &[PackageId],
                     result: &[u8],
                     emissions: &[Emission],
                     contents: &[ContentId]| {
            SubmissionFacts {
                node_id: "a",
                trigger,
                received,
                result: &bytes(result),
                emissions,
                contents,
            }
            .commitment()
        };
        let baseline = facts(&trigger, &[], b"result", &emissions, &contents);
        assert_eq!(
            baseline,
            facts(
                &root(&["route"], b"input"),
                &[],
                b"result",
                &emissions.clone(),
                &contents.clone()
            )
        );
        // The received set is canonical: order does not matter.
        assert_eq!(
            facts(
                &BoundTrigger::Packages,
                &[package(1, 0), package(2, 0)],
                b"result",
                &emissions,
                &contents
            ),
            facts(
                &BoundTrigger::Packages,
                &[package(2, 0), package(1, 0)],
                b"result",
                &emissions,
                &contents
            )
        );

        let swapped = vec![emissions[1].clone(), emissions[0].clone()];
        let variants = [
            SubmissionFacts {
                node_id: "b",
                trigger: &trigger,
                received: &[],
                result: &bytes(b"result"),
                emissions: &emissions,
                contents: &contents,
            }
            .commitment(),
            facts(
                &root(&["other"], b"input"),
                &[],
                b"result",
                &emissions,
                &contents,
            ),
            facts(
                &root(&["route"], b"other"),
                &[],
                b"result",
                &emissions,
                &contents,
            ),
            facts(
                &BoundTrigger::Packages,
                &[package(1, 0)],
                b"result",
                &emissions,
                &contents,
            ),
            facts(
                &BoundTrigger::Packages,
                &[package(1, 1)],
                b"result",
                &emissions,
                &contents,
            ),
            facts(&trigger, &[], b"other", &emissions, &contents),
            facts(&trigger, &[], b"result", &emissions[..1], &contents),
            facts(&trigger, &[], b"result", &swapped, &contents),
            facts(
                &trigger,
                &[],
                b"result",
                &[
                    Emission::new("ac", OutputAuthority::Carry, bytes(b"one")),
                    emissions[1].clone(),
                ],
                &contents,
            ),
            facts(
                &trigger,
                &[],
                b"result",
                &[
                    Emission::outbound("ab", OutputAuthority::Carry, bytes(b"one")),
                    emissions[1].clone(),
                ],
                &contents,
            ),
            facts(
                &trigger,
                &[],
                b"result",
                &[
                    emissions[0].clone(),
                    Emission::outbound("Other", OutputAuthority::Carry, bytes(b"two")),
                ],
                &contents,
            ),
            facts(
                &trigger,
                &[],
                b"result",
                &[
                    Emission::new(
                        "ab",
                        OutputAuthority::Transition(Authority::new([tag("route")])),
                        bytes(b"one"),
                    ),
                    emissions[1].clone(),
                ],
                &contents,
            ),
            facts(
                &trigger,
                &[],
                b"result",
                &[
                    Emission::new("ab", OutputAuthority::Carry, bytes(b"changed")),
                    emissions[1].clone(),
                ],
                &contents,
            ),
            facts(&trigger, &[], b"result", &emissions, &[]),
            facts(&trigger, &[], b"result", &emissions, &[content(4)]),
            facts(
                &trigger,
                &[],
                b"result",
                &emissions,
                &[content(3), content(3)],
            ),
        ];
        let distinct: HashSet<ContentDigest> = variants.iter().copied().chain([baseline]).collect();
        assert_eq!(distinct.len(), variants.len() + 1);
    }
}
