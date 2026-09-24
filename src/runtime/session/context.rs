//! Scoped host invocations. Package acceptance continues to belong to the kernel.
use super::super::sqlite::context::PreparedReceipt;
use super::{
    ActivationProposal, Arc, AssertUnwindSafe, ContentDigest, ContentId, Payload, ProposalDecision,
    Range, SessionHandle, SessionState, SessionStatus, SubmissionCustody, SubmitError,
    catch_unwind, panic_message, publish_revision, require_readable,
};
use crate::context::{
    BoundTrigger, InvocationData, InvocationLease, member_descriptor, package_key, storage,
};
use crate::context::{
    ContextContribution, ContextError, ContextEvent, ContextMode, ContextPolicy, ContextResponse,
    InitialContext, InvocationHandle, InvocationId, InvocationRecord, InvocationStatus,
    InvocationTrigger, PackageGrant, PackageMemberGrant, ReceiptState,
};
use crate::package::{PackageEnvelope, PackageStore, ResolvedEntryKind, ResolvedPackage};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet, HashSet};

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
    inner: &mut SessionState,
    handle: &InvocationHandle,
    operation: &str,
    payload: Payload,
    source: Value,
) -> Result<ContextResponse, ContextError> {
    let sequence = persist_event(
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
    inner
        .objects
        .put_all(&BTreeMap::from([(digest, payload.clone())]))
        .map_err(storage)?;
    inner.facts.append_context_event(
        handle.id(),
        handle.policy(),
        PreparedReceipt {
            operation,
            digest,
            bytes: payload.len() as u64,
            source: &source,
        },
        charge,
    )
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
    /// Returns an error for an invalid trigger or policy, unavailable source content, ended custody, or persistence failure.
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
    /// Returns an error for an invalid root declaration, unavailable dependencies, invalid policy, or persistence failure.
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
        let mut inner = self.core.inner.lock().await;
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
        if policy
            .workspace
            .as_ref()
            .is_some_and(|w| w.writable && w.output_edge.is_none())
        {
            return Err(ContextError::Denied(
                "writable workspace requires output_edge".into(),
            ));
        }
        let content_store = inner.objects.content_store();
        let package_store = PackageStore::new(content_store.clone());
        let mut packages = Vec::new();
        let mut members = Vec::new();
        let mut sources = Vec::new();
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
                ));
                inner
                    .objects
                    .put_all(&BTreeMap::from([(digest, input)]))
                    .map_err(storage)?;
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
        for (digest, source) in sources {
            let size = content_store
                .content_size(digest)
                .await
                .map_err(storage)?
                .ok_or(ContextError::NotFound)?;
            if size > policy.max_bytes as u64 {
                return Err(ContextError::Budget("package envelope bytes".into()));
            }
            let payload = Payload::from(
                content_store
                    .read_digest_range(digest, 0..size)
                    .await
                    .map_err(storage)?
                    .ok_or(ContextError::NotFound)?
                    .as_ref(),
            );
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
                &mut members,
                policy.max_members,
            )
            .await?;
        }
        let inner = self.core.inner.lock().await;
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
            members,
        };
        if data.policy.workspace.is_some() {
            workspace_root(&inner.facts, &data)?;
        }
        inner.objects.retain_content(&contents).map_err(storage)?;
        inner.facts.create_invocation(&data)?;
        Ok(InvocationHandle {
            inner: Arc::new(InvocationLease {
                session: self.invocation_session(),
                data: Arc::new(data),
                custody,
            }),
        })
    }

    pub(crate) async fn end_invocation(
        &self,
        id: InvocationId,
        state: InvocationStatus,
        reason: &str,
    ) -> Result<(), ContextError> {
        let inner = self.core.inner.lock().await;
        inner.facts.end_invocation(id, state, reason)
    }
    pub(crate) async fn interrupt_invocation_owner(
        &self,
        custody: &SubmissionCustody,
    ) -> Result<(), ContextError> {
        let inner = self.core.inner.lock().await;
        inner
            .facts
            .interrupt_invocations(Some(&custody.owner_id), "execution custody ended")
    }
    /// Lists durable invocations in insertion order using a previous invocation ID as cursor.
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
    /// Returns an error for invalid ranges, unavailable content, or unreadable persistent state.
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
    producer: Option<crate::ActivationId>,
}
async fn register_composition(
    store: &PackageStore,
    payload: &Payload,
    source: ViewSource,
    declared: &[ContentId],
    members: &mut Vec<PackageMemberGrant>,
    max_members: usize,
) -> Result<(), ContextError> {
    let Some(envelope) = PackageEnvelope::from_payload(payload).map_err(storage)? else {
        return Ok(());
    };
    let declared = dependency_keys(declared);
    if !declared.contains(&dependency_key(envelope.ontography_package)) {
        return Err(ContextError::Denied(
            "composed package was not declared by its producer".into(),
        ));
    }
    let view = store
        .resolve(envelope.ontography_package)
        .await
        .map_err(storage)?;
    let closure = view.dependencies();
    if closure
        .iter()
        .any(|id| !declared.contains(&dependency_key(*id)))
    {
        return Err(ContextError::Denied(
            "package dependency was not declared by its producer".into(),
        ));
    }
    if members.len().saturating_add(view.entries().len()) > max_members {
        return Err(ContextError::Budget("package members".into()));
    }
    for entry in view.entries() {
        members.push(PackageMemberGrant {
            handle: if entry.path.is_empty() {
                source.owner.clone()
            } else {
                opaque()
            },
            owner: source.owner.clone(),
            path: entry.path.clone(),
            package: entry.package,
            kind: entry.kind.clone(),
        });
    }
    Ok(())
}
fn workspace_root<'a>(
    facts: &super::super::sqlite::SqliteSession,
    data: &'a InvocationData,
) -> Result<&'a PackageMemberGrant, ContextError> {
    let policy = data
        .policy
        .workspace
        .as_ref()
        .ok_or_else(|| ContextError::Denied("workspace is not configured".into()))?;
    let mut selected = None;
    for root in data
        .members
        .iter()
        .filter(|m| m.path.is_empty() && matches!(m.kind, ResolvedEntryKind::Directory))
    {
        let package = data
            .packages
            .iter()
            .find(|p| p.handle == root.handle && p.received);
        if package.is_none()
            && !matches!(&data.trigger, BoundTrigger::Root { handle, .. } if handle == &root.handle)
        {
            continue;
        }
        if let Some(edge) = &policy.input_edge {
            let Some(package) = package else {
                continue;
            };
            let history = facts
                .package_history(package.package_id)
                .map_err(storage)?
                .ok_or(ContextError::NotFound)?;
            if history.package().edge_id() != Some(edge.as_str()) {
                continue;
            }
        }
        if selected.replace(root).is_some() {
            return Err(ContextError::Denied(
                "workspace selection needs exactly one delivered collection".into(),
            ));
        }
    }
    selected.ok_or_else(|| {
        ContextError::Denied("workspace selection has no delivered collection".into())
    })
}

fn immediate_child(parent: &str, path: &str) -> bool {
    if path.is_empty() {
        return false;
    }
    path.rsplit_once('/')
        .map_or(parent.is_empty(), |(prefix, _)| prefix == parent)
}
fn resolved_descriptor(data: &InvocationData, owner: &str) -> Value {
    let entries = data
        .members
        .iter()
        .filter(|member| member.owner == owner)
        .map(member_descriptor)
        .collect::<Vec<_>>();
    json!({"root":owner,"view":entries})
}

type DependencyKey = (crate::content::Hash, crate::content::BlobFormat, u64);
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
        inner.facts.end_invocation(
            handle.id(),
            InvocationStatus::Failed,
            "context event budget exhausted",
        )?;
        return Ok(());
    }
    let request = serde_json::to_vec(args).map_err(storage)?;
    let request_digest = ContentDigest::compute(&request);
    let operation = operation.chars().take(256).collect::<String>();
    let detail = error.to_string().chars().take(512).collect::<String>();
    let source = json!({"operation":operation,"request_digest":request_digest.to_string(),"request":if request.len()<=4096{args.clone()}else{Value::Null},"error":detail});
    let payload = json_payload(&source)?;
    // A denial exposes no source bytes, but still consumes a bounded event slot.
    persist_event(&mut inner, handle, "context_denied", &payload, &source, 0)?;
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
            let content = if let Some(root) = self.inner.data.root_member(owner) {
                match &root.kind {
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
                        let value = resolved_descriptor(&self.inner.data, owner);
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
    /// Selects the configured delivered collection and resolves its trusted workspace view.
    ///
    /// # Errors
    /// Returns an error for expired custody, an ambiguous or missing collection, or unavailable dependencies.
    pub async fn workspace_package(&self) -> Result<(String, ResolvedPackage), ContextError> {
        let session = self.inner.session.upgrade()?;
        let inner = session.core.inner.lock().await;
        active(&inner, self)?;
        let root = workspace_root(&inner.facts, &self.inner.data)?;
        let store = PackageStore::new(inner.objects.content_store());
        drop(inner);
        let view = store.resolve(root.package).await.map_err(storage)?;
        active(&*session.core.inner.lock().await, self)?;
        Ok((root.handle.clone(), view))
    }
    /// Records exposure of the configured, granted collection view.
    ///
    /// # Errors
    /// Returns an error for ungranted package roots, expired custody, exhausted budgets, or persistence failure.
    pub async fn record_workspace_exposure(
        &self,
        content: ContentId,
    ) -> Result<ContextResponse, ContextError> {
        let session = self.inner.session.upgrade()?;
        let mut inner = session.core.inner.lock().await;
        active(&inner, self)?;
        let root = workspace_root(&inner.facts, &self.inner.data)?;
        if root.package != content {
            return Err(ContextError::Denied(
                "workspace package is not selected".into(),
            ));
        }
        let value = json!({"package":content,"handle":root.handle,"writable":self.inner.data.policy.workspace.as_ref().is_some_and(|w|w.writable),"boundary":"host_checkout_prepared","filesystem_reads_traced":false});
        retain_event(
            &mut inner,
            self,
            "workspace_exposure",
            json_payload(&value)?,
            value,
        )
    }
    /// Checks a worker-produced delivery and returns its required retention closure.
    ///
    /// Ordinary bytes need no dependencies. Package envelopes may name only a
    /// package in this invocation's resolved view; retained historical bases do
    /// not authorize republication. Host-created outputs use `submit` directly.
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
            let Some(envelope) = PackageEnvelope::from_payload(payload).map_err(storage)? else {
                return Ok(Vec::new());
            };
            if !self
                .members()
                .iter()
                .any(|m| m.package == envelope.ontography_package)
            {
                return Err(ContextError::Denied(
                    "worker output is outside the granted package view".into(),
                ));
            }
            let store = PackageStore::new(inner.objects.content_store());
            drop(inner);
            let view = store
                .resolve(envelope.ontography_package)
                .await
                .map_err(storage)?;
            active(&*session.core.inner.lock().await, self)?;
            Ok(view.dependencies())
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
    /// Publishes through the bound trigger and atomically links acceptance; exact accepted retries return the original activation.
    ///
    /// # Errors
    /// Returns an error for ended custody, changed retry output, invalid content dependencies, or a runtime fault.
    pub async fn submit(
        &self,
        result: Payload,
        emissions: Vec<crate::Emission>,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, ContextError> {
        let session = self.inner.session.upgrade()?;
        let inner = session.core.inner.lock().await;
        if self.inner.custody.as_ref().is_some_and(|c| c.is_revoked()) {
            return Err(ContextError::Closed);
        }
        let stored = inner.facts.invocation(self.id())?;
        let mut proposal = match &self.inner.data.trigger {
            BoundTrigger::Root { authority, .. } => {
                ActivationProposal::root(self.node_id(), authority.clone(), result)
            }
            BoundTrigger::Packages => ActivationProposal::join(
                self.packages()
                    .iter()
                    .filter(|p| p.received)
                    .map(|p| p.package_id),
                result,
            ),
        };
        for emission in emissions {
            proposal.emit(emission);
        }
        // The schema version binds this identity encoding to one runtime format.
        let commitment = ContentDigest::compute(format!("{proposal:?}\n{contents:?}").as_bytes());
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
                inner.facts.end_invocation(
                    self.id(),
                    InvocationStatus::Failed,
                    &error.to_string(),
                )?;
                return Err(ContextError::Denied(error.to_string()));
            }
        };
        let _publication_protection = if envelopes.is_empty() {
            Vec::new()
        } else {
            match inner.objects.protect_content(&contents) {
                Ok(protection) => protection,
                Err(error) => {
                    inner.facts.end_invocation(
                        self.id(),
                        InvocationStatus::Failed,
                        &error.to_string(),
                    )?;
                    return Err(ContextError::Submit(SubmitError::Content(Arc::from(
                        error.to_string(),
                    ))));
                }
            }
        };
        let store = PackageStore::new(inner.objects.content_store());
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
                let inner = session.core.inner.lock().await;
                inner.facts.end_invocation(
                    self.id(),
                    InvocationStatus::Failed,
                    &error.to_string(),
                )?;
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
        let evaluation = catch_unwind(AssertUnwindSafe(|| {
            let kernel = Arc::clone(&inner.kernel);
            let SessionState { facts, objects, .. } = &mut *inner;
            facts.submit_with_invocation(
                &kernel,
                objects,
                proposal,
                &contents,
                self.id(),
                commitment,
            )
        }));
        match evaluation {
            Ok(Ok(Ok(commit))) => {
                publish_revision(&mut inner, &session.core.frontier, commit.revision);
                Ok(ProposalDecision::Committed(commit.activation_id))
            }
            Ok(Ok(Err(reject))) => Ok(ProposalDecision::Rejected(reject)),
            Ok(Err(super::super::sqlite::SqliteStateError::Content(error))) => {
                inner.facts.end_invocation(
                    self.id(),
                    InvocationStatus::Failed,
                    &error.to_string(),
                )?;
                Err(ContextError::Submit(SubmitError::Content(Arc::from(
                    error.to_string(),
                ))))
            }
            Ok(Err(error)) => Err(ContextError::Submit(SubmitError::Faulted(
                session.core.fault(&mut inner, Arc::from(error.to_string())),
            ))),
            Err(panic) => Err(ContextError::Submit(SubmitError::Faulted(
                session.core.fault(&mut inner, panic_message(panic)),
            ))),
        }
    }
    /// Runs one enabled context operation using invocation-local opaque handles.
    ///
    /// # Errors
    /// Returns an error for denied operations, invalid handles or ranges, exhausted budgets, or storage failure.
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
                    let value = if let Some(member) = self
                        .inner
                        .data
                        .members
                        .iter()
                        .find(|m| Some(m.handle.as_str()) == key)
                    {
                        member_descriptor(member)
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
                    retain_event(&mut inner, self, operation, json_payload(&value)?, args)
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
                    retain_event(&mut inner, self, operation, json_payload(&value)?, args)
                }
                "package.list" => {
                    let member = self
                        .inner
                        .data
                        .members
                        .iter()
                        .find(|m| Some(m.handle.as_str()) == key)
                        .ok_or(ContextError::NotFound)?;
                    if !matches!(member.kind, ResolvedEntryKind::Directory) {
                        return Err(ContextError::Denied("only a collection has members".into()));
                    }
                    let children = self
                        .inner
                        .data
                        .members
                        .iter()
                        .filter(|candidate| {
                            candidate.owner == member.owner
                                && immediate_child(&member.path, &candidate.path)
                        })
                        .map(member_descriptor)
                        .collect::<Vec<_>>();
                    let value = json!({"handle":member.handle,"members":children});
                    retain_event(&mut inner, self, operation, json_payload(&value)?, args)
                }
                "package.read" => {
                    let (digest, content, size) = if let Some(member) = self
                        .inner
                        .data
                        .members
                        .iter()
                        .find(|m| Some(m.handle.as_str()) == key)
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
                    retain_event(&mut inner, self, operation, json_payload(&value)?, args)
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
    /// Returns an error for expired custody, an unknown receipt, exhausted event budget, or storage failure.
    pub async fn mark_sent(&self, sequence: u64) -> Result<(), ContextError> {
        self.advance_receipt(sequence, ReceiptState::Sent).await
    }
    /// Appends acknowledgement evidence after send; it does not attest model use.
    ///
    /// # Errors
    /// Returns an error unless the receipt was sent, or if custody, budget, or persistence checks fail.
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
        retain_event(&mut inner, self, operation, payload, source)
    }
    async fn advance_receipt(
        &self,
        sequence: u64,
        state: ReceiptState,
    ) -> Result<(), ContextError> {
        let session = self.inner.session.upgrade()?;
        let mut inner = session.core.inner.lock().await;
        active(&inner, self)?;
        inner
            .facts
            .advance_receipt(self.id(), sequence, state, self.policy().max_events)
    }
}
