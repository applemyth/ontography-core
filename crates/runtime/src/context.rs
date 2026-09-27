//! Host-issued, invocation-scoped package access and durable exposure evidence.
//!
//! Grants govern this interface. They do not sandbox a native executable or its
//! terminal, filesystem, network, or other host-provided capabilities.

use ontography_calculus::{ActivationId, Authority, ContentDigest, PackageId, Payload};
use ontography_content::ContentId;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(default, deny_unknown_fields)]
/// Host-selected access and cumulative per-invocation resource limits.
pub struct ContextPolicy {
    /// Whether optional context tools are available.
    pub mode: ContextMode,
    /// Payloads to prepare before worker dispatch.
    pub initial: InitialContext,
    /// Allow describing ancestors and enumerating immediate parent handles.
    pub ancestor_metadata: bool,
    /// Grant payload reads for the full causal ancestry.
    pub ancestor_payloads: bool,
    /// Maximum number of received and ancestor package grants.
    pub max_packages: usize,
    /// Maximum number of visible composed-package members registered for this invocation.
    pub max_members: usize,
    /// Cumulative source and recorded response bytes; bounded denial metadata is separate.
    pub max_bytes: usize,
    /// Maximum receipt rows, including delivery transitions and denials.
    pub max_events: usize,
}
impl Default for ContextPolicy {
    fn default() -> Self {
        Self {
            mode: ContextMode::Prepared,
            initial: InitialContext::Received,
            ancestor_metadata: false,
            ancestor_payloads: false,
            max_packages: 256,
            max_members: 100_000,
            max_bytes: 8 * 1024 * 1024,
            max_events: 4096,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
/// Whether the worker receives optional interactive context tools.
pub enum ContextMode {
    #[default]
    /// Prepare initial context; do not expose interactive context tools.
    Prepared,
    /// Expose the bounded package tools.
    Explorable,
}
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
/// Which granted package payloads the host initially prepares.
pub enum InitialContext {
    /// Prepare no package or root input payloads.
    None,
    #[default]
    /// Prepare received packages, or the explicit root input.
    Received,
    /// Prepare all granted causal ancestor payloads in dependency order.
    Ancestry,
}
#[derive(Clone, Debug)]
/// The exact root request or received packages to which publication is bound.
pub enum InvocationTrigger {
    /// Root activation request and its exact initial input.
    Root {
        /// Requested root authority bounded by the node ceiling.
        authority: Authority,
        /// Exact host-provided root input bytes.
        input: Payload,
    },
    /// Received package occurrences pending at the bound node.
    Packages(Vec<PackageId>),
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
/// Durable invocation identity, encoded as a UUID string in JSON.
pub struct InvocationId(pub(crate) uuid::Uuid);
impl InvocationId {
    pub(crate) fn fresh() -> Self {
        Self(uuid::Uuid::new_v4())
    }
}
impl fmt::Display for InvocationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
/// A host-issued package capability and its available operations.
pub struct PackageGrant {
    /// Opaque handle scoped to this invocation, never a caller-selected content hash.
    pub handle: String,
    #[serde(with = "package_id_serde")]
    /// Canonical package identity represented by the capability.
    pub package_id: PackageId,
    /// The package’s declared object type.
    pub object_type: String,
    #[serde(with = "digest_serde")]
    /// Integrity commitment to the exact referenced bytes.
    pub content_digest: ContentDigest,
    /// Whether package description operations are permitted.
    pub metadata: bool,
    /// Whether payload reads are permitted.
    pub payload: bool,
    /// Whether this package belongs to the bound received trigger.
    pub received: bool,
    /// Immediate causal parent handles within the issued grant set.
    pub parents: Vec<String>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
/// A capability for one member of a frozen, resolved package view.
pub struct PackageMemberGrant {
    /// Opaque invocation-local handle. Directory handles bind to this exact view and path.
    pub handle: String,
    /// Root capability owning this resolved view.
    pub owner: String,
    /// Canonical path inside the view; the root uses the empty path.
    pub path: String,
    /// Content identity for trusted host inspection, never a worker-selected lookup key.
    pub package: ContentId,
    /// Current filesystem interpretation, including the exact visible file commitment.
    pub kind: ontography_content::package::ResolvedEntryKind,
}

#[derive(Clone, Debug)]
/// One exact payload selected for initial host preparation.
pub struct ContextContribution {
    /// Source package, or none for a root input.
    pub package_id: Option<PackageId>,
    /// Integrity commitment to the exact referenced bytes.
    pub content_digest: ContentDigest,
    /// Exact bytes retained and supplied by the host.
    pub content: Payload,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
/// An operation response paired with its durable prepared receipt.
pub struct ContextResponse {
    /// Monotone event sequence, independent of the graph revision.
    pub sequence: u64,
    /// Response body associated with the prepared receipt.
    pub value: Value,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
/// Operational lifecycle, independent of canonical graph activations.
pub enum InvocationStatus {
    /// The invocation may prepare, expose, or publish.
    Open,
    /// A canonical activation was committed and linked atomically.
    Accepted,
    /// The kernel rejected publication; evidence remains retained.
    Rejected,
    /// Custody ended, the session closed, or restart found unfinished work.
    Interrupted,
    /// The host recorded an operational failure.
    Failed,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
/// Host-observed delivery progress; acknowledgement does not prove model influence.
pub enum ReceiptState {
    /// Exact bytes were persisted before any transport-send claim.
    Prepared,
    /// The host observed its transport-send boundary.
    Sent,
    /// The host observed the corresponding worker acknowledgement.
    Acknowledged,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
/// An immutable receipt event with an invocation-local monotone sequence.
pub struct ContextEvent {
    /// Invocation owning this event.
    pub invocation_id: InvocationId,
    /// Monotone event sequence, independent of the graph revision.
    pub sequence: u64,
    /// Sequence of the original prepared event for this delivery.
    pub receipt_sequence: u64,
    /// Prepared, sent, or acknowledged delivery evidence.
    pub state: ReceiptState,
    /// Operation that produced this receipt.
    pub operation: String,
    #[serde(with = "digest_serde")]
    /// Integrity commitment to the exact referenced bytes.
    pub content_digest: ContentDigest,
    /// Exact retained receipt body length, including bounded denial audit metadata.
    pub bytes: u64,
    /// Bounded host metadata identifying the operation and its source.
    pub source: Value,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
/// A trusted inspection view of persisted grants, lifecycle, and submission linkage.
pub struct InvocationRecord {
    /// Durable invocation identity.
    pub id: InvocationId,
    /// Graph node to which this invocation was bound.
    pub node_id: String,
    /// Current operational lifecycle.
    pub status: InvocationStatus,
    /// Host policy frozen when the invocation began.
    pub policy: ContextPolicy,
    /// Package capabilities issued to this invocation.
    pub packages: Vec<PackageGrant>,
    /// Capabilities for members visible in the resolved delivered package views.
    pub members: Vec<PackageMemberGrant>,
    /// Accepted activation identity, encoded as hexadecimal when committed.
    pub activation_id: Option<String>,
    /// Reason for rejection, interruption, or failure.
    pub detail: Option<String>,
    /// Cumulative bytes charged to the invocation’s response budget.
    pub returned_bytes: u64,
}
#[derive(Debug, thiserror::Error)]
/// Failure to issue, use, record, or publish a scoped invocation.
pub enum ContextError {
    #[error("context access denied: {0}")]
    /// Policy or a handle disallows this operation.
    Denied(String),
    #[error("context budget exceeded: {0}")]
    /// A configured cumulative limit would be exceeded.
    Budget(String),
    #[error("invocation is no longer active")]
    /// The invocation, custody, or session is no longer active.
    Closed,
    #[error("unknown invocation or handle")]
    /// The invocation or capability handle does not exist.
    NotFound,
    #[error("context storage failed: {0}")]
    /// Persistent metadata or content could not be read or written.
    ///
    /// A failure once a context-store or object write had begun also faults
    /// the owning session, which then reports `SessionError::Faulted` from
    /// every operation; the payload is the retained fault message. See the
    /// session module's classification rule.
    Storage(String),
    #[error(transparent)]
    /// Publication failed before obtaining a kernel decision.
    ///
    /// Reachable variants: `Faulted`, `Panicked`, and `Content`. Revoked
    /// custody and a closed or faulted session are reported as [`Self::Closed`]
    /// before publication is attempted.
    Submit(#[from] crate::SessionError),
}
pub(crate) fn storage(error: impl fmt::Display) -> ContextError {
    ContextError::Storage(error.to_string())
}

#[derive(Clone)]
/// A cloneable host-issued capability bound to one invocation and session lifetime.
pub struct InvocationHandle {
    pub(crate) inner: Arc<InvocationLease>,
}
pub(crate) struct InvocationLease {
    pub session: crate::session::InvocationSession,
    pub data: Arc<InvocationData>,
    pub custody: Option<Arc<crate::session::SubmissionCustody>>,
}
impl fmt::Debug for InvocationHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InvocationHandle")
            .field("id", &self.id())
            .field("node_id", &self.node_id())
            .finish_non_exhaustive()
    }
}
impl Drop for InvocationLease {
    fn drop(&mut self) {
        if let Ok(runtime) = tokio::runtime::Handle::try_current() {
            let session = self.session.clone();
            let id = self.data.id;
            runtime.spawn(async move {
                let Ok(session) = session.upgrade() else {
                    return;
                };
                let _ = session
                    .end_invocation(
                        id,
                        InvocationStatus::Interrupted,
                        "last invocation handle dropped",
                    )
                    .await;
            });
        }
    }
}
impl InvocationHandle {
    /// Returns the durable invocation identity.
    #[must_use]
    pub fn id(&self) -> InvocationId {
        self.inner.data.id
    }
    /// Returns the node to which this capability is bound.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.inner.data.node_id
    }
    /// Returns the frozen host policy.
    #[must_use]
    pub fn policy(&self) -> &ContextPolicy {
        &self.inner.data.policy
    }
    /// Returns the issued capability catalog, including identities and permission flags.
    #[must_use]
    pub fn packages(&self) -> &[PackageGrant] {
        &self.inner.data.packages
    }
    /// Returns process-visible capabilities with metadata and parent relations redacted by policy.
    #[must_use]
    pub fn tool_descriptors(&self) -> Value {
        let mut packages = self
            .inner
            .data
            .packages
            .iter()
            .map(|p| package_descriptor(p, self.policy()))
            .collect::<Vec<_>>();
        if let BoundTrigger::Root {
            handle,
            input: digest,
            ..
        } = &self.inner.data.trigger
            && self.inner.data.root_member(handle).is_none()
        {
            packages.push(root_input_descriptor(handle, *digest));
        }
        serde_json::json!({"packages":packages,"members":self.inner.data.members.iter().map(member_descriptor).collect::<Vec<_>>()})
    }
    /// Returns the trusted catalog of resolved-view members without exposing a raw store.
    #[must_use]
    pub fn members(&self) -> &[PackageMemberGrant] {
        &self.inner.data.members
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) enum BoundTrigger {
    /// Root activation request and its exact initial input.
    Root {
        authority: Authority,
        #[serde(with = "digest_serde")]
        input: ContentDigest,
        handle: String,
        dependencies: Vec<ContentId>,
    },
    Packages,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct InvocationData {
    /// Durable invocation identity.
    pub id: InvocationId,
    /// Graph node to which this invocation was bound.
    pub node_id: String,
    pub owner: Option<String>,
    pub trigger: BoundTrigger,
    /// Host policy frozen when the invocation began.
    pub policy: ContextPolicy,
    /// Package capabilities issued to this invocation.
    pub packages: Vec<PackageGrant>,
    /// Capabilities for members visible in the resolved delivered package views.
    pub members: Vec<PackageMemberGrant>,
}
impl InvocationData {
    pub fn root_member(&self, handle: &str) -> Option<&PackageMemberGrant> {
        self.members
            .iter()
            .find(|member| member.handle == handle && member.path.is_empty())
    }
}
pub(crate) fn package_key(id: PackageId) -> String {
    format!("{:032x}:{:032x}", id.producer().as_u128(), id.output())
}
pub(crate) fn parse_package(key: &str) -> Result<PackageId, ContextError> {
    let (a, b) = key.split_once(':').ok_or(ContextError::NotFound)?;
    Ok(PackageId::from_parts(
        ActivationId::from_u128(u128::from_str_radix(a, 16).map_err(storage)?),
        u128::from_str_radix(b, 16).map_err(storage)?,
    ))
}
mod package_id_serde {
    use super::{Deserialize, PackageId, package_key, parse_package};
    pub fn serialize<S: serde::Serializer>(id: &PackageId, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&package_key(*id))
    }
    pub fn deserialize<'de, D: serde::Deserializer<'de>>(d: D) -> Result<PackageId, D::Error> {
        parse_package(&String::deserialize(d)?).map_err(serde::de::Error::custom)
    }
}
pub(crate) mod digest_serde {
    use super::{ContentDigest, Deserialize, Serialize};
    pub fn serialize<S: serde::Serializer>(id: &ContentDigest, s: S) -> Result<S::Ok, S::Error> {
        id.as_bytes().serialize(s)
    }
    pub fn deserialize<'de, D: serde::Deserializer<'de>>(d: D) -> Result<ContentDigest, D::Error> {
        Ok(ContentDigest::from_bytes(<[u8; 32]>::deserialize(d)?))
    }
}

impl std::str::FromStr for InvocationId {
    type Err = ContextError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        uuid::Uuid::parse_str(s).map(Self).map_err(storage)
    }
}
/// Reads paginated invocation metadata from a suspended session directory without opening its blob store.
///
/// # Errors
/// Returns an error for an invalid page limit, unsupported schema, locked owner, or unreadable session.
pub fn read_invocations(
    path: impl AsRef<std::path::Path>,
    node: Option<&str>,
    after: Option<&str>,
    limit: usize,
) -> Result<Vec<InvocationRecord>, ContextError> {
    crate::sqlite::context::read_invocations(path.as_ref(), node, after, limit)
}
/// Reads paginated receipt metadata from a suspended session directory without opening its blob store.
///
/// # Errors
/// Returns an error for an invalid page limit or cursor, unsupported schema, locked owner, or unreadable session.
pub fn read_events(
    path: impl AsRef<std::path::Path>,
    id: InvocationId,
    after: u64,
    limit: usize,
) -> Result<Vec<ContextEvent>, ContextError> {
    crate::sqlite::context::read_events(path.as_ref(), id, after, limit)
}

pub(crate) fn package_descriptor(package: &PackageGrant, policy: &ContextPolicy) -> Value {
    let mut value = serde_json::json!({"handle":package.handle,"metadata":package.metadata,"payload":package.payload});
    if package.metadata {
        value["package_id"] = Value::String(package_key(package.package_id));
        value["object_type"] = Value::String(package.object_type.clone());
        value["content_digest"] = Value::String(package.content_digest.to_string());
        value["received"] = Value::Bool(package.received);
        if policy.ancestor_metadata {
            value["parents"] = serde_json::json!(package.parents);
        }
    }
    value
}

pub(crate) fn member_descriptor(member: &PackageMemberGrant) -> Value {
    use ontography_content::package::ResolvedEntryKind;
    let mut value =
        serde_json::json!({"handle":member.handle,"owner":member.owner,"path":member.path});
    match &member.kind {
        ResolvedEntryKind::Directory => {
            value["kind"] = Value::String("collection".into());
        }
        ResolvedEntryKind::File {
            content,
            executable,
        } => {
            value["kind"] = Value::String("file".into());
            value["size"] = serde_json::json!(content.size());
            value["executable"] = Value::Bool(*executable);
        }
        ResolvedEntryKind::Symlink { target } => {
            value["kind"] = Value::String("symlink".into());
            value["target"] = Value::String(target.clone());
        }
    }
    value
}

pub(crate) fn root_input_descriptor(handle: &str, digest: ContentDigest) -> Value {
    serde_json::json!({"handle":handle,"kind":"payload","root_input":true,"metadata":true,"payload":true,"content_digest":digest.to_string()})
}
