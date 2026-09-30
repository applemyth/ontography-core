//! Minimal serialized hosting for canonical kernel proposals.
//!
//! This module knows nothing about executable node kinds, retries, or
//! supervision. It owns the current graph and logical state and exposes bounded
//! trigger observations from admitted ingress metadata. Mutations commit and
//! publish under one lock, without an intervening cancellation boundary.
//!
//! # Failure classification
//!
//! Every session operation reports failure through [`SessionError`]; every
//! mutation additionally reports the kernel's own rejection as the inner
//! `Err` of its result, so a rejection is never confused with an operational
//! failure. The classification is uniform:
//!
//! - A kernel rejection leaves the state unchanged and is returned as
//!   `Ok(Err(rejection))` with that operation's own rejection type.
//! - Trusted code (a contract validator, an evaluator) that panics before the
//!   operation has written anything is [`SessionError::Panicked`]; the
//!   transaction is discarded and the session stays open.
//! - A storage failure on a read path, while preparing a rewrite, or while
//!   reading the payload evidence a transfer or rewrite must check, is
//!   [`SessionError::Storage`]; nothing was written and the session stays
//!   open. Missing or corrupt evidence for a package the store has a row for
//!   is such a failure, never a kernel rejection.
//! - A storage failure or panic on a write path, once the operation has begun
//!   writing, is [`SessionError::Faulted`]: commit acknowledgment is
//!   uncertain, so the session records a durable fault and refuses every
//!   further mutation and coherent read until it is reopened.
//! - The invocation context store follows the same rule through
//!   [`ContextError`](crate::context::ContextError): a lifecycle, budget, or
//!   read failure before any write is that error's own refusal and leaves the
//!   session open; a context-store or object write that fails once begun
//!   faults the session and is reported as `ContextError::Storage` carrying
//!   the retained fault message.

mod context;

use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, Weak};

use thiserror::Error;
use tokio::sync::{Mutex as AsyncMutex, watch};

use super::object_store::{ObjectStore, ObjectStoreError};
use super::panic_message;
use super::sqlite::{Committed, OpenedSqliteSession, SqliteSession, SqliteStateError, unlinked};
use ontography_calculus::storage::{
    ActivationId, Delivery, PackageId, PackageRecord, Retirement, RetirementReason, Transition,
};
use ontography_calculus::{
    ActivationProposal, ContentDigest, DenyAll, EditPolicy, ExtensionError, Kernel, Payload, Phase,
    Reject, RetireError, RewriteError, RewriteRequest, State, StateParts, StateRestoreError,
    TransferError,
};
use ontography_content::content::{ContentError, ContentId, ContentReader, ContentStore};
use ontography_content::package::PackageLimits;

type Text = Arc<str>;

/// Result of asking the kernel to consider one proposal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProposalDecision {
    /// The kernel atomically committed the proposal.
    Committed(ActivationId),
    /// The kernel rejected the proposal and left accepted state unchanged.
    Rejected(Reject),
}

/// Operational failure of one session operation.
///
/// Kernel rejections are never reported here; each mutation returns them as
/// the inner `Err` of its result. Every method documents the subset of
/// variants it can return. See the module documentation for the
/// classification rule behind [`Self::Faulted`], [`Self::Storage`], and
/// [`Self::Panicked`].
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum SessionError {
    /// Proposal admission has been explicitly closed.
    #[error("proposal session is closed")]
    Closed,
    /// The execution that owned this submission path has terminated.
    #[error("execution proposal custody is revoked")]
    Revoked,
    /// Storage or trusted code failed after a write began, now or earlier.
    ///
    /// The payload is the retained fault message. Reopen the session to
    /// resolve the durable state before observing it again.
    #[error("proposal session faulted: {0}")]
    Faulted(Text),
    /// Storage, or the payload evidence an evaluation reads, could not be
    /// read; nothing was written and the session is open.
    #[error("proposal session storage failed: {0}")]
    Storage(Text),
    /// Trusted kernel or contract code panicked before anything was written.
    ///
    /// The operation's transaction was discarded and the session stays open.
    #[error("trusted code panicked before writing: {0}")]
    Panicked(Text),
    /// An explicit artifact dependency is missing, incomplete, or corrupt.
    #[error("proposal content is unavailable: {0}")]
    Content(Text),
    /// The query named no node in the kernel definition.
    #[error("unknown node {0}")]
    UnknownNode(Text),
    /// The query named no edge in the kernel definition.
    #[error("unknown edge {0}")]
    UnknownEdge(Text),
    /// The query named an edge that does not enter the selected node.
    #[error("edge {edge_id} does not enter node {node_id}")]
    EdgeTargetMismatch {
        /// Selected graph node.
        node_id: Text,
        /// Edge whose static target differs from `node_id`.
        edge_id: Text,
    },
    /// A bounded pending query requested an empty page.
    #[error("pending page limit must be greater than zero")]
    InvalidPageLimit,
}

/// The operational error of a submission; an alias of [`SessionError`].
///
/// A submission can return `Closed`, `Revoked`, `Faulted`, `Panicked`, and
/// `Content`.
pub type SubmitError = SessionError;

/// The operational error of a rewrite, transfer, retirement, or extension; an
/// alias of [`SessionError`].
///
/// Each of those methods returns the kernel's rejection as its inner `Err`
/// and documents the reachable subset of this alias.
pub type SessionTransitionError = SessionError;

impl From<SqliteStateError> for SessionError {
    fn from(error: SqliteStateError) -> Self {
        match error {
            SqliteStateError::Content(error) => Self::Content(Arc::from(error.to_string())),
            SqliteStateError::Panicked(message) => Self::Panicked(message),
            other => Self::Storage(Arc::from(other.to_string())),
        }
    }
}

impl From<ObjectStoreError> for SessionError {
    fn from(error: ObjectStoreError) -> Self {
        Self::Storage(Arc::from(error.to_string()))
    }
}

impl From<ContentError> for SessionError {
    fn from(error: ContentError) -> Self {
        Self::Storage(Arc::from(error.to_string()))
    }
}

/// An admitted rewrite and retirement report bound to one session state.
pub struct SessionRewrite {
    owner: Weak<SessionCore>,
    transition: Transition,
    next_kernel: Arc<Kernel>,
    retirements: BTreeMap<PackageId, RetirementReason>,
}

impl fmt::Debug for SessionRewrite {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SessionRewrite")
            .field("revision", &self.revision())
            .field("retirements", self.retirements())
            .finish_non_exhaustive()
    }
}

impl SessionRewrite {
    /// Returns the graph that would be installed.
    #[must_use]
    pub const fn next_kernel(&self) -> &Arc<Kernel> {
        &self.next_kernel
    }

    /// Returns every package this rewrite would retire and its reason.
    #[must_use]
    pub const fn retirements(&self) -> &BTreeMap<PackageId, RetirementReason> {
        &self.retirements
    }

    /// Returns the predecessor revision used to prepare this report.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.transition.base().revision()
    }
}

/// The revision and package retirements of one committed rewrite.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteOutcome {
    revision: u64,
    retirements: BTreeMap<PackageId, RetirementReason>,
}

impl RewriteOutcome {
    /// Returns the committed state revision.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns the packages removed from the live frontier.
    #[must_use]
    pub const fn retirements(&self) -> &BTreeMap<PackageId, RetirementReason> {
        &self.retirements
    }
}

/// Failure while opening or restoring a proposal session.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum SessionOpenError {
    /// The proposal runtime has begun terminal shutdown.
    #[error("proposal runtime is shutting down")]
    ShuttingDown,
    /// The runtime exhausted its process-local session identity space.
    #[error("proposal runtime session identity space is exhausted")]
    IdentityExhausted,
    /// Persisted records or their external payload evidence could not be restored.
    #[error("could not restore proposal session state: {0}")]
    Restore(#[source] Box<StateRestoreError>),
    /// Trusted kernel or contract code panicked while restoring or verifying.
    ///
    /// Nothing was opened; the store on disk is unchanged.
    #[error("proposal session restoration panicked: {0}")]
    Panicked(Text),
    /// Session storage could not be created, opened, or verified.
    #[error("could not open proposal session storage: {0}")]
    Storage(Text),
}

impl From<StateRestoreError> for SessionOpenError {
    fn from(error: StateRestoreError) -> Self {
        Self::Restore(Box::new(error))
    }
}

impl From<SqliteStateError> for SessionOpenError {
    fn from(error: SqliteStateError) -> Self {
        Self::Storage(Arc::from(error.to_string()))
    }
}

impl From<ObjectStoreError> for SessionOpenError {
    fn from(error: ObjectStoreError) -> Self {
        Self::Storage(Arc::from(error.to_string()))
    }
}

/// Explicit proposal-admission lifecycle, independent of frontier shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SessionStatus {
    /// Proposals are still passed to the kernel.
    Open,
    /// Proposal admission was explicitly closed; read-only queries remain live.
    Closed,
    /// Storage or trusted code failed; reopen to resolve the durable state.
    Faulted,
}

impl SessionStatus {
    const fn is_terminal(self) -> bool {
        matches!(self, Self::Closed | Self::Faulted)
    }
}

/// Point-in-time accepted state owned by one proposal session.
///
/// Artifact dependencies are captured as identities. Their bytes remain in the
/// content store and must be exported separately when relocating a workflow.
#[derive(Clone, Debug)]
pub struct SessionSnapshot {
    status: SessionStatus,
    kernel: Arc<Kernel>,
    state: State,
    activation_content: BTreeMap<ActivationId, Vec<ContentId>>,
    revision: u64,
    fault: Option<Text>,
}

impl SessionSnapshot {
    /// Returns the current graph captured with this exact state.
    #[must_use]
    pub const fn kernel(&self) -> &Arc<Kernel> {
        &self.kernel
    }
    /// Returns the proposal-admission lifecycle at the snapshot point.
    #[must_use]
    pub const fn status(&self) -> SessionStatus {
        self.status
    }

    /// Returns the exact accepted kernel state.
    #[must_use]
    pub const fn state(&self) -> &State {
        &self.state
    }

    /// Returns explicit artifact dependencies, grouped by accepting activation.
    ///
    /// These references do not materialize artifact bytes. The graph-only
    /// `State` and `StateParts` values do not carry this supplemental metadata.
    #[must_use]
    pub const fn activation_content(&self) -> &BTreeMap<ActivationId, Vec<ContentId>> {
        &self.activation_content
    }

    /// Returns the revision of this graph and frontier snapshot.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns the retained operational fault, when the session faulted.
    #[must_use]
    pub fn fault(&self) -> Option<&str> {
        self.fault.as_deref()
    }
}

/// Point-in-time digest-bearing package projection, captured with its graph.
#[derive(Clone, Debug)]
pub struct PendingFrontier {
    kernel: Arc<Kernel>,
    revision: u64,
    packages: Vec<(PackageId, PackageRecord)>,
}

/// One retained package and the causal inputs of its producing activation.
///
/// This metadata query reads no payloads or activation results. Consumed and
/// retired packages remain available; current custody is not represented here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageHistory {
    package: PackageRecord,
    inputs: Vec<PackageId>,
}

impl PackageHistory {
    pub(crate) fn new(package: PackageRecord, inputs: Vec<PackageId>) -> Self {
        Self { package, inputs }
    }

    /// Returns the retained package metadata, including its immutable digest.
    #[must_use]
    pub const fn package(&self) -> &PackageRecord {
        &self.package
    }

    /// Returns the producer's consumed inputs in canonical package-ID order.
    ///
    /// A root activation has no package inputs. These are immediate causal
    /// predecessors, rather than all transitive ancestors or content references.
    #[must_use]
    pub fn inputs(&self) -> &[PackageId] {
        &self.inputs
    }
}

impl PendingFrontier {
    /// Returns the graph captured with this bounded frontier observation.
    #[must_use]
    pub const fn kernel(&self) -> &Arc<Kernel> {
        &self.kernel
    }
    /// Returns the state revision at which the projection was taken.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns pending packages in canonical package-identity order.
    #[must_use]
    pub fn packages(&self) -> &[(PackageId, PackageRecord)] {
        &self.packages
    }
}

/// Exact live package counts at one node in a frontier observation.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FrontierCounts {
    pub(super) received: usize,
    pub(super) outbound: usize,
}

impl FrontierCounts {
    /// Returns packages delivered here and still live, including speculative work.
    #[must_use]
    pub const fn received(self) -> usize {
        self.received
    }

    /// Returns packages held here awaiting transfer.
    #[must_use]
    pub const fn outbound(self) -> usize {
        self.outbound
    }
}

/// Current topology, exact node counts, and bounded package details at one revision.
///
/// Empty nodes may be absent from `counts`. Package details are independently
/// limited for each phase; their lengths must not be used as total counts.
#[derive(Clone, Debug)]
pub struct FrontierOverview {
    kernel: Arc<Kernel>,
    revision: u64,
    counts: BTreeMap<Text, FrontierCounts>,
    received: Vec<(PackageId, PackageRecord)>,
    outbound: Vec<(PackageId, PackageRecord)>,
}

impl FrontierOverview {
    /// Returns the graph captured with these package observations.
    #[must_use]
    pub const fn kernel(&self) -> &Arc<Kernel> {
        &self.kernel
    }

    /// Returns the common committed mutation revision.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns exact counts, indexed by node incarnation identity.
    #[must_use]
    pub const fn counts(&self) -> &BTreeMap<Text, FrontierCounts> {
        &self.counts
    }

    /// Returns the first bounded page of live delivered packages in identity order.
    #[must_use]
    pub fn received(&self) -> &[(PackageId, PackageRecord)] {
        &self.received
    }

    /// Returns the first bounded page of outbound packages in identity order.
    #[must_use]
    pub fn outbound(&self) -> &[(PackageId, PackageRecord)] {
        &self.outbound
    }
}

/// Coalesced notification that the graph or package frontier changed.
///
/// Revisions are hints rather than package custody. After observing a revision,
/// query [`SessionHandle::pending_page`] or [`SessionHandle::pending_at`] for
/// current truth. A new subscription immediately exposes the current revision,
/// so a relaunched consumer can recover pending work without replaying
/// notifications.
#[derive(Clone, Debug)]
pub struct FrontierReceiver {
    receiver: watch::Receiver<u64>,
}

impl FrontierReceiver {
    /// Returns the latest published state revision.
    #[must_use]
    pub fn revision(&self) -> u64 {
        *self.receiver.borrow()
    }

    /// Waits for a state revision not yet observed by this receiver.
    ///
    /// A session close does not manufacture a frontier revision. Observe
    /// [`SessionHandle::status`] separately when a waiter must also stop on
    /// lifecycle changes.
    pub async fn changed(&mut self) -> u64 {
        if self.receiver.changed().await.is_err() {
            return *self.receiver.borrow();
        }
        *self.receiver.borrow_and_update()
    }
}

struct SessionState {
    kernel: Arc<Kernel>,
    status: SessionStatus,
    facts: SqliteSession,
    objects: ObjectStore,
    revision: u64,
    fault: Option<Text>,
    readable: bool,
}

#[derive(Debug)]
pub(crate) struct SubmissionCustody {
    revoked: AtomicBool,
    owner_id: String,
}

impl SubmissionCustody {
    pub(super) fn new() -> Self {
        Self {
            revoked: AtomicBool::new(false),
            owner_id: uuid::Uuid::new_v4().to_string(),
        }
    }
    pub(super) fn revoke(&self) {
        self.revoked.store(true, Ordering::Release);
    }
    fn is_revoked(&self) -> bool {
        self.revoked.load(Ordering::Acquire)
    }
}

struct SessionCore {
    policy: Arc<dyn EditPolicy>,
    /// Bounds on resolving content packages, fixed when the session opened.
    package_limits: PackageLimits,
    inner: AsyncMutex<SessionState>,
    status: watch::Sender<SessionStatus>,
    frontier: watch::Sender<u64>,
}

impl SessionCore {
    async fn frontier_overview(&self, limit: usize) -> Result<FrontierOverview, SessionError> {
        if limit == 0 {
            return Err(SessionError::InvalidPageLimit);
        }
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        let counts = inner.facts.frontier_counts()?;
        let received = inner.facts.frontier_page(Phase::In, None, None, limit)?;
        let outbound = inner.facts.frontier_page(Phase::Out, None, None, limit)?;
        if received.revision != inner.revision || outbound.revision != inner.revision {
            return Err(SessionError::Storage(Arc::from(
                "frontier revision disagrees with current graph; reopen the session",
            )));
        }
        Ok(FrontierOverview {
            kernel: Arc::clone(&inner.kernel),
            revision: inner.revision,
            counts,
            received: received.packages,
            outbound: outbound.packages,
        })
    }

    /// The one fault ladder of every mutation.
    ///
    /// `op` evaluates and writes inside one storage transaction and returns
    /// the committed value with its revision, or the operation's own kernel
    /// rejection. The ladder classifies its outcome exactly as the module
    /// documentation states: a rejection is `Ok(Err(..))`; an error that
    /// storage can only produce before writing anything is typed and leaves
    /// the session open; any other storage error, and any panic that escapes
    /// `op`, faults the session because commit acknowledgment is uncertain.
    /// A committed transition publishes its revision before returning, with
    /// no await or cancellation boundary in between.
    fn transition<T, R>(
        &self,
        inner: &mut SessionState,
        op: impl FnOnce(&mut SessionState) -> Result<Result<Committed<T>, R>, SqliteStateError>,
    ) -> Result<Result<T, R>, SessionError> {
        match catch_unwind(AssertUnwindSafe(|| op(inner))) {
            Ok(Ok(Ok(committed))) => {
                publish_revision(inner, &self.frontier, committed.revision);
                Ok(Ok(committed.value))
            }
            Ok(Ok(Err(rejection))) => Ok(Err(rejection)),
            Ok(Err(error)) if error.before_any_write() => Err(SessionError::from(error)),
            Ok(Err(error)) => Err(SessionError::Faulted(
                self.fault(inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SessionError::Faulted(
                self.fault(inner, panic_message(panic)),
            )),
        }
    }

    async fn submit(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
        custody: Option<&SubmissionCustody>,
    ) -> Result<ProposalDecision, SessionError> {
        let mut inner = self.inner.lock().await;
        if custody.is_some_and(SubmissionCustody::is_revoked) {
            return Err(SessionError::Revoked);
        }
        require_open(&inner)?;
        // User work runs outside this lock. Once admitted here, a transition is
        // committed and published without an await or cancellation boundary.
        let decision = self.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            let SessionState { facts, objects, .. } = state;
            facts.submit(&kernel, objects, proposal, &contents, unlinked)
        })?;
        Ok(match decision {
            Ok(activation_id) => ProposalDecision::Committed(activation_id),
            Err(reject) => ProposalDecision::Rejected(reject),
        })
    }

    async fn prepare_rewrite(
        &self,
        request: &RewriteRequest,
    ) -> Result<Result<(Transition, Arc<Kernel>), RewriteError>, SessionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        // Preparation reads only; a storage error or evaluator panic here is
        // typed and leaves the session open.
        let SessionState {
            facts,
            kernel,
            objects,
            ..
        } = &mut *inner;
        Ok(facts.prepare_rewrite(kernel, objects, self.policy.as_ref(), request)?)
    }

    async fn commit_rewrite(
        &self,
        plan: SessionRewrite,
    ) -> Result<Result<RewriteOutcome, RewriteError>, SessionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let SessionRewrite {
            transition,
            next_kernel,
            retirements,
            ..
        } = plan;
        let committed = self.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            let committed = state
                .facts
                .commit_rewrite(&kernel, &transition, &next_kernel)?;
            if committed.is_ok() {
                state.kernel = Arc::clone(&next_kernel);
            }
            Ok(committed)
        })?;
        Ok(committed.map(|()| RewriteOutcome {
            revision: inner.revision,
            retirements,
        }))
    }

    async fn transfer(
        &self,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Result<Delivery, TransferError>, SessionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        self.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            let SessionState { facts, objects, .. } = state;
            facts.transfer(&kernel, objects, package_id, edge_id)
        })
    }

    async fn retire(
        &self,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Result<Retirement, RetireError>, SessionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        self.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            state.facts.retire(&kernel, package_id, evidence)
        })
    }

    async fn extend(&self, next: Arc<Kernel>) -> Result<Result<u64, ExtensionError>, SessionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let committed = self.transition(&mut inner, |state| {
            let kernel = Arc::clone(&state.kernel);
            let committed = state.facts.extend(&kernel, &next)?;
            if committed.is_ok() {
                state.kernel = Arc::clone(&next);
            }
            Ok(committed)
        })?;
        Ok(committed.map(|()| inner.revision))
    }

    /// Faults the session and returns the message it retains.
    ///
    /// A storage error can leave commit acknowledgment uncertain, so every
    /// coherent read is fenced until reopening resolves the durable state. If
    /// the durable fault marker itself cannot be written, that failure is part
    /// of the retained message: the next opener must not mistake an unmarked
    /// store for a healthy one.
    fn fault(&self, inner: &mut SessionState, message: Text) -> Text {
        let message = match inner.facts.fault(&message) {
            Ok(()) => message,
            Err(error) => Arc::from(format!(
                "{message}; the durable fault marker could not be written: {error}"
            )),
        };
        let message = match inner.facts.reconcile_objects(&inner.objects) {
            Ok(()) => message,
            Err(error) => Arc::from(format!(
                "{message}; content reconciliation requires reopening: {error}"
            )),
        };
        inner.readable = false;
        inner.fault = Some(Arc::clone(&message));
        inner.status = SessionStatus::Faulted;
        self.status.send_replace(SessionStatus::Faulted);
        message
    }

    async fn close(&self) {
        let mut inner = self.inner.lock().await;
        if inner.status == SessionStatus::Open {
            if let Err(error) = inner.facts.close() {
                self.fault(&mut inner, Arc::from(error.to_string()));
                return;
            }
            inner.status = SessionStatus::Closed;
            self.status.send_replace(SessionStatus::Closed);
        }
    }

    async fn snapshot(&self) -> Result<SessionSnapshot, SessionError> {
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        let state = catch_unwind(AssertUnwindSafe(|| {
            inner.facts.snapshot(&inner.kernel, &inner.objects)
        }))
        .map_err(|panic| SessionError::Panicked(panic_message(panic)))??;
        if state.definition_id() != inner.kernel.id()
            || state.definition_fingerprint() != inner.kernel.fingerprint()
            || state.revision() != inner.revision
        {
            return Err(SessionError::Storage(Arc::from(
                "current graph and durable state disagree; reopen the session",
            )));
        }
        Ok(SessionSnapshot {
            status: inner.status,
            kernel: Arc::clone(&inner.kernel),
            state,
            activation_content: inner.facts.all_activation_content()?,
            revision: inner.revision,
            fault: inner.fault.clone(),
        })
    }

    async fn packages(
        &self,
        phase: Phase,
        node_id: Option<&str>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        if limit == 0 {
            return Err(SessionError::InvalidPageLimit);
        }
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        if let Some(node) = node_id {
            require_node(&inner.kernel, node)?;
        }
        let read = inner.facts.frontier_page(phase, node_id, after, limit)?;
        Ok(PendingFrontier {
            kernel: Arc::clone(&inner.kernel),
            revision: read.revision,
            packages: read.packages,
        })
    }

    async fn next_trigger(&self, node_id: &str) -> Result<PendingFrontier, SessionError> {
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        require_node(&inner.kernel, node_id)?;
        let definition = inner
            .kernel
            .node_definition(node_id)
            .expect("admitted node definition");
        let incoming_edges = inner
            .kernel
            .graph()
            .incoming_edge_ids(node_id)
            .expect("admitted node ingress");
        let read = inner
            .facts
            .next_trigger(node_id, definition.ingress_mode(), incoming_edges)?;
        Ok(PendingFrontier {
            kernel: Arc::clone(&inner.kernel),
            revision: read.revision,
            packages: read.packages,
        })
    }

    async fn next_pending_on_edge(
        &self,
        node_id: &str,
        edge_id: &str,
    ) -> Result<PendingFrontier, SessionError> {
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        require_node(&inner.kernel, node_id)?;
        let edge = inner
            .kernel
            .graph()
            .edge(edge_id)
            .ok_or_else(|| SessionError::UnknownEdge(Arc::from(edge_id)))?;
        if edge.target() != node_id {
            return Err(SessionError::EdgeTargetMismatch {
                node_id: Arc::from(node_id),
                edge_id: Arc::from(edge_id),
            });
        }
        let read = inner.facts.next_pending_on_edge(node_id, edge_id)?;
        Ok(PendingFrontier {
            kernel: Arc::clone(&inner.kernel),
            revision: read.revision,
            packages: read.packages,
        })
    }

    async fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SessionError> {
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.facts.package_history(package_id)?)
    }

    async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        let inner = self.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.objects.get(digest)?)
    }
}

/// Handle to one independently serialized canonical kernel state.
#[derive(Clone)]
pub struct SessionHandle {
    core: Arc<SessionCore>,
    registration: Arc<SessionRegistration>,
}

#[derive(Clone)]
pub(crate) struct InvocationSession {
    core: Weak<SessionCore>,
    registration: Weak<SessionRegistration>,
}
impl InvocationSession {
    pub(crate) fn upgrade(&self) -> Result<SessionHandle, crate::context::ContextError> {
        Ok(SessionHandle {
            core: self
                .core
                .upgrade()
                .ok_or(crate::context::ContextError::Closed)?,
            registration: self
                .registration
                .upgrade()
                .ok_or(crate::context::ContextError::Closed)?,
        })
    }
}
impl SessionHandle {
    pub(crate) fn owns_invocation(&self, handle: &crate::context::InvocationHandle) -> bool {
        Weak::ptr_eq(&Arc::downgrade(&self.core), &handle.inner.session.core)
    }

    fn invocation_session(&self) -> InvocationSession {
        InvocationSession {
            core: Arc::downgrade(&self.core),
            registration: Arc::downgrade(&self.registration),
        }
    }
}

impl fmt::Debug for SessionHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SessionHandle")
            .field("status", &self.status())
            .field("frontier_revision", &*self.core.frontier.borrow())
            .finish_non_exhaustive()
    }
}

impl SessionHandle {
    /// Captures topology, exact live node counts, and bounded details of both phases.
    ///
    /// All graph and package fields are read under the same session lock. This
    /// observation does not reserve packages or read payloads or activation history.
    /// Executable activity is separate operational telemetry.
    ///
    /// # Errors
    /// `InvalidPageLimit`, `Faulted`, or `Storage`.
    pub async fn frontier_overview(&self, limit: usize) -> Result<FrontierOverview, SessionError> {
        self.core.frontier_overview(limit).await
    }
    fn new(core: Arc<SessionCore>, registration: SessionRegistration) -> Self {
        Self {
            core,
            registration: Arc::new(registration),
        }
    }

    /// Returns the current graph from the serialized session owner.
    ///
    /// # Errors
    /// `Faulted`: reopen after a failure with uncertain commit publication.
    pub async fn kernel(&self) -> Result<Arc<Kernel>, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        Ok(Arc::clone(&inner.kernel))
    }

    /// Returns the latest proposal-admission lifecycle observed by this handle.
    #[must_use]
    pub fn status(&self) -> SessionStatus {
        *self.core.status.borrow()
    }

    /// Creates a coalesced frontier-revision receiver.
    #[must_use]
    pub fn frontier(&self) -> FrontierReceiver {
        FrontierReceiver {
            receiver: self.core.frontier.subscribe(),
        }
    }

    /// Subscribes to session changes after validating a current node.
    ///
    /// Notifications are coalesced across all nodes and graph changes. Query
    /// current state after waking; a subscription does not reserve its node.
    ///
    /// # Errors
    /// `UnknownNode` or `Faulted`.
    pub async fn frontier_at(
        &self,
        node_id: impl Into<Text>,
    ) -> Result<FrontierReceiver, SessionError> {
        let node_id = node_id.into();
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        require_node(&inner.kernel, &node_id)?;
        Ok(self.frontier())
    }

    /// Prepares a graph replacement and its exact package retirement report.
    ///
    /// Preparation reads the live frontier only and writes nothing; the
    /// kernel's rejection is the inner `Err`.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, `Storage` (including payload evidence the cleanup
    /// must read), or `Panicked`.
    pub async fn prepare_rewrite(
        &self,
        request: &RewriteRequest,
    ) -> Result<Result<SessionRewrite, RewriteError>, SessionError> {
        Ok(self
            .core
            .prepare_rewrite(request)
            .await?
            .map(|(transition, next_kernel)| SessionRewrite {
                owner: Arc::downgrade(&self.core),
                retirements: transition.retirements(),
                transition,
                next_kernel,
            }))
    }

    /// Commits the prepared graph and frontier together if its state is current.
    ///
    /// A plan whose base revision is no longer current, and a plan prepared by
    /// another session (whose base names a state this session never held),
    /// are both the kernel's own [`RewriteError::Stale`] and leave the state
    /// unchanged.
    ///
    /// # Errors
    /// `Closed` or `Faulted`. A failed durable commit faults admission and
    /// requires reopening before reading coherent current state.
    pub async fn commit_rewrite(
        &self,
        plan: SessionRewrite,
    ) -> Result<Result<RewriteOutcome, RewriteError>, SessionError> {
        if !Weak::ptr_eq(&plan.owner, &Arc::downgrade(&self.core)) {
            return Ok(Err(RewriteError::Stale));
        }
        self.core.commit_rewrite(plan).await
    }

    /// Delivers one live outbound package through a currently accepting edge.
    ///
    /// The kernel's rejection is the inner `Err`.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, `Storage` (the package's payload evidence could
    /// not be read), or `Panicked`.
    pub async fn transfer(
        &self,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Result<Delivery, TransferError>, SessionError> {
        self.core.transfer(package_id, edge_id).await
    }

    /// Retires one live package, citing an optional accepted activation as evidence.
    ///
    /// The package leaves the frontier and a canonical retirement record is
    /// stored; history, deliveries, and immutable package facts are unchanged.
    /// The kernel's rejection is the inner `Err`.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, or `Panicked`.
    pub async fn retire(
        &self,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Result<Retirement, RetireError>, SessionError> {
        self.core.retire(package_id, evidence).await
    }

    /// Installs a monotone vocabulary extension of the current definition.
    ///
    /// `next` must keep the graph, annotations, and existing contracts
    /// unchanged and add schema vocabulary or contracts. The frontier is
    /// untouched. Reopening the session later requires supplying `next`. The
    /// kernel's rejection is the inner `Err`; success returns the revision.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, or `Panicked`.
    pub async fn extend(
        &self,
        next: Arc<Kernel>,
    ) -> Result<Result<u64, ExtensionError>, SessionError> {
        self.core.extend(next).await
    }

    /// Submits one canonical root or package-triggered proposal.
    ///
    /// The outer result reports only operational failure;
    /// [`ProposalDecision::Rejected`] is the exact graph-admission decision from
    /// the kernel. Concurrent submissions are considered in state-lock order.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, or `Panicked`.
    pub async fn submit(
        &self,
        proposal: ActivationProposal,
    ) -> Result<ProposalDecision, SessionError> {
        self.core.submit(proposal, Vec::new(), None).await
    }

    /// Submits a proposal with explicit immutable artifact dependencies.
    ///
    /// The artifacts must already be complete in this session's content store.
    /// Accepted dependencies remain retained with activation history even after
    /// their caller-managed pins are released. Contracts still validate the
    /// proposal's exact bytes; declaring a dependency does not validate its
    /// application-specific meaning.
    ///
    /// # Errors
    /// `Closed`, `Faulted`, `Panicked`, or `Content`.
    pub async fn submit_with_content(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, SessionError> {
        self.core.submit(proposal, contents, None).await
    }

    /// Submits under an execution's custody; adds `Revoked` to the errors.
    pub(super) async fn submit_custodied(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
        custody: &SubmissionCustody,
    ) -> Result<ProposalDecision, SessionError> {
        self.core.submit(proposal, contents, Some(custody)).await
    }

    /// Closes proposal admission while retaining read-only access to final state.
    ///
    /// Proposals linearized before this call receive kernel decisions. Open
    /// sessions transition to [`SessionStatus::Closed`], after which submissions
    /// receive [`SessionError::Closed`]. Faulted sessions retain their more
    /// informative terminal status and error. This is idempotent, including
    /// after proposal-runtime shutdown.
    pub async fn close(&self) {
        self.core.close().await;
    }

    /// Waits until proposal admission is closed or faulted.
    pub async fn wait_closed(&self) -> SessionStatus {
        let mut status = self.core.status.subscribe();
        loop {
            let current = *status.borrow_and_update();
            if current.is_terminal() {
                return current;
            }
            if status.changed().await.is_err() {
                return *status.borrow();
            }
        }
    }

    /// Returns an exact point-in-time clone of accepted state.
    ///
    /// This remains available after session close and proposal-runtime shutdown.
    /// Persistent sessions should prefer [`Self::try_snapshot`] when storage
    /// failure must be reported instead of treated as an invariant violation.
    ///
    /// # Panics
    ///
    /// Panics when storage cannot be read, its records are inconsistent, or a
    /// live fault requires reopening before coherent state can be observed.
    pub async fn snapshot(&self) -> SessionSnapshot {
        self.try_snapshot()
            .await
            .expect("session snapshot storage remains readable")
    }

    /// Tries to materialize the complete accepted state.
    ///
    /// This is intentionally an eager export operation. Long-running callers
    /// should use bounded frontier queries for routine execution. Besides
    /// checking the exported records, it checks that the derived readiness
    /// indexes agree with them, at O(frontier) cost.
    ///
    /// # Errors
    /// `Faulted`, `Storage` (undecodable or inconsistent records), or
    /// `Panicked`. This does not replay historical rules.
    pub async fn try_snapshot(&self) -> Result<SessionSnapshot, SessionError> {
        self.core.snapshot().await
    }

    /// Reads one retained package and its producer's immediate causal inputs.
    ///
    /// Returns `None` for an unknown package identity. The query uses indexed
    /// metadata and does not read payloads or materialize the session history.
    /// It remains available after package consumption, retirement, or session
    /// close. Reading does not reserve or consume packages.
    ///
    /// # Errors
    /// `Faulted` or `Storage`.
    pub async fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SessionError> {
        self.core.package_history(package_id).await
    }

    /// Resolves exact bytes in this session's object pool by content digest.
    ///
    /// # Errors
    /// `Faulted`, or `Storage` when durable content is unreadable or fails
    /// its digest.
    pub async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        self.core.content(digest).await
    }

    /// Returns this session's cloneable blob, artifact, and transfer API.
    ///
    /// The returned handle owns its storage access. File work, streams, and
    /// transfers do not hold the session's graph-admission lock. Payloads and
    /// artifacts share the session's iroh store.
    ///
    /// # Errors
    /// `Faulted`.
    pub async fn content_store(&self) -> Result<ContentStore, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.objects.content_store())
    }

    /// Returns retained payload size without allocating the complete payload.
    ///
    /// This metadata is useful for allocation limits; it does not authenticate
    /// the bytes. Use a content read for integrity verification.
    ///
    /// # Errors
    /// `Faulted` or `Storage`.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.objects.content_size(digest)?)
    }

    /// Reads exact offsets from a retained payload with integrity verification.
    ///
    /// Establishing the SHA-256 to BLAKE3 binding can require an incremental
    /// complete verification pass. Returned memory is bounded by the range.
    ///
    /// # Errors
    /// `Faulted` or `Storage` (invalid ranges, storage failures, corrupt
    /// content).
    pub async fn content_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Payload>, SessionError> {
        Ok(self
            .content_store()
            .await?
            .read_digest_range(digest, range)
            .await?
            .map(|bytes| Payload::from(bytes.as_ref())))
    }

    /// Opens a verified, seekable payload reader without holding the session lock.
    ///
    /// # Errors
    /// `Faulted` or `Storage`.
    pub async fn content_reader(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<ContentReader>, SessionError> {
        Ok(self.content_store().await?.digest_reader(digest).await?)
    }

    /// Returns the explicit artifact dependencies retained by an activation.
    ///
    /// Unknown activations and activations without dependencies return an empty
    /// list. This metadata does not read artifact payloads.
    ///
    /// # Errors
    /// `Faulted` or `Storage`.
    pub async fn activation_content(
        &self,
        activation_id: ActivationId,
    ) -> Result<Vec<ContentId>, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.facts.activation_content(activation_id)?)
    }

    /// Returns one bounded page of currently pending packages.
    ///
    /// `after` is an exclusive canonical package-identity cursor. Pass the last
    /// package ID from one page to retrieve the next. If the returned revision
    /// changes between pages, restart pagination; packages use random
    /// identities and a concurrently inserted package may sort before a cursor.
    /// This remains available after session close and proposal-runtime shutdown.
    ///
    /// # Errors
    /// `InvalidPageLimit`, `Faulted`, or `Storage`.
    pub async fn pending_page(
        &self,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        self.core.packages(Phase::In, None, after, limit).await
    }

    /// Reads a bounded page of outbound packages, optionally at one node.
    ///
    /// `after` is an exclusive identity cursor. Restart pagination if the
    /// returned revision changes between pages.
    ///
    /// # Errors
    /// `InvalidPageLimit`, `UnknownNode`, `Faulted`, or `Storage`.
    pub async fn outbound_page(
        &self,
        node_id: Option<&str>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        self.core.packages(Phase::Out, node_id, after, limit).await
    }

    /// Returns currently pending packages at one current graph node.
    ///
    /// This remains available after session close and proposal-runtime shutdown.
    ///
    /// # Errors
    /// `UnknownNode`, `Faulted`, or `Storage`.
    pub async fn pending_at(
        &self,
        node_id: impl Into<Text>,
    ) -> Result<PendingFrontier, SessionError> {
        let node_id = node_id.into();
        self.core
            .packages(Phase::In, Some(&node_id), None, usize::MAX)
            .await
    }

    /// Returns the next complete package trigger at one current graph node.
    ///
    /// `Any` ingress returns at most one package. `All` ingress returns either
    /// no packages or exactly one package for every current incoming edge under a common
    /// authority. The observation does not reserve its packages; admission
    /// revalidates them when the caller submits a proposal.
    ///
    /// # Errors
    /// `UnknownNode`, `Faulted`, or `Storage`.
    pub async fn next_trigger_at(
        &self,
        node_id: impl Into<Text>,
    ) -> Result<PendingFrontier, SessionError> {
        let node_id = node_id.into();
        self.core.next_trigger(&node_id).await
    }

    /// Returns the least pending package on one incoming edge at a node.
    ///
    /// The returned projection contains zero or one package and does not reserve
    /// it. This supports executables that react to one distinguished edge rather
    /// than to the node's general ingress mode.
    ///
    /// # Errors
    /// `UnknownNode`, `UnknownEdge`, `EdgeTargetMismatch`, `Faulted`, or
    /// `Storage`.
    pub async fn next_pending_on_edge_at(
        &self,
        node_id: impl Into<Text>,
        edge_id: impl Into<Text>,
    ) -> Result<PendingFrontier, SessionError> {
        let node_id = node_id.into();
        let edge_id = edge_id.into();
        self.core.next_pending_on_edge(&node_id, &edge_id).await
    }

    /// Returns one bounded page of pending packages at a current graph node.
    ///
    /// `after` is an exclusive canonical package-identity cursor.
    /// If the returned revision changes between pages, restart pagination.
    ///
    /// # Errors
    /// `InvalidPageLimit`, `UnknownNode`, `Faulted`, or `Storage`.
    pub async fn pending_page_at(
        &self,
        node_id: impl Into<Text>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        let node_id = node_id.into();
        self.core
            .packages(Phase::In, Some(&node_id), after, limit)
            .await
    }
}

struct ProposalRuntimeControl {
    accepting: bool,
    sessions: BTreeMap<u64, Weak<SessionCore>>,
    package_limits: PackageLimits,
}

struct ProposalRuntimeCore {
    kernel: Arc<Kernel>,
    policy: Arc<dyn EditPolicy>,
    next_session_id: AtomicU64,
    control: Mutex<ProposalRuntimeControl>,
}

impl ProposalRuntimeCore {
    fn register_session(
        self: &Arc<Self>,
        session: &Arc<SessionCore>,
    ) -> Result<SessionRegistration, SessionOpenError> {
        let mut control = self
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !control.accepting {
            return Err(SessionOpenError::ShuttingDown);
        }
        let id = self
            .next_session_id
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
                current.checked_add(1)
            })
            .map_err(|_| SessionOpenError::IdentityExhausted)?;
        let previous = control.sessions.insert(id, Arc::downgrade(session));
        debug_assert!(previous.is_none(), "monotone session identity is unique");
        Ok(SessionRegistration {
            runtime: Arc::downgrade(self),
            id,
        })
    }

    fn begin_shutdown(&self) -> Vec<Arc<SessionCore>> {
        let mut control = self
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        control.accepting = false;
        control
            .sessions
            .values()
            .filter_map(Weak::upgrade)
            .collect()
    }

    fn unregister_session(&self, id: u64) {
        self.control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .sessions
            .remove(&id);
    }
}

struct SessionRegistration {
    runtime: Weak<ProposalRuntimeCore>,
    id: u64,
}

impl Drop for SessionRegistration {
    fn drop(&mut self) {
        if let Some(runtime) = self.runtime.upgrade() {
            runtime.unregister_session(self.id);
        }
    }
}

/// Independent host for sessions sharing an initial graph and graph-edit policy.
///
/// This core contains no compiled executable bindings and assigns no semantic
/// type to a graph node. Opaque hosts may retain a [`SessionHandle`], observe
/// its pending frontier, and submit any [`ActivationProposal`].
#[derive(Clone)]
pub struct ProposalRuntime {
    core: Arc<ProposalRuntimeCore>,
}

impl fmt::Debug for ProposalRuntime {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let control = self
            .core
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        formatter
            .debug_struct("ProposalRuntime")
            .field("definition_id", self.core.kernel.id())
            .field("accepting", &control.accepting)
            .field("sessions", &control.sessions.len())
            .finish()
    }
}

impl ProposalRuntime {
    /// Creates a runtime whose sessions accept no graph edits.
    #[must_use]
    pub fn new(kernel: Arc<Kernel>) -> Self {
        Self::with_policy(kernel, Arc::new(DenyAll))
    }

    /// Creates a runtime whose sessions admit graph edits under `policy`.
    #[must_use]
    pub fn with_policy(kernel: Arc<Kernel>, policy: Arc<dyn EditPolicy>) -> Self {
        Self {
            core: Arc::new(ProposalRuntimeCore {
                kernel,
                policy,
                next_session_id: AtomicU64::new(1),
                control: Mutex::new(ProposalRuntimeControl {
                    accepting: true,
                    sessions: BTreeMap::new(),
                    package_limits: PackageLimits::default(),
                }),
            }),
        }
    }

    /// Sets how much a content package may cost to resolve in sessions opened
    /// after this call: documents and bytes read, and entries visible. The
    /// right values depend on the host machine, so the host chooses them.
    pub fn set_package_limits(&self, limits: PackageLimits) {
        self.core
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .package_limits = limits;
    }

    /// Returns the initial graph and fixed schema/contract registry for new sessions.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.core.kernel
    }

    /// Opens an ephemeral session over a new empty canonical state.
    ///
    /// # Errors
    ///
    /// Returns an error when transient storage cannot be initialized, after
    /// runtime shutdown begins, or on process-local session identity exhaustion.
    pub fn open(&self) -> Result<SessionHandle, SessionOpenError> {
        let opened = SqliteSession::create_in_memory(&self.core.kernel)?;
        let objects = ObjectStore::memory(BTreeMap::new())?;
        self.open_sqlite(opened, objects)
    }

    /// Creates a durable proposal session in a new run directory.
    ///
    /// `SQLite` owns indexed occurrence facts at `state.sqlite3`; the sibling
    /// `objects` directory owns exact activation-result and package bytes.
    ///
    /// # Errors
    ///
    /// Returns an error when a persistent session already exists at `path`,
    /// the store cannot be initialized, its definition binding is invalid, or
    /// the proposal runtime is shutting down.
    pub fn create_persistent(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<SessionHandle, SessionOpenError> {
        let run_path = path.as_ref();
        create_run_directory(run_path).map_err(|error| {
            SessionOpenError::Storage(Arc::from(format!(
                "could not create run directory {}: {error}",
                run_path.display()
            )))
        })?;
        let result = (|| {
            let objects = ObjectStore::create(&run_path.join("objects"))?;
            let opened = SqliteSession::create(&run_path.join("state.sqlite3"), &self.core.kernel)?;
            self.open_sqlite(opened, objects)
        })();
        if result.is_err() {
            let _ = std::fs::remove_dir_all(run_path);
        }
        result
    }

    /// Opens an existing durable proposal run.
    ///
    /// Loads the stored current graph under this runtime's definition identity,
    /// fixed schema, and contract registry; its topology may differ from the
    /// runtime's initial graph. This path trusts a store previously created and
    /// exclusively owned by this implementation; it does not replay historical
    /// contracts or rewrites. Open sessions resume admission. Faulted sessions
    /// resume only after checkpoint, content, and invocation integrity checks;
    /// closed sessions retain their terminal lifecycle with coherent read access.
    /// Every open checks derived readiness against the frontier and scans
    /// committed graph and invocation references to reclaim orphan ledger tags.
    /// Fault recovery additionally reads and verifies all committed content.
    ///
    /// # Errors
    ///
    /// Returns an error when the store is absent, incompatible, corrupt, or
    /// the proposal runtime is shutting down.
    pub fn open_persistent(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<SessionHandle, SessionOpenError> {
        let run_path = path.as_ref();
        // Acquire the run's ownership lock before starting another storage
        // engine. A competing opener must fail without entering FsStore.
        let opened = SqliteSession::open(&run_path.join("state.sqlite3"), &self.core.kernel)?;
        let objects = ObjectStore::open(&run_path.join("objects"))?;
        self.open_sqlite(opened, objects)
    }

    /// Opens and verifies a durable run with a fixed-graph activation history.
    ///
    /// This operation materializes and replays the complete occurrence graph
    /// with every retained package payload. The stored definition identity and
    /// current graph fingerprint must match this runtime's initial kernel.
    /// It is intended for imported-state
    /// validation and audits, not bounded-memory routine restart. Runs containing
    /// rewrites, explicit transfers, retirements, or vocabulary extensions require
    /// trusted current-state loading via [`Self::open_persistent`].
    ///
    /// # Errors
    ///
    /// Returns an error when any historical record, derived target, content
    /// object, contract proof, or definition binding is invalid, or the run
    /// contains transitions outside fixed-graph activation history.
    pub fn open_persistent_verified(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<SessionHandle, SessionOpenError> {
        let run_path = path.as_ref();
        let opened = SqliteSession::open(&run_path.join("state.sqlite3"), &self.core.kernel)?;
        let objects = ObjectStore::open(&run_path.join("objects"))?;
        let opened = catch_unwind(AssertUnwindSafe(|| {
            SqliteSession::verify_opened(opened, &self.core.kernel, &objects)
        }))
        .map_err(|panic| SessionOpenError::Panicked(panic_message(panic)))??;
        self.open_sqlite(opened, objects)
    }

    /// Restores validated canonical activation records into a new session.
    ///
    /// Package payload bytes are borrowed as external evidence keyed by their
    /// accepted content digests. The opened session retains referenced evidence
    /// in its in-memory object pool.
    ///
    /// `StateParts` is a graph-fact export. This method does not restore explicit
    /// artifact dependencies or their bytes; use the original persistent run
    /// for complete session restoration. Artifact files and collections can be
    /// exported or transferred separately through [`ContentStore`].
    ///
    /// # Errors
    ///
    /// Returns an error when restoration rejects the records (`Restore`),
    /// trusted contract code panics (`Panicked`), the in-memory stores cannot
    /// be initialized (`Storage`), shutdown has begun, or identity is
    /// exhausted.
    pub fn restore(
        &self,
        parts: StateParts,
        payload_evidence: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<SessionHandle, SessionOpenError> {
        let state = catch_unwind(AssertUnwindSafe(|| {
            self.core.kernel.restore_state(parts, payload_evidence)
        }))
        .map_err(|panic| SessionOpenError::Panicked(panic_message(panic)))??;
        let retained = retained_objects(&state, payload_evidence);
        let opened = SqliteSession::restore_in_memory(&self.core.kernel, &state)?;
        let objects = ObjectStore::memory(retained)?;
        self.open_sqlite(opened, objects)
    }

    /// Stops accepting sessions and closes proposal admission for every tracked
    /// session.
    ///
    /// Shutdown is terminal and idempotent for this runtime and its clones.
    /// Existing session handles retain read-only snapshot and frontier access.
    pub async fn shutdown(&self) {
        let sessions = self.core.begin_shutdown();
        let closes = sessions
            .into_iter()
            .map(|session| tokio::spawn(async move { session.close().await }))
            .collect::<Vec<_>>();
        for close in closes {
            let _ = close.await;
        }
    }

    fn open_sqlite(
        &self,
        mut opened: OpenedSqliteSession,
        objects: ObjectStore,
    ) -> Result<SessionHandle, SessionOpenError> {
        if opened.status == SessionStatus::Faulted {
            opened
                .session
                .recover_fault(&opened.current_kernel, &objects)?;
            opened.status = SessionStatus::Open;
            opened.fault = None;
        } else {
            opened.session.reconcile_objects(&objects)?;
        }
        let OpenedSqliteSession {
            session: sqlite,
            current_kernel,
            status: initial_status,
            revision,
            fault,
        } = opened;
        let (status, _) = watch::channel(initial_status);
        let (frontier, _) = watch::channel(revision);
        let package_limits = self
            .core
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .package_limits;
        let session = Arc::new(SessionCore {
            policy: Arc::clone(&self.core.policy),
            package_limits,
            inner: AsyncMutex::new(SessionState {
                kernel: current_kernel,
                status: initial_status,
                facts: sqlite,
                objects,
                revision,
                fault,
                readable: true,
            }),
            status,
            frontier,
        });
        let registration = self.core.register_session(&session)?;
        Ok(SessionHandle::new(session, registration))
    }
}

fn create_run_directory(path: &Path) -> io::Result<()> {
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(path)?;
    #[cfg(unix)]
    if let Err(error) = std::fs::File::open(path.parent().unwrap_or(path))
        .and_then(|directory| directory.sync_all())
    {
        let _ = std::fs::remove_dir(path);
        return Err(error);
    }
    Ok(())
}

fn retained_objects(
    state: &State,
    payload_evidence: &BTreeMap<ContentDigest, Payload>,
) -> BTreeMap<ContentDigest, Payload> {
    let mut retained = state
        .packages()
        .values()
        .map(|package| {
            let digest = package.content_digest();
            (
                digest,
                payload_evidence
                    .get(&digest)
                    .expect("restored package has validated payload evidence")
                    .clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for activation in state.activations().values() {
        let result = activation.result().clone();
        retained.insert(ContentDigest::compute(&result), result);
    }
    retained
}

fn publish_revision(inner: &mut SessionState, frontier: &watch::Sender<u64>, revision: u64) {
    inner.revision = revision;
    frontier.send_replace(revision);
}

fn fault_message(inner: &SessionState) -> Text {
    inner
        .fault
        .clone()
        .unwrap_or_else(|| Arc::from("session faulted"))
}

fn require_readable(inner: &SessionState) -> Result<(), SessionError> {
    if !inner.readable {
        return Err(SessionError::Faulted(fault_message(inner)));
    }
    Ok(())
}

fn require_open(inner: &SessionState) -> Result<(), SessionError> {
    match inner.status {
        SessionStatus::Open => Ok(()),
        SessionStatus::Closed => Err(SessionError::Closed),
        SessionStatus::Faulted => Err(SessionError::Faulted(fault_message(inner))),
    }
}

fn require_node(kernel: &Kernel, node_id: &str) -> Result<(), SessionError> {
    if kernel.graph().node(node_id).is_none() {
        return Err(SessionError::UnknownNode(Arc::from(node_id)));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ontography_calculus::{
        Authority, AuthorityTag, Contract, ContractViolation, DefinitionId, Edge, EdgeDefinition,
        Emission, Graph, Node, NodeDefinition, OutputAuthority, RootRule, Schema,
    };

    fn payload(value: &[u8]) -> Arc<[u8]> {
        Arc::from(value)
    }

    fn test_kernel(panic_on_result: bool) -> Arc<Kernel> {
        test_kernel_with_edge(panic_on_result, "source.sink")
    }

    /// The test kernel with its one edge named `edge_id`.
    fn test_kernel_with_edge(panic_on_result: bool, edge_id: &str) -> Arc<Kernel> {
        let tag = AuthorityTag::new("source.sink").expect("authority tag");
        let schema =
            Schema::new(["Source", "Sink"], ["Message", "Result"], [tag.clone()]).expect("schema");
        let graph = Graph::new(
            [
                Node::new("source").expect("source"),
                Node::new("sink").expect("sink"),
            ],
            [Edge::new(edge_id, "source", "sink").expect("edge")],
        )
        .expect("graph");
        let input = Contract::new("message", "Message", move |body| {
            assert!(
                !panic_on_result || body != b"panic",
                "message validator panic"
            );
            Ok::<(), ContractViolation>(())
        })
        .expect("input contract");
        let result = Contract::new("result", "Result", move |body| {
            assert!(
                !panic_on_result || body != b"panic",
                "result validator panic"
            );
            Ok::<(), ContractViolation>(())
        })
        .expect("result contract");
        let definitions = [
            NodeDefinition::new("source", ["Source"], "result").expect("source definition"),
            NodeDefinition::new("sink", ["Sink"], "result").expect("sink definition"),
        ];
        let edge_definitions = [EdgeDefinition::new(
            edge_id,
            ["Delivery"],
            ["Source"],
            ["Sink"],
            "message",
            [tag.clone()],
        )
        .expect("edge definition")];
        let authority = Authority::new([tag]);
        Arc::new(
            Kernel::admit(
                DefinitionId::new("proposal-session-test").expect("definition ID"),
                schema,
                graph,
                [input, result],
                definitions,
                edge_definitions,
                [],
                [RootRule::new("source", authority).expect("root rule")],
            )
            .expect("kernel"),
        )
    }

    fn root(kernel: &Kernel, result: &[u8], message: Option<&[u8]>) -> ActivationProposal {
        let authority = kernel.root_ceiling("source").expect("source root").clone();
        let mut proposal = ActivationProposal::root("source", authority, payload(result));
        if let Some(message) = message {
            proposal.emit(Emission::new(
                "source.sink",
                OutputAuthority::Carry,
                payload(message),
            ));
        }
        proposal
    }

    #[tokio::test]
    async fn concurrent_roots_are_serialized_and_both_remain_legal() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");

        let left = {
            let session = session.clone();
            let proposal = root(&kernel, b"left", None);
            tokio::spawn(async move { session.submit(proposal).await })
        };
        let right = {
            let session = session.clone();
            let proposal = root(&kernel, b"right", None);
            tokio::spawn(async move { session.submit(proposal).await })
        };

        assert!(matches!(
            left.await.expect("left task").expect("left decision"),
            ProposalDecision::Committed(_)
        ));
        assert!(matches!(
            right.await.expect("right task").expect("right decision"),
            ProposalDecision::Committed(_)
        ));
        assert_eq!(session.snapshot().await.state().activations().len(), 2);
    }

    #[tokio::test]
    async fn conflicting_package_proposals_receive_exact_kernel_decisions() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        session
            .submit(root(&kernel, b"root", Some(b"message")))
            .await
            .expect("root submission");
        let package_id = session
            .pending_page(None, usize::MAX)
            .await
            .expect("pending")
            .packages()[0]
            .0;

        let left = {
            let session = session.clone();
            tokio::spawn(async move {
                session
                    .submit(ActivationProposal::package(package_id, payload(b"left")))
                    .await
            })
        };
        let right = {
            let session = session.clone();
            tokio::spawn(async move {
                session
                    .submit(ActivationProposal::package(package_id, payload(b"right")))
                    .await
            })
        };
        let decisions = [
            left.await.expect("left task").expect("left decision"),
            right.await.expect("right task").expect("right decision"),
        ];
        assert_eq!(
            decisions
                .iter()
                .filter(|decision| matches!(decision, ProposalDecision::Committed(_)))
                .count(),
            1
        );
        assert_eq!(
            decisions
                .iter()
                .filter(|decision| matches!(
                    decision,
                    ProposalDecision::Rejected(Reject::AlreadyActivated { .. })
                ))
                .count(),
            1
        );
        assert_eq!(session.status(), SessionStatus::Open);
    }

    #[tokio::test]
    async fn close_preserves_read_only_state_and_fences_later_submissions() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        session
            .submit(root(&kernel, b"root", Some(b"message")))
            .await
            .expect("root submission");
        let before = session.snapshot().await;

        session.close().await;
        assert_eq!(session.status(), SessionStatus::Closed);
        assert_eq!(
            session.submit(root(&kernel, b"later", None)).await,
            Err(SessionError::Closed)
        );
        let after = session.snapshot().await;
        assert_eq!(after.state(), before.state());
        assert_eq!(
            session
                .pending_at("sink")
                .await
                .expect("pending after close")
                .packages()
                .len(),
            1
        );
    }

    #[tokio::test]
    async fn frontier_notifications_are_coalesced_and_restored_state_is_replayable() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        let mut frontier = session.frontier();
        assert_eq!(frontier.revision(), 0);

        session
            .submit(root(&kernel, b"one", Some(b"one")))
            .await
            .expect("first root");
        session
            .submit(root(&kernel, b"two", Some(b"two")))
            .await
            .expect("second root");
        assert!(frontier.changed().await >= 1);
        let pending = session.pending_at("sink").await.expect("pending");
        assert_eq!(pending.packages().len(), 2);
        assert_eq!(pending.revision(), session.frontier().revision());

        let restored = ProposalRuntime::new(Arc::clone(&kernel))
            .restore(
                session
                    .snapshot()
                    .await
                    .state()
                    .to_parts()
                    .expect("fixed-graph history"),
                &BTreeMap::from([
                    (ContentDigest::compute(b"one"), payload(b"one")),
                    (ContentDigest::compute(b"two"), payload(b"two")),
                ]),
            )
            .expect("restored session");
        assert!(restored.frontier().revision() > 0);
        assert_eq!(
            restored
                .pending_at("sink")
                .await
                .expect("restored pending")
                .packages()
                .len(),
            2
        );
    }

    /// A contract validator panics during evaluation. The rule this pins: a
    /// panic in trusted code before any write is a typed error, not a session
    /// fault, and not a kernel rejection. The transaction is discarded, the
    /// session stays open, and a later valid proposal is accepted. Only a
    /// storage error or panic after a write has begun faults the session.
    #[tokio::test]
    async fn contract_panic_is_a_typed_error_that_leaves_the_session_open() {
        let kernel = test_kernel(true);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");

        assert!(matches!(
            session.submit(root(&kernel, b"panic", None)).await,
            Err(SessionError::Panicked(message)) if message.contains("result validator panic")
        ));
        assert_eq!(session.status(), SessionStatus::Open);
        let snapshot = session.try_snapshot().await.expect("session is readable");
        assert!(snapshot.state().activations().is_empty());
        assert_eq!(snapshot.revision(), 0);
        assert!(session.kernel().await.is_ok());
        assert!(matches!(
            session.submit(root(&kernel, b"valid", None)).await,
            Ok(ProposalDecision::Committed(_))
        ));
        assert_eq!(session.snapshot().await.revision(), 1);
        session.close().await;
        assert_eq!(session.status(), SessionStatus::Closed);
    }

    #[tokio::test]
    async fn runtime_shutdown_closes_admission_and_preserves_queries() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        session
            .submit(root(&kernel, b"root", Some(b"message")))
            .await
            .expect("root");

        runtime.shutdown().await;

        assert_eq!(session.status(), SessionStatus::Closed);
        assert_eq!(session.snapshot().await.state().activations().len(), 1);
        assert_eq!(
            session
                .pending_page(None, usize::MAX)
                .await
                .expect("pending after shutdown")
                .packages()
                .len(),
            1
        );
        assert_eq!(
            session.submit(root(&kernel, b"later", None)).await,
            Err(SessionError::Closed)
        );
        assert_eq!(
            runtime.open().expect_err("shutdown is terminal"),
            SessionOpenError::ShuttingDown
        );
    }

    #[tokio::test]
    async fn custody_revocation_fences_a_proposal_waiting_for_linearization() {
        let kernel = test_kernel(false);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        let custody = Arc::new(SubmissionCustody::new());
        let state_guard = session.core.inner.lock().await;
        let submission = {
            let session = session.clone();
            let custody = Arc::clone(&custody);
            let proposal = root(&kernel, b"waiting", None);
            tokio::spawn(async move {
                session
                    .submit_custodied(proposal, Vec::new(), &custody)
                    .await
            })
        };
        tokio::task::yield_now().await;

        custody.revoke();
        drop(state_guard);

        assert_eq!(
            submission.await.expect("submission task"),
            Err(SessionError::Revoked)
        );
        assert!(session.snapshot().await.state().activations().is_empty());
    }

    /// The same rule as for submission, on the transfer path: the kernel
    /// catches the validator's panic itself and reports it as its own typed
    /// rejection, so the session returns it as the inner `Err` and stays open.
    #[tokio::test]
    async fn validator_panic_during_transfer_is_the_kernels_typed_rejection() {
        let kernel = test_kernel(true);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");
        let mut proposal = root(&kernel, b"result", None);
        proposal.emit(Emission::outbound(
            "Message",
            OutputAuthority::Carry,
            payload(b"panic"),
        ));
        let ProposalDecision::Committed(activation) =
            session.submit(proposal).await.expect("root submission")
        else {
            panic!("outbound root is legal");
        };
        let package = PackageId::from_parts(activation, 0);

        assert!(matches!(
            session.transfer(package, "source.sink").await,
            Ok(Err(TransferError::Admission(
                RewriteError::ValidatorPanicked(_)
            )))
        ));
        assert_eq!(session.status(), SessionStatus::Open);
        let snapshot = session.snapshot().await;
        assert_eq!(snapshot.revision(), 1);
        assert!(
            snapshot
                .state()
                .package(package)
                .unwrap()
                .delivery()
                .is_none()
        );
    }

    fn persistent_kernel() -> Arc<Kernel> {
        test_kernel(false)
    }

    fn with_detached_connection(run: &Path, sql: &str) {
        rusqlite::Connection::open(run.join("state.sqlite3"))
            .expect("detached connection")
            .execute_batch(sql)
            .expect("detached statement");
    }

    /// A storage error after the write began faults the session. When the
    /// durable fault marker itself cannot be written, the retained message
    /// says so instead of silently leaving the store unmarked.
    #[tokio::test]
    async fn fault_reports_a_failed_durable_marker() {
        let directory = tempfile::tempdir().expect("temporary directory");
        let run = directory.path().join("run");
        let kernel = persistent_kernel();
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        drop(runtime.create_persistent(&run).expect("persistent session"));
        drop(runtime);
        with_detached_connection(
            &run,
            "CREATE TRIGGER fail_revision BEFORE UPDATE OF state_revision ON session_meta
             BEGIN SELECT RAISE(FAIL, 'injected revision failure'); END;
             CREATE TRIGGER fail_marker BEFORE UPDATE OF fault ON session_meta
             BEGIN SELECT RAISE(FAIL, 'injected marker failure'); END;",
        );

        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open_persistent(&run).expect("reopened session");
        let Err(SessionError::Faulted(message)) = session.submit(root(&kernel, b"one", None)).await
        else {
            panic!("the injected revision failure must fault the session");
        };
        assert!(message.contains("injected revision failure"), "{message}");
        assert!(
            message.contains("the durable fault marker could not be written"),
            "{message}"
        );
        assert!(message.contains("injected marker failure"), "{message}");
        assert_eq!(session.status(), SessionStatus::Faulted);
        assert!(matches!(
            session.try_snapshot().await,
            Err(SessionError::Faulted(retained)) if retained == message
        ));
        drop(session);
        drop(runtime);
        with_detached_connection(
            &run,
            "DROP TRIGGER fail_revision; DROP TRIGGER fail_marker;",
        );
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open_persistent(&run).expect("recovered session");
        assert_eq!(session.status(), SessionStatus::Open);
        assert_eq!(
            session
                .content(ContentDigest::compute(b"one"))
                .await
                .expect("orphan lookup"),
            None
        );
        assert!(matches!(
            session.submit(root(&kernel, b"retry", None)).await,
            Ok(ProposalDecision::Committed(_))
        ));
    }

    /// The context store's version is checked on every open, independently of
    /// the graph store's, by both the session and the read-only inspectors.
    #[tokio::test]
    async fn context_schema_version_is_checked_independently_of_the_graph_store() {
        let directory = tempfile::tempdir().expect("temporary directory");
        let run = directory.path().join("run");
        let kernel = persistent_kernel();
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        drop(runtime.create_persistent(&run).expect("persistent session"));
        drop(runtime);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        for version in [1, 99] {
            with_detached_connection(
                &run,
                &format!("UPDATE context_meta SET schema_version = {version};"),
            );
            let expected = format!("unsupported context schema version {version}");
            assert!(matches!(
                runtime.open_persistent(&run),
                Err(SessionOpenError::Storage(message)) if message.contains(&expected)
            ));
            assert!(matches!(
                crate::context::read_invocations(&run, None, None, 10),
                Err(crate::context::ContextError::Storage(message))
                    if message.contains(&expected)
            ));
        }

        with_detached_connection(
            &run,
            &format!(
                "UPDATE context_meta SET schema_version = {};",
                crate::sqlite::context::CONTEXT_SCHEMA_VERSION
            ),
        );
        assert!(
            crate::context::read_invocations(&run, None, None, 10)
                .expect("inspection at the compiled context version")
                .is_empty()
        );
        let session = runtime.open_persistent(&run).expect("reopened session");
        assert_eq!(session.status(), SessionStatus::Open);
    }

    /// Payload evidence the store cannot supply for a package it has a row
    /// for is an integrity failure of the store: the transfer and the rewrite
    /// preparation that must read it report `Storage`, never the kernel's
    /// `EvidenceUnavailable`, nothing is written, and the session stays open.
    #[tokio::test]
    async fn corrupt_payload_evidence_is_a_storage_error_that_leaves_the_session_open() {
        use std::collections::BTreeSet;
        use std::io::Write as _;

        use iroh_blobs::Hash;
        use ontography_calculus::{GraphEdit, GraphFragment, PermitAll, Principal, RewriteRequest};

        let directory = tempfile::tempdir().expect("temporary directory");
        let run = directory.path().join("run");
        let kernel = persistent_kernel();
        let replacement = test_kernel_with_edge(false, "source.sink2");
        let request = RewriteRequest::new(
            Principal::new("test"),
            GraphEdit::new(
                BTreeSet::new(),
                BTreeSet::from([Arc::from("source.sink")]),
                GraphFragment::new(
                    vec![],
                    replacement.graph().edges().to_vec(),
                    vec![],
                    replacement.edge_definitions().to_vec(),
                    vec![],
                    vec![],
                ),
            ),
        );
        // Larger than the store's inline threshold, so the bytes live in
        // their own data file.
        let message: Payload = Arc::from(vec![0x4d; 200_000]);
        let runtime = ProposalRuntime::with_policy(Arc::clone(&kernel), Arc::new(PermitAll));
        let session = runtime.create_persistent(&run).expect("persistent session");
        let mut proposal = root(&kernel, b"result", None);
        proposal.emit(Emission::outbound(
            "Message",
            OutputAuthority::Carry,
            Arc::clone(&message),
        ));
        let ProposalDecision::Committed(activation) =
            session.submit(proposal).await.expect("root submission")
        else {
            panic!("outbound root is legal");
        };
        let package = PackageId::from_parts(activation, 0);
        drop(session);
        drop(runtime);
        let data = run
            .join("objects")
            .join("data")
            .join(format!("{}.data", Hash::new(&message).to_hex()));
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .open(&data)
            .expect("payload data file");
        file.write_all(b"corruption").expect("corrupt the payload");
        file.sync_all().expect("sync the corruption");

        let runtime = ProposalRuntime::with_policy(Arc::clone(&kernel), Arc::new(PermitAll));
        let session = runtime.open_persistent(&run).expect("reopened session");
        assert!(matches!(
            session.transfer(package, "source.sink").await,
            Err(SessionError::Storage(message)) if message.contains("does not match its digest")
        ));
        assert_eq!(session.status(), SessionStatus::Open);
        assert!(matches!(
            session.prepare_rewrite(&request).await,
            Err(SessionError::Storage(message)) if message.contains("does not match its digest")
        ));
        assert_eq!(session.status(), SessionStatus::Open);
        let snapshot = session.try_snapshot().await.expect("session is readable");
        assert_eq!(snapshot.revision(), 1);
        assert!(
            snapshot
                .state()
                .package(package)
                .expect("package row")
                .delivery()
                .is_none()
        );
        assert!(matches!(
            session.submit(root(&kernel, b"later", None)).await,
            Ok(ProposalDecision::Committed(_))
        ));
    }

    /// The invocation context store follows the session's fault rule: a
    /// refusal before any write leaves the session open, and a write that
    /// fails once begun faults it durably.
    #[tokio::test]
    async fn context_store_writes_follow_the_fault_rule() {
        use crate::context::{ContextError, ContextPolicy, InvocationTrigger};

        let directory = tempfile::tempdir().expect("temporary directory");
        let run = directory.path().join("run");
        let kernel = persistent_kernel();
        let trigger = || InvocationTrigger::Root {
            authority: kernel.root_ceiling("source").expect("source root").clone(),
            input: payload(b"input"),
        };
        let policy = ContextPolicy {
            max_events: 1,
            ..ContextPolicy::default()
        };
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.create_persistent(&run).expect("persistent session");
        let invocation = session
            .begin_invocation("source", trigger(), policy.clone())
            .await
            .expect("invocation");
        invocation
            .record_tool_response("tool", payload(b"one"))
            .await
            .expect("first receipt");
        assert!(matches!(
            invocation
                .record_tool_response("tool", payload(b"two"))
                .await,
            Err(ContextError::Budget(_))
        ));
        assert_eq!(session.status(), SessionStatus::Open);
        drop(invocation);
        drop(session);
        drop(runtime);
        with_detached_connection(
            &run,
            "CREATE TRIGGER fail_event BEFORE INSERT ON context_events
             BEGIN SELECT RAISE(FAIL, 'injected event failure'); END;",
        );

        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open_persistent(&run).expect("reopened session");
        let invocation = session
            .begin_invocation("source", trigger(), policy)
            .await
            .expect("invocation");
        let Err(ContextError::Storage(message)) = invocation
            .record_tool_response("tool", payload(b"three"))
            .await
        else {
            panic!("the injected event failure must fault the session");
        };
        assert!(message.contains("injected event failure"), "{message}");
        assert_eq!(session.status(), SessionStatus::Faulted);
        assert!(matches!(
            session.try_snapshot().await,
            Err(SessionError::Faulted(retained)) if retained.contains("injected event failure")
        ));
    }
}
