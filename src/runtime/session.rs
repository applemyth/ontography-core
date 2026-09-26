//! Minimal serialized hosting for canonical kernel proposals.
//!
//! This module knows nothing about executable node kinds, retries, or
//! supervision. It owns the current graph and logical state and exposes bounded
//! trigger observations from admitted ingress metadata. Mutations commit and
//! publish under one lock, without an intervening cancellation boundary.

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

use super::object_store::ObjectStore;
use super::sqlite::{OpenedSqliteSession, SqlitePreparedRewrite, SqliteSession};
use crate::content::{ContentId, ContentReader, ContentStore};
use crate::{
    ActivationId, ActivationProposal, ContentDigest, Delivery, ExtensionError, Kernel, Package,
    PackageId, Payload, Phase, Reject, RetireError, Retirement, RetirementReason, RewriteError,
    RewriteGrammar, RewriteRequest, State, StateParts, StateRestoreError, TransferError,
};

type Text = Arc<str>;

/// Result of asking the kernel to consider one proposal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProposalDecision {
    /// The kernel atomically committed the proposal.
    Committed(ActivationId),
    /// The kernel rejected the proposal and left accepted state unchanged.
    Rejected(Reject),
}

/// Operational failure before a proposal received a kernel decision.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum SubmitError {
    /// Proposal admission has been explicitly closed.
    #[error("proposal session is closed")]
    Closed,
    /// An explicit artifact dependency is missing, incomplete, or corrupt.
    #[error("proposal content is unavailable: {0}")]
    Content(Text),
    /// Storage or trusted code failed while considering a proposal.
    #[error("proposal session faulted: {0}")]
    Faulted(Text),
    /// The execution that owned this proposal path has terminated.
    #[error("execution proposal custody is revoked")]
    Revoked,
}

/// Failure while preparing or committing a graph rewrite or package transfer.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum SessionTransitionError {
    /// The session no longer accepts mutations.
    #[error("proposal session is closed")]
    Closed,
    /// Storage or trusted code failed; reopen before observing current state.
    #[error("proposal session faulted: {0}")]
    Faulted(Text),
    /// A prepared rewrite belongs to another session.
    #[error("prepared rewrite belongs to another session")]
    ForeignSession,
    /// State changed after the rewrite and its retirement report were prepared.
    #[error("prepared rewrite is stale")]
    Stale,
    /// The kernel rejected the rewrite without mutation.
    #[error(transparent)]
    Rewrite(#[from] RewriteError),
    /// The kernel rejected the transfer without mutation.
    #[error(transparent)]
    Transfer(#[from] TransferError),
    /// The kernel rejected the retirement without mutation.
    #[error(transparent)]
    Retire(#[from] RetireError),
    /// The kernel rejected the vocabulary extension without mutation.
    #[error(transparent)]
    Extension(#[from] ExtensionError),
    /// Preparation could not read its required state or evidence.
    #[error("transition preparation storage failed: {0}")]
    Storage(Text),
    /// Trusted preparation code panicked without installing state.
    #[error("transition preparation failed: {0}")]
    EvaluationFault(Text),
}

/// An admitted rewrite and retirement report bound to one session state.
pub struct SessionRewrite {
    owner: Weak<SessionCore>,
    prepared: SqlitePreparedRewrite,
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
    pub fn next_kernel(&self) -> &Arc<Kernel> {
        self.prepared.next_kernel()
    }

    /// Returns every package this rewrite would retire and its reason.
    #[must_use]
    pub fn retirements(&self) -> &BTreeMap<PackageId, RetirementReason> {
        self.prepared.retirements()
    }

    /// Returns the predecessor revision used to prepare this report.
    #[must_use]
    pub fn revision(&self) -> u64 {
        self.prepared.revision()
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
    /// Trusted kernel or contract code panicked during restoration.
    #[error("proposal session restoration faulted: {0}")]
    RestoreFault(Text),
    /// Session storage could not be created or opened.
    #[error("could not open proposal session storage: {0}")]
    Storage(Text),
}

impl From<StateRestoreError> for SessionOpenError {
    fn from(error: StateRestoreError) -> Self {
        Self::Restore(Box::new(error))
    }
}

/// Failure of a read-only session query.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum SessionError {
    /// The session faulted and must be reopened before reading current state.
    #[error("proposal session faulted; reopen before reading current state: {0}")]
    Faulted(Text),
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
    /// Session storage could not be read.
    #[error("proposal session storage read failed: {0}")]
    Storage(Text),
    /// Trusted code panicked while checking a materialized view.
    #[error("proposal session validation faulted: {0}")]
    ValidationFault(Text),
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
    packages: Vec<(PackageId, Package)>,
}

/// One retained package and the causal inputs of its producing activation.
///
/// This metadata query reads no payloads or activation results. Consumed and
/// retired packages remain available; current custody is not represented here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageHistory {
    package: Package,
    inputs: Vec<PackageId>,
}

impl PackageHistory {
    pub(crate) fn new(package: Package, inputs: Vec<PackageId>) -> Self {
        Self { package, inputs }
    }

    /// Returns the retained package metadata, including its immutable digest.
    #[must_use]
    pub const fn package(&self) -> &Package {
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
    pub fn packages(&self) -> &[(PackageId, Package)] {
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
    received: Vec<(PackageId, Package)>,
    outbound: Vec<(PackageId, Package)>,
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
    pub fn received(&self) -> &[(PackageId, Package)] {
        &self.received
    }

    /// Returns the first bounded page of outbound packages in identity order.
    #[must_use]
    pub fn outbound(&self) -> &[(PackageId, Package)] {
        &self.outbound
    }
}

/// Coalesced notification that the graph or package frontier changed.
///
/// Revisions are hints rather than package custody. After observing a revision,
/// query [`SessionHandle::pending`] or [`SessionHandle::pending_at`] for current
/// truth. A new subscription immediately exposes the current revision, so a
/// relaunched consumer can recover pending work without replaying notifications.
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
    grammar: Arc<RewriteGrammar>,
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
        let storage = |error: super::sqlite::SqliteStateError| {
            SessionError::Storage(Arc::from(error.to_string()))
        };
        let counts = inner.facts.frontier_counts().map_err(storage)?;
        let received = inner
            .facts
            .pending(&inner.kernel, None, None, limit)
            .map_err(storage)?;
        let outbound = inner
            .facts
            .outbound(&inner.kernel, None, None, limit)
            .map_err(storage)?;
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
    async fn submit(
        &self,
        proposal: ActivationProposal,
        custody: Option<&SubmissionCustody>,
    ) -> Result<ProposalDecision, SubmitError> {
        self.submit_with_content(proposal, Vec::new(), custody)
            .await
    }

    async fn submit_with_content(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
        custody: Option<&SubmissionCustody>,
    ) -> Result<ProposalDecision, SubmitError> {
        let mut inner = self.inner.lock().await;
        if custody.is_some_and(SubmissionCustody::is_revoked) {
            return Err(SubmitError::Revoked);
        }
        match inner.status {
            SessionStatus::Closed => return Err(SubmitError::Closed),
            SessionStatus::Faulted => return Err(SubmitError::Faulted(fault_message(&inner))),
            SessionStatus::Open => {}
        }
        // User work runs outside this lock. Once admitted here, a transition is
        // committed and published without an await or cancellation boundary.
        let result = catch_unwind(AssertUnwindSafe(|| {
            let kernel = Arc::clone(&inner.kernel);
            let SessionState { facts, objects, .. } = &mut *inner;
            facts.submit_with_content(&kernel, objects, proposal, &contents)
        }));
        match result {
            Ok(Ok(Ok(commit))) => {
                publish_revision(&mut inner, &self.frontier, commit.revision);
                Ok(ProposalDecision::Committed(commit.activation_id))
            }
            Ok(Ok(Err(reject))) => Ok(ProposalDecision::Rejected(reject)),
            Ok(Err(super::sqlite::SqliteStateError::Content(error))) => {
                Err(SubmitError::Content(Arc::from(error.to_string())))
            }
            Ok(Err(error)) => Err(SubmitError::Faulted(
                self.fault(&mut inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SubmitError::Faulted(
                self.fault(&mut inner, panic_message(panic)),
            )),
        }
    }

    async fn prepare_rewrite(
        &self,
        request: &RewriteRequest,
    ) -> Result<SqlitePreparedRewrite, SessionTransitionError> {
        let inner = self.inner.lock().await;
        require_open(&inner)?;
        catch_unwind(AssertUnwindSafe(|| {
            inner
                .facts
                .prepare_rewrite(&inner.kernel, &inner.objects, &self.grammar, request)
        }))
        .map_err(|panic| SessionTransitionError::EvaluationFault(panic_message(panic)))?
        .map_err(|error| SessionTransitionError::Storage(Arc::from(error.to_string())))?
        .map_err(SessionTransitionError::Rewrite)
    }

    async fn commit_rewrite(
        &self,
        prepared: SqlitePreparedRewrite,
    ) -> Result<RewriteOutcome, SessionTransitionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let retirements = prepared.retirements().clone();
        let kernel = Arc::clone(&inner.kernel);
        let committed = catch_unwind(AssertUnwindSafe(|| {
            inner.facts.commit_rewrite(&kernel, prepared)
        }));
        match committed {
            Ok(Ok(Some(commit))) => {
                inner.kernel = commit.current_kernel;
                publish_revision(&mut inner, &self.frontier, commit.revision);
                Ok(RewriteOutcome {
                    revision: commit.revision,
                    retirements,
                })
            }
            Ok(Ok(None)) => Err(SessionTransitionError::Stale),
            Ok(Err(error)) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, panic_message(panic)),
            )),
        }
    }

    async fn transfer(
        &self,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Delivery, SessionTransitionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let result = catch_unwind(AssertUnwindSafe(|| {
            let kernel = Arc::clone(&inner.kernel);
            let SessionState { facts, objects, .. } = &mut *inner;
            facts.transfer(&kernel, objects, package_id, edge_id)
        }));
        match result {
            Ok(Ok(Ok(commit))) => {
                publish_revision(&mut inner, &self.frontier, commit.revision);
                Ok(commit.delivery)
            }
            Ok(Ok(Err(reject))) => Err(SessionTransitionError::Transfer(reject)),
            Ok(Err(error)) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, panic_message(panic)),
            )),
        }
    }

    async fn retire(
        &self,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Retirement, SessionTransitionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let result = catch_unwind(AssertUnwindSafe(|| {
            let kernel = Arc::clone(&inner.kernel);
            inner.facts.retire(&kernel, package_id, evidence)
        }));
        match result {
            Ok(Ok(Ok(commit))) => {
                publish_revision(&mut inner, &self.frontier, commit.revision);
                Ok(commit.retirement)
            }
            Ok(Ok(Err(reject))) => Err(SessionTransitionError::Retire(reject)),
            Ok(Err(error)) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, panic_message(panic)),
            )),
        }
    }

    async fn extend(&self, next: Arc<Kernel>) -> Result<u64, SessionTransitionError> {
        let mut inner = self.inner.lock().await;
        require_open(&inner)?;
        let result = catch_unwind(AssertUnwindSafe(|| {
            let kernel = Arc::clone(&inner.kernel);
            inner.facts.extend(&kernel, &next)
        }));
        match result {
            Ok(Ok(Ok(revision))) => {
                inner.kernel = next;
                publish_revision(&mut inner, &self.frontier, revision);
                Ok(revision)
            }
            Ok(Ok(Err(reject))) => Err(SessionTransitionError::Extension(reject)),
            Ok(Err(error)) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, Arc::from(error.to_string())),
            )),
            Err(panic) => Err(SessionTransitionError::Faulted(
                self.fault(&mut inner, panic_message(panic)),
            )),
        }
    }

    fn fault(&self, inner: &mut SessionState, message: Text) -> Text {
        // A storage error can leave commit acknowledgment uncertain. Every
        // coherent read is fenced until reopening resolves the durable state.
        let _ = inner.facts.fault(&message);
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
        .map_err(|panic| SessionError::ValidationFault(panic_message(panic)))?
        .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))?;
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
            activation_content: inner
                .facts
                .all_activation_content()
                .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))?,
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
        let read = match phase {
            Phase::In => inner.facts.pending(&inner.kernel, node_id, after, limit),
            Phase::Out => inner.facts.outbound(&inner.kernel, node_id, after, limit),
        }
        .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))?;
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
            .next_trigger(
                &inner.kernel,
                node_id,
                definition.ingress_mode(),
                incoming_edges,
            )
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))?;
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
        let read = inner
            .facts
            .next_pending_on_edge(&inner.kernel, node_id, edge_id)
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))?;
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
        inner
            .facts
            .package_history(package_id)
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
    }

    async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        let inner = self.inner.lock().await;
        inner
            .objects
            .get(digest)
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
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
    /// Returns an error for a zero per-phase limit or unreadable persistent state.
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
    /// Requires reopening after a failure with uncertain commit publication.
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
    /// # Errors
    /// Rejects an absent node or a session whose state must be reloaded.
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
    /// # Errors
    /// Rejects inadmissible rewrites or unavailable state/evidence without mutation.
    pub async fn prepare_rewrite(
        &self,
        request: &RewriteRequest,
    ) -> Result<SessionRewrite, SessionTransitionError> {
        Ok(SessionRewrite {
            owner: Arc::downgrade(&self.core),
            prepared: self.core.prepare_rewrite(request).await?,
        })
    }

    /// Commits the prepared graph and frontier together if its state is current.
    ///
    /// # Errors
    /// Rejects foreign or stale plans. A failed durable commit faults admission
    /// and requires reopening before reading coherent current state.
    pub async fn commit_rewrite(
        &self,
        plan: SessionRewrite,
    ) -> Result<RewriteOutcome, SessionTransitionError> {
        if !Weak::ptr_eq(&plan.owner, &Arc::downgrade(&self.core)) {
            return Err(SessionTransitionError::ForeignSession);
        }
        self.core.commit_rewrite(plan.prepared).await
    }

    /// Delivers one live outbound package through a currently accepting edge.
    ///
    /// # Errors
    /// Returns the kernel's transfer rejection or a session/storage failure.
    pub async fn transfer(
        &self,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Delivery, SessionTransitionError> {
        self.core.transfer(package_id, edge_id).await
    }

    /// Retires one live package, citing an optional accepted activation as evidence.
    ///
    /// The package leaves the frontier and a canonical retirement record is
    /// stored; history, deliveries, and immutable package facts are unchanged.
    ///
    /// # Errors
    /// Returns the kernel's retirement rejection or a session/storage failure.
    pub async fn retire(
        &self,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Retirement, SessionTransitionError> {
        self.core.retire(package_id, evidence).await
    }

    /// Installs a monotone vocabulary extension of the current definition.
    ///
    /// `next` must keep the graph, annotations, and existing contracts
    /// unchanged and add schema vocabulary or contracts. The frontier is
    /// untouched. Reopening the session later requires supplying `next`.
    ///
    /// # Errors
    /// Returns the kernel's extension rejection or a session/storage failure.
    pub async fn extend(&self, next: Arc<Kernel>) -> Result<u64, SessionTransitionError> {
        self.core.extend(next).await
    }

    /// Submits one canonical root or package-triggered proposal.
    ///
    /// The outer result reports only operational failure;
    /// [`ProposalDecision::Rejected`] is the exact graph-admission decision from
    /// the kernel. Concurrent submissions are considered in state-lock order.
    ///
    /// # Errors
    ///
    /// Returns an operational error when admission is closed or faulted.
    pub async fn submit(
        &self,
        proposal: ActivationProposal,
    ) -> Result<ProposalDecision, SubmitError> {
        self.core.submit(proposal, None).await
    }

    /// Submits a proposal with explicit immutable artifact dependencies.
    ///
    /// The artifacts must already be complete in this session's content store.
    /// Accepted dependencies remain retained with activation history even after
    /// their caller-managed pins are released. Contracts still validate the
    /// proposal's exact bytes; declaring a dependency does not validate its
    /// application-specific meaning.
    /// # Errors
    /// Reports closed or faulted admission and unavailable artifact content.
    pub async fn submit_with_content(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, SubmitError> {
        self.core
            .submit_with_content(proposal, contents, None)
            .await
    }

    pub(super) async fn submit_with_custody(
        &self,
        proposal: ActivationProposal,
        custody: &SubmissionCustody,
    ) -> Result<ProposalDecision, SubmitError> {
        self.core.submit(proposal, Some(custody)).await
    }

    pub(super) async fn submit_content_with_custody(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
        custody: &SubmissionCustody,
    ) -> Result<ProposalDecision, SubmitError> {
        self.core
            .submit_with_content(proposal, contents, Some(custody))
            .await
    }

    /// Closes proposal admission while retaining read-only access to final state.
    ///
    /// Proposals linearized before this call receive kernel decisions. Open
    /// sessions transition to [`SessionStatus::Closed`], after which submissions
    /// receive [`SubmitError::Closed`]. Faulted sessions retain their more
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
    /// should use bounded frontier queries for routine execution.
    ///
    /// # Errors
    ///
    /// Returns an error when current state cannot be decoded or checked, or a
    /// live fault requires reopening. This does not replay historical rules.
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
    ///
    /// Returns an error when metadata is unreadable or a live storage fault
    /// requires reopening before coherent state can be observed.
    pub async fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SessionError> {
        self.core.package_history(package_id).await
    }

    /// Resolves exact bytes in this session's object pool by content digest.
    ///
    /// # Errors
    ///
    /// Returns an error when durable content is unreadable or fails its digest.
    pub async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        self.core.content(digest).await
    }

    /// Returns this session's cloneable blob, artifact, and transfer API.
    ///
    /// The returned handle owns its storage access. File work, streams, and
    /// transfers do not hold the session's graph-admission lock. Payloads and
    /// artifacts share the session's iroh store.
    /// # Errors
    /// Reports unreadable session state.
    pub async fn content_store(&self) -> Result<ContentStore, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        Ok(inner.objects.content_store())
    }

    /// Returns retained payload size without allocating the complete payload.
    ///
    /// This metadata is useful for allocation limits; it does not authenticate
    /// the bytes. Use a content read for integrity verification.
    /// # Errors
    /// Reports unreadable storage or inconsistent metadata.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        inner
            .objects
            .content_size(digest)
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
    }

    /// Reads exact offsets from a retained payload with integrity verification.
    ///
    /// Establishing the SHA-256 to BLAKE3 binding can require an incremental
    /// complete verification pass. Returned memory is bounded by the range.
    /// # Errors
    /// Reports invalid ranges, storage failures, or corrupt content.
    pub async fn content_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Payload>, SessionError> {
        self.content_store()
            .await?
            .read_digest_range(digest, range)
            .await
            .map(|content| content.map(|bytes| Payload::from(bytes.as_ref())))
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
    }

    /// Opens a verified, seekable payload reader without holding the session lock.
    /// # Errors
    /// Reports unreadable storage or corrupt content.
    pub async fn content_reader(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<ContentReader>, SessionError> {
        self.content_store()
            .await?
            .digest_reader(digest)
            .await
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
    }

    /// Returns the explicit artifact dependencies retained by an activation.
    ///
    /// Unknown activations and activations without dependencies return an empty
    /// list. This metadata does not read artifact payloads.
    /// # Errors
    /// Reports unreadable or inconsistent retained state.
    pub async fn activation_content(
        &self,
        activation_id: ActivationId,
    ) -> Result<Vec<ContentId>, SessionError> {
        let inner = self.core.inner.lock().await;
        require_readable(&inner)?;
        inner
            .facts
            .activation_content(activation_id)
            .map_err(|error| SessionError::Storage(Arc::from(error.to_string())))
    }

    /// Returns every currently pending package.
    ///
    /// This remains available after session close and proposal-runtime shutdown.
    ///
    /// # Panics
    ///
    /// Panics when storage cannot be read or a live fault requires reopening.
    /// Use [`Self::try_pending`] when that failure must be handled.
    pub async fn pending(&self) -> PendingFrontier {
        self.try_pending()
            .await
            .expect("session pending frontier storage remains readable")
    }

    /// Tries to return every currently pending package.
    ///
    /// Prefer [`Self::pending_page`] for a frontier that may be large.
    ///
    /// # Errors
    ///
    /// Returns a storage error for an unreadable persistent session.
    pub async fn try_pending(&self) -> Result<PendingFrontier, SessionError> {
        self.core.packages(Phase::In, None, None, usize::MAX).await
    }

    /// Returns one bounded page of currently pending packages.
    ///
    /// `after` is an exclusive canonical package-identity cursor. Pass the last
    /// package ID from one page to retrieve the next. If the returned revision
    /// changes between pages, restart pagination; packages use random
    /// identities and a concurrently inserted package may sort before a cursor.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero limit or unreadable persistent state.
    pub async fn pending_page(
        &self,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        self.core.packages(Phase::In, None, after, limit).await
    }

    /// Returns all packages awaiting transfer, together with the current graph.
    ///
    /// # Errors
    /// Returns a storage error or requires reopening after a failed commit.
    pub async fn outbound(&self) -> Result<PendingFrontier, SessionError> {
        self.outbound_page(None, None, usize::MAX).await
    }

    /// Reads a bounded page of outbound packages, optionally at one node.
    ///
    /// `after` is an exclusive identity cursor. Restart pagination if the
    /// returned revision changes between pages.
    /// # Errors
    /// Rejects an absent node, zero limit, or unavailable current state.
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
    ///
    /// Returns an error when `node_id` is absent from the kernel definition or
    /// persistent state cannot be read.
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
    ///
    /// Returns an error for an unknown node or unreadable persistent state.
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
    ///
    /// Returns an error for an unknown node, an unknown edge, an edge targeting
    /// another node, or unreadable persistent state.
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
    ///
    /// Returns an error for an unknown node, a zero limit, or unreadable
    /// persistent state.
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
}

struct ProposalRuntimeCore {
    kernel: Arc<Kernel>,
    grammar: Arc<RewriteGrammar>,
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

/// Independent host for sessions sharing an initial graph and rewrite grammar.
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
    /// Creates a runtime with an empty rewrite grammar.
    #[must_use]
    pub fn new(kernel: Arc<Kernel>) -> Self {
        Self::with_grammar(kernel, RewriteGrammar::default())
    }

    /// Creates a runtime with one immutable set of permitted rewrite productions.
    #[must_use]
    pub fn with_grammar(kernel: Arc<Kernel>, grammar: RewriteGrammar) -> Self {
        Self {
            core: Arc::new(ProposalRuntimeCore {
                kernel,
                grammar: Arc::new(grammar),
                next_session_id: AtomicU64::new(1),
                control: Mutex::new(ProposalRuntimeControl {
                    accepting: true,
                    sessions: BTreeMap::new(),
                }),
            }),
        }
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
        let opened = SqliteSession::create_in_memory(&self.core.kernel)
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
        let objects = ObjectStore::memory(BTreeMap::new())
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
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
            let objects = ObjectStore::create(&run_path.join("objects"))
                .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
            let opened = SqliteSession::create(&run_path.join("state.sqlite3"), &self.core.kernel)
                .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
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
    /// contracts or rewrites. Open sessions resume admission. Closed and faulted
    /// sessions retain their terminal lifecycle with coherent read access.
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
        let opened = SqliteSession::open(&run_path.join("state.sqlite3"), &self.core.kernel)
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
        let objects = ObjectStore::open(&run_path.join("objects"))
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
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
        let opened = SqliteSession::open(&run_path.join("state.sqlite3"), &self.core.kernel)
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
        let objects = ObjectStore::open(&run_path.join("objects"))
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
        let opened = catch_unwind(AssertUnwindSafe(|| {
            SqliteSession::verify_opened(opened, &self.core.kernel, &objects)
        }))
        .map_err(|panic| SessionOpenError::RestoreFault(panic_message(panic)))?
        .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
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
    /// Returns an error when restoration rejects the records, trusted contract
    /// code panics, shutdown has begun, or identity is exhausted.
    pub fn restore(
        &self,
        parts: StateParts,
        payload_evidence: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<SessionHandle, SessionOpenError> {
        let state = catch_unwind(AssertUnwindSafe(|| {
            self.core.kernel.restore_state(parts, payload_evidence)
        }))
        .map_err(|panic| SessionOpenError::RestoreFault(panic_message(panic)))??;
        let retained = retained_objects(&state, payload_evidence);
        let opened = SqliteSession::restore_in_memory(&self.core.kernel, &state)
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
        let objects = ObjectStore::memory(retained)
            .map_err(|error| SessionOpenError::Storage(Arc::from(error.to_string())))?;
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
        opened: OpenedSqliteSession,
        objects: ObjectStore,
    ) -> Result<SessionHandle, SessionOpenError> {
        let OpenedSqliteSession {
            session: sqlite,
            current_kernel,
            status: initial_status,
            revision,
            fault,
        } = opened;
        let (status, _) = watch::channel(initial_status);
        let (frontier, _) = watch::channel(revision);
        let session = Arc::new(SessionCore {
            grammar: Arc::clone(&self.core.grammar),
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

fn require_open(inner: &SessionState) -> Result<(), SessionTransitionError> {
    match inner.status {
        SessionStatus::Open => Ok(()),
        SessionStatus::Closed => Err(SessionTransitionError::Closed),
        SessionStatus::Faulted => Err(SessionTransitionError::Faulted(fault_message(inner))),
    }
}

fn require_node(kernel: &Kernel, node_id: &str) -> Result<(), SessionError> {
    if kernel.graph().node(node_id).is_none() {
        return Err(SessionError::UnknownNode(Arc::from(node_id)));
    }
    Ok(())
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> Text {
    if let Some(message) = panic.downcast_ref::<&str>() {
        return Arc::from(*message);
    }
    if let Some(message) = panic.downcast_ref::<String>() {
        return Arc::from(message.as_str());
    }
    Arc::from("trusted kernel callback panicked")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Authority, AuthorityTag, Contract, ContractViolation, DefinitionId, Edge, EdgeDefinition,
        Emission, Graph, Node, NodeDefinition, OutputAuthority, RootRule, Schema,
    };

    fn payload(value: &[u8]) -> Arc<[u8]> {
        Arc::from(value)
    }

    fn test_kernel(panic_on_result: bool) -> Arc<Kernel> {
        let tag = AuthorityTag::new("source.sink").expect("authority tag");
        let schema =
            Schema::new(["Source", "Sink"], ["Message", "Result"], [tag.clone()]).expect("schema");
        let graph = Graph::new(
            [
                Node::new("source").expect("source"),
                Node::new("sink").expect("sink"),
            ],
            [Edge::new("source.sink", "source", "sink").expect("edge")],
        )
        .expect("graph");
        let input = Contract::new("message", "Message", |_| Ok(())).expect("input contract");
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
            "source.sink",
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
        let package_id = session.pending().await.packages()[0].0;

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
            Err(SubmitError::Closed)
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

    #[tokio::test]
    async fn contract_panic_faults_session_without_becoming_kernel_rejection() {
        let kernel = test_kernel(true);
        let runtime = ProposalRuntime::new(Arc::clone(&kernel));
        let session = runtime.open().expect("session");

        assert!(matches!(
            session.submit(root(&kernel, b"panic", None)).await,
            Err(SubmitError::Faulted(message)) if message.contains("result validator panic")
        ));
        assert_eq!(session.status(), SessionStatus::Faulted);
        assert!(matches!(
            session.try_snapshot().await,
            Err(SessionError::Faulted(_))
        ));
        assert!(matches!(
            session.kernel().await,
            Err(SessionError::Faulted(_))
        ));
        assert!(matches!(
            session.try_pending().await,
            Err(SessionError::Faulted(_))
        ));
        assert!(matches!(
            session.submit(root(&kernel, b"valid", None)).await,
            Err(SubmitError::Faulted(_))
        ));
        session.close().await;
        assert_eq!(session.status(), SessionStatus::Faulted);
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
        assert_eq!(session.pending().await.packages().len(), 1);
        assert_eq!(
            session.submit(root(&kernel, b"later", None)).await,
            Err(SubmitError::Closed)
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
            tokio::spawn(async move { session.submit_with_custody(proposal, &custody).await })
        };
        tokio::task::yield_now().await;

        custody.revoke();
        drop(state_guard);

        assert_eq!(
            submission.await.expect("submission task"),
            Err(SubmitError::Revoked)
        );
        assert!(session.snapshot().await.state().activations().is_empty());
    }
}
