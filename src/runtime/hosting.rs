//! Opaque executable hosting over canonical proposal sessions.
//!
//! Every executable receives the same context. It may react to pending
//! packages, submit roots without a package trigger, remain live, submit any
//! number of proposals, or exit. The host supervises process mechanics only;
//! [`crate::Kernel`] remains the sole graph-legality authority.

use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::ops::Range;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, Weak};

use thiserror::Error;
use tokio::sync::{Notify, oneshot, watch};
use tokio::task::AbortHandle;

use super::activity::{ActivityReporter, ActivitySnapshot, ActivityTracker};
use super::session::{
    FrontierReceiver, PackageHistory, PendingFrontier, ProposalDecision, SessionError,
    SessionHandle, SessionStatus, SubmissionCustody, SubmitError,
};
use crate::{
    ActivationId, ActivationProposal, ContentDigest, ContentId, ContentReader, ContentStore,
    Kernel, PackageId, Payload,
};

type Text = Arc<str>;

/// Future returned by a dynamically dispatched executable definition.
pub type ExecutionFuture =
    Pin<Box<dyn Future<Output = Result<(), ExecutionFailure>> + Send + 'static>>;

/// One opaque executable definition attached to a graph node identity.
///
/// The runtime does not infer behavior or lifecycle from this trait. A
/// definition may submit no proposals or many, wait for frontier changes,
/// submit spontaneous roots, spawn its own internal work, or return.
pub trait ExecutableDefinition: Send + Sync + 'static {
    /// Launches one live executable instance.
    fn launch(&self, context: ExecutionContext) -> ExecutionFuture;
}

impl<F, Fut> ExecutableDefinition for F
where
    F: Fn(ExecutionContext) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Result<(), ExecutionFailure>> + Send + 'static,
{
    fn launch(&self, context: ExecutionContext) -> ExecutionFuture {
        Box::pin((self)(context))
    }
}

/// Stable host-local identity of one launched executable instance.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExecutionId(u64);

impl ExecutionId {
    /// Returns the host-local integer representation.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl fmt::Display for ExecutionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Stable failure returned deliberately by an opaque executable.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
#[error("{class}: {message}")]
pub struct ExecutionFailure {
    class: Text,
    message: Text,
}

impl ExecutionFailure {
    /// Creates a classified executable failure.
    #[must_use]
    pub fn new(class: impl Into<Text>, message: impl Into<Text>) -> Self {
        Self {
            class: class.into(),
            message: message.into(),
        }
    }

    /// Returns the application-defined failure class.
    #[must_use]
    pub fn class(&self) -> &str {
        &self.class
    }

    /// Returns the human-readable failure description.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Cooperative stop signal supplied to an opaque executable.
#[derive(Clone, Debug)]
pub struct ExecutionStop {
    receiver: watch::Receiver<bool>,
}

impl ExecutionStop {
    /// Reports whether host stop has been requested.
    #[must_use]
    pub fn is_requested(&self) -> bool {
        *self.receiver.borrow()
    }

    /// Waits until host stop is requested or the host disappears.
    pub async fn requested(&mut self) {
        while !*self.receiver.borrow_and_update() {
            if self.receiver.changed().await.is_err() {
                return;
            }
        }
    }
}

/// One change observed by a live executable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionSignal {
    /// The graph or package frontier changed to this coalesced revision.
    FrontierChanged(u64),
    /// The execution host requested cooperative stop.
    StopRequested,
    /// Proposal admission closed or faulted independently of frontier shape.
    SessionEnded(SessionStatus),
}

/// Uniform facilities supplied to one opaque executable instance.
pub struct ExecutionContext {
    node_id: Text,
    session: SessionHandle,
    frontier: FrontierReceiver,
    stop: ExecutionStop,
    custody: Arc<SubmissionCustody>,
    activity: Arc<ActivityTracker>,
}

impl fmt::Debug for ExecutionContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExecutionContext")
            .field("node_id", &self.node_id)
            .field("session_status", &self.session.status())
            .field("frontier_revision", &self.frontier.revision())
            .field("stop_requested", &self.stop.is_requested())
            .finish_non_exhaustive()
    }
}

impl ExecutionContext {
    pub(crate) fn owns_invocation(&self, handle: &crate::context::InvocationHandle) -> bool {
        self.session.owns_invocation(handle)
            && handle
                .inner
                .custody
                .as_ref()
                .is_some_and(|custody| Arc::ptr_eq(custody, &self.custody))
    }

    /// Begins a durable invocation bound to this execution's custody.
    ///
    /// # Errors
    /// Returns an error for revoked custody, invalid trigger or policy, unavailable dependencies, or persistence failure.
    pub async fn begin_invocation(
        &self,
        trigger: crate::context::InvocationTrigger,
        policy: crate::context::ContextPolicy,
    ) -> Result<crate::context::InvocationHandle, crate::context::ContextError> {
        self.session
            .begin_invocation_bound(
                self.node_id.clone(),
                trigger,
                policy,
                Vec::new(),
                Some(self.custody.clone()),
            )
            .await
    }
    /// Begins a root invocation with trusted explicit resource dependencies.
    ///
    /// # Errors
    /// Returns an error for revoked custody, invalid trigger or policy, unavailable dependencies, or persistence failure.
    pub async fn begin_invocation_with_content(
        &self,
        trigger: crate::context::InvocationTrigger,
        policy: crate::context::ContextPolicy,
        contents: Vec<ContentId>,
    ) -> Result<crate::context::InvocationHandle, crate::context::ContextError> {
        self.session
            .begin_invocation_bound(
                self.node_id.clone(),
                trigger,
                policy,
                contents,
                Some(self.custody.clone()),
            )
            .await
    }
    /// Enables optional reporting of this execution's current invocations.
    ///
    /// An executable that never obtains a reporter has unknown activity.
    /// Reporting does not reserve packages or affect proposal admission.
    #[must_use]
    pub fn activity_reporter(&self) -> ActivityReporter {
        self.activity.reporter()
    }

    /// Returns the graph node identity to which this instance was attached.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Reads the current graph from the serialized session owner.
    ///
    /// # Errors
    /// Requires reopening if a failed commit has not been resolved.
    pub async fn kernel(&self) -> Result<Arc<Kernel>, SessionError> {
        self.session.kernel().await
    }

    /// Returns the latest proposal-session lifecycle.
    #[must_use]
    pub fn session_status(&self) -> SessionStatus {
        self.session.status()
    }

    /// Returns currently pending packages at this instance's graph position.
    ///
    /// Observing packages does not reserve or consume them. Only a proposal
    /// accepted by the kernel changes package custody.
    ///
    /// # Errors
    ///
    /// Returns an error if the attached node is absent from the current graph
    /// or current state cannot be read.
    pub async fn pending(&self) -> Result<PendingFrontier, SessionError> {
        self.session.pending_at(Arc::clone(&self.node_id)).await
    }

    /// Returns one bounded page of pending packages at this execution's node.
    ///
    /// `after` is an exclusive package-identity cursor. If the returned
    /// revision changes between pages, restart pagination to obtain a coherent
    /// frontier traversal.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero limit or unreadable persistent state.
    pub async fn pending_page(
        &self,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        self.session
            .pending_page_at(Arc::clone(&self.node_id), after, limit)
            .await
    }

    /// Returns the next complete package trigger at this graph position.
    ///
    /// The result is bounded by the node's admitted ingress mode and in-degree.
    /// It is an observation rather than a reservation; submission performs the
    /// authoritative custody check.
    ///
    /// # Errors
    ///
    /// Returns an error if the attached node is absent or persistent state cannot
    /// be read.
    pub async fn next_trigger(&self) -> Result<PendingFrontier, SessionError> {
        self.session
            .next_trigger_at(Arc::clone(&self.node_id))
            .await
    }

    /// Returns the least pending package on one incoming edge at this position.
    ///
    /// The projection contains zero or one package and does not reserve it.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or non-incoming edge, or unreadable
    /// persistent state.
    pub async fn next_pending_on_edge(
        &self,
        edge_id: impl Into<Arc<str>>,
    ) -> Result<PendingFrontier, SessionError> {
        self.session
            .next_pending_on_edge_at(Arc::clone(&self.node_id), edge_id)
            .await
    }

    /// Reads retained package metadata and its producer's immediate causal inputs.
    ///
    /// Returns `None` for an unknown identity. Accepted packages remain readable
    /// after consumption or retirement. No payloads are read and no package
    /// custody changes.
    ///
    /// # Errors
    ///
    /// Returns an error for unreadable metadata or unresolved session faults.
    pub async fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SessionError> {
        self.session.package_history(package_id).await
    }

    /// Resolves bytes retained by the proposal session for an accepted digest.
    ///
    /// # Errors
    ///
    /// Returns an error when durable content is unreadable or fails its digest.
    pub async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        self.session.content(digest).await
    }

    /// Returns this session's independent blob, artifact, and transfer handle.
    /// # Errors
    /// Reports unreadable session state.
    pub async fn content_store(&self) -> Result<ContentStore, SessionError> {
        self.session.content_store().await
    }

    /// Returns payload size without allocating the complete content.
    /// # Errors
    /// Reports unreadable storage or inconsistent metadata.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>, SessionError> {
        self.session.content_size(digest).await
    }

    /// Reads an exact verified byte range without holding the session lock.
    /// # Errors
    /// Reports invalid offsets, storage failures, or corrupt content.
    pub async fn content_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Payload>, SessionError> {
        self.session.content_range(digest, range).await
    }

    /// Opens a verified, seekable reader for one complete content commitment.
    /// # Errors
    /// Reports unreadable storage or corrupt content.
    pub async fn content_reader(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<ContentReader>, SessionError> {
        self.session.content_reader(digest).await
    }

    /// Returns artifact dependencies retained with the specified activation.
    /// # Errors
    /// Reports unreadable or inconsistent retained state.
    pub async fn activation_content(
        &self,
        activation_id: ActivationId,
    ) -> Result<Vec<ContentId>, SessionError> {
        self.session.activation_content(activation_id).await
    }

    /// Submits one canonical root or package-triggered proposal.
    ///
    /// The host does not translate or pre-validate graph semantics. Trusted
    /// executable definitions may therefore submit any proposal; the kernel
    /// returns the graph decision.
    ///
    /// # Errors
    ///
    /// Returns an operational error when proposal admission is closed or
    /// faulted, or when this execution's submission custody has been revoked.
    pub async fn submit(
        &self,
        proposal: ActivationProposal,
    ) -> Result<ProposalDecision, SubmitError> {
        self.session
            .submit_with_custody(proposal, &self.custody)
            .await
    }

    /// Submits a proposal and retains its explicit artifact dependencies.
    ///
    /// Submission uses this execution's custody boundary. Dependencies must be
    /// complete in the session's content store before admission.
    /// # Errors
    /// Reports closed or faulted admission, unavailable content, or revoked custody.
    pub async fn submit_with_content(
        &self,
        proposal: ActivationProposal,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, SubmitError> {
        self.session
            .submit_content_with_custody(proposal, contents, &self.custody)
            .await
    }

    /// Returns the latest coalesced graph and frontier revision.
    #[must_use]
    pub fn frontier_revision(&self) -> u64 {
        self.frontier.revision()
    }

    /// Returns a clone of the cooperative stop signal.
    #[must_use]
    pub fn stop(&self) -> ExecutionStop {
        self.stop.clone()
    }

    /// Waits for frontier change, host stop, or proposal-session termination.
    pub async fn next_signal(&mut self) -> ExecutionSignal {
        if self.stop.is_requested() {
            return ExecutionSignal::StopRequested;
        }
        if self.session.status() != SessionStatus::Open {
            return ExecutionSignal::SessionEnded(self.session.status());
        }
        let session = self.session.clone();
        tokio::select! {
            revision = self.frontier.changed() => ExecutionSignal::FrontierChanged(revision),
            () = self.stop.requested() => ExecutionSignal::StopRequested,
            status = session.wait_closed() => ExecutionSignal::SessionEnded(status),
        }
    }
}

/// Terminal or live state of one launched executable instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionStatus {
    /// The executable future is live.
    Running,
    /// The executable returned successfully and is no longer live.
    Exited,
    /// The executable returned a classified failure and is no longer live.
    Failed(ExecutionFailure),
    /// The executable panicked and is no longer live.
    Panicked(Text),
    /// The executable task was forcibly aborted and is no longer live.
    Aborted,
}

impl ExecutionStatus {
    /// Reports whether the executable is no longer live.
    #[must_use]
    pub const fn is_terminal(&self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Operational failure while launching an opaque executable.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum LaunchError {
    /// The configured graph position does not exist.
    #[error("cannot launch executable for unknown node {0}")]
    UnknownNode(Text),
    /// The session cannot provide a coherent current graph observation.
    #[error("cannot observe session while launching executable: {0}")]
    Session(#[source] SessionError),
    /// The execution host has begun terminal shutdown.
    #[error("execution host is shutting down")]
    ShuttingDown,
    /// The host exhausted its local execution identity space.
    #[error("execution host identity space is exhausted")]
    IdentityExhausted,
    /// Launch was attempted outside a Tokio runtime.
    #[error("launching an executable requires a Tokio runtime")]
    NoAsyncRuntime,
}

struct HostedExecution {
    abort: AbortHandle,
    stop: watch::Sender<bool>,
    custody: Arc<SubmissionCustody>,
    activity: Arc<ActivityTracker>,
}

struct ExecutionCustodyGuard {
    stop: watch::Sender<bool>,
    custody: Arc<SubmissionCustody>,
    activity: Arc<ActivityTracker>,
}

impl Drop for ExecutionCustodyGuard {
    fn drop(&mut self) {
        self.activity.close();
        self.custody.revoke();
        self.stop.send_replace(true);
    }
}

struct ExecutionHostControl {
    accepting: bool,
    executions: BTreeMap<ExecutionId, HostedExecution>,
}

struct ExecutionHostInner {
    session: SessionHandle,
    next_execution_id: AtomicU64,
    control: Mutex<ExecutionHostControl>,
    idle: Notify,
}

impl Drop for ExecutionHostInner {
    fn drop(&mut self) {
        let control = self
            .control
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for execution in control.executions.values() {
            execution.activity.close();
            execution.custody.revoke();
            execution.stop.send_replace(true);
            execution.abort.abort();
        }
    }
}

/// Runtime-owned lifecycle host for opaque executable definitions.
///
/// This host assigns no semantic node categories. Every launched definition
/// receives the same [`ExecutionContext`]. Multiple definitions may be attached
/// to the same graph position, and one definition may remain live for the
/// session's entire lifetime.
#[derive(Clone)]
pub struct ExecutionHost {
    inner: Arc<ExecutionHostInner>,
}

impl fmt::Debug for ExecutionHost {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let control = self
            .inner
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        formatter
            .debug_struct("ExecutionHost")
            .field("session_status", &self.inner.session.status())
            .field("accepting", &control.accepting)
            .field("live_executions", &control.executions.len())
            .finish()
    }
}

impl ExecutionHost {
    /// Creates an empty execution host over one proposal session.
    #[must_use]
    pub fn new(session: SessionHandle) -> Self {
        Self {
            inner: Arc::new(ExecutionHostInner {
                session,
                next_execution_id: AtomicU64::new(1),
                control: Mutex::new(ExecutionHostControl {
                    accepting: true,
                    executions: BTreeMap::new(),
                }),
                idle: Notify::new(),
            }),
        }
    }

    /// Returns the canonical proposal session observed by this host.
    #[must_use]
    pub fn session(&self) -> &SessionHandle {
        &self.inner.session
    }

    /// Launches one opaque executable at one current graph node.
    ///
    /// No user code runs while host state is locked. The returned handle
    /// observes only operational execution status; graph effects remain visible
    /// through the proposal session. Node validation is an observation: a later
    /// rewrite may remove the node before its executable starts.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown node, shutting down host, exhausted
    /// identity space, missing Tokio runtime, or unavailable current state.
    /// Closed sessions still admit read-only executions.
    pub async fn launch(
        &self,
        node_id: impl Into<Text>,
        definition: impl ExecutableDefinition,
    ) -> Result<ExecutionHandle, LaunchError> {
        self.launch_arc(node_id, Arc::new(definition)).await
    }

    /// Launches one dynamically dispatched opaque executable definition.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::launch`].
    pub async fn launch_arc(
        &self,
        node_id: impl Into<Text>,
        definition: Arc<dyn ExecutableDefinition>,
    ) -> Result<ExecutionHandle, LaunchError> {
        tokio::runtime::Handle::try_current().map_err(|_| LaunchError::NoAsyncRuntime)?;
        let node_id = node_id.into();
        let frontier = match self.inner.session.frontier_at(Arc::clone(&node_id)).await {
            Ok(frontier) => frontier,
            Err(SessionError::UnknownNode(node_id)) => {
                return Err(LaunchError::UnknownNode(node_id));
            }
            Err(error) => return Err(LaunchError::Session(error)),
        };
        let (stop, stop_receiver) = watch::channel(false);
        let (status, status_receiver) = watch::channel(ExecutionStatus::Running);
        let custody = Arc::new(SubmissionCustody::new());
        let activity = Arc::new(ActivityTracker::new());
        let context = ExecutionContext {
            node_id: Arc::clone(&node_id),
            session: self.inner.session.clone(),
            frontier,
            stop: ExecutionStop {
                receiver: stop_receiver,
            },
            custody: Arc::clone(&custody),
            activity: Arc::clone(&activity),
        };
        let mut control = self
            .inner
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !control.accepting {
            return Err(LaunchError::ShuttingDown);
        }
        let execution_id = self
            .inner
            .next_execution_id
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
                current.checked_add(1)
            })
            .map(ExecutionId)
            .map_err(|_| LaunchError::IdentityExhausted)?;
        let (start, receive_start) = oneshot::channel();
        let execution_stop = stop.clone();
        let execution_custody = Arc::clone(&custody);
        let execution_activity = Arc::clone(&activity);
        let execution = tokio::spawn(async move {
            let _custody_guard = ExecutionCustodyGuard {
                stop: execution_stop,
                custody: execution_custody,
                activity: execution_activity,
            };
            if receive_start.await.is_err() {
                return Ok(());
            }
            definition.launch(context).await
        });
        let abort = execution.abort_handle();
        let previous = control.executions.insert(
            execution_id,
            HostedExecution {
                abort: abort.clone(),
                stop: stop.clone(),
                custody: Arc::clone(&custody),
                activity: Arc::clone(&activity),
            },
        );
        debug_assert!(previous.is_none(), "monotone execution identity is unique");
        drop(control);
        let _ = start.send(());

        let inner: Weak<ExecutionHostInner> = Arc::downgrade(&self.inner);
        let terminal_stop = stop.clone();
        let terminal_custody = Arc::clone(&custody);
        let terminal_activity = Arc::clone(&activity);
        let terminal_session = self.inner.session.clone();
        tokio::spawn(async move {
            let terminal = match execution.await {
                Ok(Ok(())) => ExecutionStatus::Exited,
                Ok(Err(failure)) => ExecutionStatus::Failed(failure),
                Err(error) if error.is_cancelled() => ExecutionStatus::Aborted,
                Err(error) => ExecutionStatus::Panicked(Arc::from(error.to_string())),
            };
            terminal_activity.close();
            terminal_custody.revoke();
            let _ = terminal_session
                .interrupt_invocation_owner(&terminal_custody)
                .await;
            terminal_stop.send_replace(true);
            status.send_replace(terminal);
            if let Some(inner) = inner.upgrade() {
                let mut control = inner
                    .control
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                let removed = control.executions.remove(&execution_id).is_some();
                let became_idle = removed && control.executions.is_empty();
                drop(control);
                if became_idle {
                    inner.idle.notify_waiters();
                }
            }
        });

        Ok(ExecutionHandle {
            execution_id,
            node_id,
            status: status_receiver,
            stop,
            abort,
            custody,
            activity,
        })
    }

    /// Stops accepting new executable launches without disturbing live ones.
    ///
    /// This transition is terminal and shared by every clone of the host.
    pub fn stop_accepting(&self) {
        self.inner
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .accepting = false;
    }

    /// Requests cooperative stop from every live executable.
    pub fn request_stop(&self) {
        let control = self
            .inner
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for execution in control.executions.values() {
            execution.stop.send_replace(true);
        }
    }

    /// Forcibly aborts every live executable future.
    ///
    /// Abortion cannot prove that external effects have stopped.
    pub fn abort_all(&self) {
        let control = self
            .inner
            .control
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for execution in control.executions.values() {
            execution.activity.close();
            execution.custody.revoke();
            execution.abort.abort();
        }
    }

    /// Waits until no hosted executable future remains live.
    pub async fn wait_idle(&self) {
        loop {
            let notified = self.inner.idle.notified();
            if self
                .inner
                .control
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .executions
                .is_empty()
            {
                return;
            }
            notified.await;
        }
    }

    /// Immediately stops accepting launches, requests stop, forcibly aborts
    /// remaining futures, and waits for host cleanup.
    ///
    /// This is a forced convenience operation, not a cooperative grace period.
    /// Call [`Self::stop_accepting`], [`Self::request_stop`], and
    /// [`Self::wait_idle`] separately when executables should receive time to
    /// exit cooperatively. This does not close the proposal session; execution
    /// lifetime and graph state lifetime are deliberately independent.
    pub async fn shutdown(&self) {
        self.stop_accepting();
        self.request_stop();
        self.abort_all();
        self.wait_idle().await;
    }
}

/// Cloneable operational handle to one launched executable instance.
#[derive(Clone, Debug)]
pub struct ExecutionHandle {
    execution_id: ExecutionId,
    node_id: Text,
    status: watch::Receiver<ExecutionStatus>,
    stop: watch::Sender<bool>,
    abort: AbortHandle,
    custody: Arc<SubmissionCustody>,
    activity: Arc<ActivityTracker>,
}

impl ExecutionHandle {
    /// Observes this execution's optional, in-memory invocation reports.
    ///
    /// Activity is self-reported telemetry. This observation is not atomic with
    /// execution status or the proposal session's graph/package frontier.
    #[must_use]
    pub fn activity(&self) -> ActivitySnapshot {
        self.activity.snapshot()
    }

    /// Returns the host-local execution identity.
    #[must_use]
    pub const fn id(&self) -> ExecutionId {
        self.execution_id
    }

    /// Returns the attached graph node identity.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Returns the latest observed operational status.
    #[must_use]
    pub fn status(&self) -> ExecutionStatus {
        self.status.borrow().clone()
    }

    /// Requests cooperative stop from this executable.
    pub fn request_stop(&self) {
        self.stop.send_replace(true);
    }

    /// Forcibly aborts this executable future.
    ///
    /// Abortion cannot prove that external effects have stopped.
    pub fn abort(&self) {
        self.activity.close();
        self.custody.revoke();
        self.abort.abort();
    }

    /// Waits until this executable is no longer live.
    pub async fn wait(&self) -> ExecutionStatus {
        let mut status = self.status.clone();
        loop {
            let current = status.borrow_and_update().clone();
            if current.is_terminal() {
                return current;
            }
            if status.changed().await.is_err() {
                return ExecutionStatus::Aborted;
            }
        }
    }
}

#[cfg(test)]
mod activity_tests {
    use std::time::Duration;

    use tokio::sync::{Barrier, mpsc};

    use super::*;
    use crate::{Contract, DefinitionId, Graph, Node, NodeDefinition, ProposalRuntime, Schema};

    fn fixture() -> (ProposalRuntime, ExecutionHost) {
        let kernel = Kernel::admit(
            DefinitionId::new("execution-activity").expect("definition"),
            Schema::new(["Worker"], ["Result"], []).expect("schema"),
            Graph::new([Node::new("worker").expect("node")], []).expect("graph"),
            [Contract::new("result", "Result", |_| Ok(())).expect("contract")],
            [NodeDefinition::new("worker", ["Worker"], "result").expect("definition")],
            [],
            [],
            [],
        )
        .expect("kernel");
        let runtime = ProposalRuntime::new(Arc::new(kernel));
        let host = ExecutionHost::new(runtime.open().expect("session"));
        (runtime, host)
    }

    #[tokio::test]
    async fn opaque_uninstrumented_executions_have_unknown_activity() {
        let (_runtime, host) = fixture();
        let execution = host
            .launch("worker", |_: ExecutionContext| async {
                std::future::pending::<Result<(), ExecutionFailure>>().await
            })
            .await
            .expect("launch");
        assert_eq!(execution.status(), ExecutionStatus::Running);
        assert!(!execution.activity().reported());
        assert!(execution.activity().invocations().is_empty());
        execution.abort();
        assert_eq!(execution.wait().await, ExecutionStatus::Aborted);
        assert!(!execution.activity().reported());
    }

    #[tokio::test]
    async fn terminal_lifetimes_clear_and_fence_detached_activity() {
        for mode in ["exit", "failure", "panic", "abort", "host-drop"] {
            let (_runtime, host) = fixture();
            let release = Arc::new(Barrier::new(2));
            let execution_release = Arc::clone(&release);
            let (reports, mut incoming) = mpsc::unbounded_channel();
            let execution = host
                .launch("worker", move |context: ExecutionContext| {
                    let release = Arc::clone(&execution_release);
                    let reports = reports.clone();
                    async move {
                        let reporter = context.activity_reporter();
                        let guard = reporter.begin([], "detached work");
                        reports.send((reporter, guard)).expect("test observes work");
                        release.wait().await;
                        match mode {
                            "failure" => Err(ExecutionFailure::new("test", "failed")),
                            "panic" => panic!("test execution panics"),
                            _ => Ok(()),
                        }
                    }
                })
                .await
                .expect("launch");
            let (reporter, detached_guard) =
                tokio::time::timeout(Duration::from_secs(2), incoming.recv())
                    .await
                    .expect("execution reports work")
                    .expect("report");
            assert!(execution.activity().reported());
            assert_eq!(execution.activity().invocations().len(), 1);
            match mode {
                "host-drop" => drop(host),
                "abort" => {
                    execution.request_stop();
                    // Cooperative stop is not proof that current work ended.
                    assert_eq!(execution.activity().invocations().len(), 1);
                    execution.abort();
                }
                _ => {
                    release.wait().await;
                }
            }
            let status = tokio::time::timeout(Duration::from_secs(2), execution.wait())
                .await
                .expect("execution terminates");
            assert!(status.is_terminal());
            assert!(execution.activity().invocations().is_empty());
            detached_guard.set_description("late update");
            let _late = reporter.begin([], "late invocation");
            assert!(execution.activity().invocations().is_empty());
        }
    }
}
