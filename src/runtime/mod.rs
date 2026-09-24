//! Canonical proposal sessions and opaque execution hosting.
//!
//! [`ProposalRuntime`] owns independent kernel states and serializes canonical
//! proposals without adding graph law. [`ExecutionHost`] launches opaque
//! definitions over current graph and frontier observations.

mod activity;
mod hosting;
pub(crate) mod object_store;
pub(crate) mod session;
pub(crate) mod sqlite;

pub use activity::{ActivityReporter, ActivitySnapshot, InvocationActivity, InvocationGuard};
pub use hosting::{
    ExecutableDefinition, ExecutionContext, ExecutionFailure, ExecutionFuture, ExecutionHandle,
    ExecutionHost, ExecutionId, ExecutionSignal, ExecutionStatus, ExecutionStop, LaunchError,
};
pub use session::{
    FrontierCounts, FrontierOverview, FrontierReceiver, PackageHistory, PendingFrontier,
    ProposalDecision, ProposalRuntime, RewriteOutcome, SessionError, SessionHandle,
    SessionOpenError, SessionRewrite, SessionSnapshot, SessionStatus, SessionTransitionError,
    SubmitError,
};
