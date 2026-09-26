//! Canonical proposal sessions, invocation context, and opaque execution hosting.
//!
//! [`ProposalRuntime`] owns independent kernel states and serializes canonical
//! proposals without adding graph law. [`ExecutionHost`] launches opaque
//! definitions over current graph and frontier observations. [`context`]
//! records what each invocation was shown and what it contributed.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::any::Any;
use std::sync::Arc;

mod activity;
pub mod context;
mod hosting;
pub(crate) mod object_store;
pub(crate) mod session;
pub(crate) mod sqlite;

pub use activity::{ActivityReporter, ActivitySnapshot, InvocationActivity, InvocationGuard};
pub use context::{
    ContextContribution, ContextError, ContextEvent, ContextMode, ContextPolicy, ContextResponse,
    InitialContext, InvocationHandle, InvocationId, InvocationRecord, InvocationStatus,
    InvocationTrigger, PackageGrant, PackageMemberGrant, ReceiptState, WorkspacePolicy,
};
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

/// Renders a caught panic payload as the message a session retains.
pub(crate) fn panic_message(panic: Box<dyn Any + Send>) -> Arc<str> {
    if let Some(message) = panic.downcast_ref::<&str>() {
        return Arc::from(*message);
    }
    if let Some(message) = panic.downcast_ref::<String>() {
        return Arc::from(message.as_str());
    }
    Arc::from("trusted kernel callback panicked")
}
