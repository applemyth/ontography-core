//! Ontography: authority-governed workflow occurrence graphs.
//!
//! Graph declarations compile into immutable kernel versions. The kernel checks
//! activations, transfers, explicit retirements, graph edits admitted under a
//! trusted policy with local frontier cleanup, and monotone vocabulary extensions.
//! Runtime sessions persist and serialize these actions together.
//!
//! This crate is the facade over the workspace crates: `ontography-calculus`,
//! `ontography-content`, `ontography-runtime`, and
//! `ontography-application`. It re-exports one flat set of names from them,
//! plus the calculus crate's [`storage`] module, which names the adapter
//! contract a persistent store implements.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub use ontography_application::application;
pub use ontography_application::project;
pub use ontography_calculus::storage;
pub use ontography_content::content;
pub use ontography_content::package;
pub use ontography_runtime::context;

/// Canonical proposal sessions and opaque execution hosting.
pub mod runtime {
    pub use ontography_runtime::{
        ActivityReporter, ActivitySnapshot, ExecutableDefinition, ExecutionContext,
        ExecutionFailure, ExecutionFuture, ExecutionHandle, ExecutionHost, ExecutionId,
        ExecutionSignal, ExecutionStatus, ExecutionStop, FrontierCounts, FrontierOverview,
        FrontierReceiver, InvocationActivity, InvocationGuard, LaunchError, PackageHistory,
        PendingFrontier, ProposalDecision, ProposalRuntime, RewriteOutcome, SessionError,
        SessionHandle, SessionOpenError, SessionRewrite, SessionSnapshot, SessionStatus,
        SessionTransitionError, SubmitError,
    };
}

pub use application::{
    Application, ApplicationBuilder, ApplicationContext, ApplicationError, ApplicationRunMode,
    ApplicationStartError, EdgeConfig, NodeComponent, NodeConfig, RunningApplication,
};
pub use content::{ContentError, ContentId, ContentMetadata, ContentReader, ContentStore};
pub use context::{
    ContextContribution, ContextError, ContextEvent, ContextMode, ContextPolicy, ContextResponse,
    InitialContext, InvocationHandle, InvocationId, InvocationRecord, InvocationStatus,
    InvocationTrigger, PackageGrant, ReceiptState, ViewGrant,
};
pub use ontography_application::{ApplicationConfig, ApplicationConfigError, ApplicationRegistry};
pub use ontography_calculus::{
    Activation, ActivationId, ActivationProposal, ApplyError, Authority, AuthorityMatch,
    AuthorityTag, AuthorityTransitionRule, Binding, Checkpoint, CheckpointError, ContentDigest,
    Contract, ContractViolation, DefinitionError, DefinitionFingerprint, DefinitionId, Delivery,
    DenyAll, Edge, EdgeDefinition, EditContext, EditPolicy, Emission, ExtensionError,
    FRAGMENT_ENCODING_VERSION, FragmentData, FragmentDecodeError, FrontierView, Graph, GraphEdit,
    GraphFragment, IngressMode, Kernel, Node, NodeDefinition, Output, OutputAuthority, PackageId,
    PackageRecord, PackageStatus, PackageView, Payload, PermitAll, Phase, PolicyDenial, Position,
    PreparedExtension, PreparedRewrite, PreparedTransfer, Principal, Reject, RetireError,
    Retirement, RetirementReason, RewriteError, RewriteRequest, RootRule, Schema, State,
    StateParts, StateRestoreError, TransferError, TransferRejection, Transition, TransitionKind,
    Trigger, TriggerWitness,
};
pub use package::{
    PackageDocument, PackageEnvelope, PackageError, PackageLimits, PackageStore, ResolvedEntry,
    ResolvedEntryKind, ResolvedPackage,
};
pub use runtime::{
    ActivityReporter, ActivitySnapshot, ExecutableDefinition, ExecutionContext, ExecutionFailure,
    ExecutionFuture, ExecutionHandle, ExecutionHost, ExecutionId, ExecutionSignal, ExecutionStatus,
    ExecutionStop, FrontierCounts, FrontierOverview, FrontierReceiver, InvocationActivity,
    InvocationGuard, LaunchError, PackageHistory, PendingFrontier, ProposalDecision,
    ProposalRuntime, RewriteOutcome, SessionError, SessionHandle, SessionOpenError, SessionRewrite,
    SessionSnapshot, SessionStatus, SessionTransitionError, SubmitError,
};

/// The crate version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
