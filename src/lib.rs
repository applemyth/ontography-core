//! Ontography: authority-governed workflow occurrence graphs.
//!
//! Graph declarations compile into immutable kernel versions. The kernel checks
//! activations, transfers, and interface-preserving graph rewrites with frontier
//! cleanup. Runtime sessions persist and serialize these actions together.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod application;
mod config;
pub mod content;
pub mod context;
mod graph;
mod kernel;
pub mod package;
pub mod project;
pub mod runtime;
pub mod workspace;

pub use application::{
    Application, ApplicationBuilder, ApplicationContext, ApplicationError, ApplicationRunMode,
    ApplicationStartError, EdgeComponent, EdgeConfig, NodeComponent, NodeConfig,
    RunningApplication,
};
pub use config::{ApplicationConfig, ApplicationConfigError, ApplicationRegistry};
pub use content::{ContentError, ContentId, ContentMetadata, ContentReader, ContentStore};
pub use context::{
    ContextContribution, ContextError, ContextEvent, ContextMode, ContextPolicy, ContextResponse,
    InitialContext, InvocationHandle, InvocationId, InvocationRecord, InvocationStatus,
    InvocationTrigger, PackageGrant, PackageMemberGrant, ReceiptState, WorkspacePolicy,
};
pub use graph::{
    Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, ContentDigest, Contract,
    ContractViolation, DefinitionError, DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition,
    Graph, IngressMode, Node, NodeDefinition, Payload, RootRule, Schema,
};
pub use kernel::{
    Activation, ActivationId, ActivationProposal, Delivery, EdgeUse, Emission, Kernel, Output,
    OutputAuthority, Package, PackageId, Phase, Position, PreparedRewrite, PreparedTransfer,
    Reject, RetirementReason, RewriteError, RewriteFragment, RewriteGrammar, RewriteMatch,
    RewriteProduction, RewriteRequest, State, StateParts, StateRestoreError, TransferError,
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
