//! The Ontography calculus: authority-governed workflow occurrence graphs.
//!
//! Graph declarations compile into immutable kernel versions. The kernel checks
//! activations, transfers, explicit retirements, interface-preserving graph
//! rewrites with local frontier cleanup, and monotone vocabulary extensions.
//! This crate holds the graph law alone; persistence, invocation context, and
//! execution hosting live in the crates that build on it.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod graph;
mod kernel;

/// The storage adapter contract.
///
/// A persistent store supplies the [`PackageView`] and [`FrontierView`]
/// observations the kernel evaluates against, runs [`Transition::verify`] over
/// its own rows before writing the facts of a [`TransitionKind`], exports
/// [`Checkpoint`]s that [`Kernel::restore_checkpoint`](crate::Kernel::restore_checkpoint)
/// validates, and persists definition fragments in the versioned
/// [`FragmentData`] encoding. This module names everything an adapter reads or
/// writes; each name is also re-exported at the crate root.
pub mod storage {
    pub use crate::kernel::{
        Activation, ActivationId, ApplyError, Binding, Checkpoint, CheckpointError, Delivery,
        FRAGMENT_ENCODING_VERSION, FragmentData, FragmentDecodeError, FrontierView, Output,
        PackageId, PackageRecord, PackageStatus, PackageView, Retirement, RetirementReason,
        RewriteFragment, Transition, TransitionKind, Trigger,
    };
}

pub use graph::{
    Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, ContentDigest, Contract,
    ContractViolation, DefinitionError, DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition,
    Graph, IngressMode, Node, NodeDefinition, Payload, RootRule, Schema,
};
pub use kernel::{
    Activation, ActivationId, ActivationProposal, ApplyError, Binding, Checkpoint, CheckpointError,
    Delivery, Emission, ExtensionError, FRAGMENT_ENCODING_VERSION, FragmentData,
    FragmentDecodeError, FrontierView, Kernel, Output, OutputAuthority, PackageId, PackageRecord,
    PackageStatus, PackageView, Phase, Position, PreparedExtension, PreparedRewrite,
    PreparedTransfer, Reject, RetireError, Retirement, RetirementReason, RewriteError,
    RewriteFragment, RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest, State,
    StateParts, StateRestoreError, TransferError, TransferRejection, Transition, TransitionKind,
    Trigger, TriggerWitness,
};
