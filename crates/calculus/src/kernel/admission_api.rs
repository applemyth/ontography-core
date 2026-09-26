//! Public request and rejection vocabulary for kernel admission.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use thiserror::Error;

use crate::graph::{
    Authority, AuthorityMatch, AuthorityTag, ContentDigest, ContractViolation,
    DefinitionFingerprint, DefinitionId, IngressMode, Payload,
};

use super::occurrence::{ActivationId, PackageId, PackageRecord, Trigger};

/// Immutable evidence that one exact package set currently forms a legal
/// package trigger.
///
/// A witness snapshots the validated package records and the static ingress
/// facts used to validate them. It neither reserves nor consumes its packages,
/// and it may become stale as the state advances. Activation admission always
/// revalidates the package trigger against the then-current state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TriggerWitness {
    pub(super) definition_id: DefinitionId,
    pub(super) definition_fingerprint: DefinitionFingerprint,
    pub(super) package_ids: BTreeSet<PackageId>,
    pub(super) packages: BTreeMap<PackageId, PackageRecord>,
    pub(super) node_id: Arc<str>,
    pub(super) authority: Authority,
    pub(super) ingress_mode: IngressMode,
    pub(super) incoming_edge_ids: BTreeSet<Arc<str>>,
    pub(super) realized_edge_ids: BTreeSet<Arc<str>>,
}

impl TriggerWitness {
    /// Returns the admitted definition that issued this witness.
    #[must_use]
    pub const fn definition_id(&self) -> &DefinitionId {
        &self.definition_id
    }

    /// Returns the structural fingerprint of the issuing definition.
    #[must_use]
    pub const fn definition_fingerprint(&self) -> &DefinitionFingerprint {
        &self.definition_fingerprint
    }

    /// Returns the exact canonical package set validated by this witness.
    #[must_use]
    pub const fn package_ids(&self) -> &BTreeSet<PackageId> {
        &self.package_ids
    }

    /// Returns snapshots of the validated package records.
    #[must_use]
    pub const fn packages(&self) -> &BTreeMap<PackageId, PackageRecord> {
        &self.packages
    }

    /// Returns the common static target at which the packages have custody.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Returns the common authority governing a resulting activation.
    #[must_use]
    pub const fn authority(&self) -> &Authority {
        &self.authority
    }

    /// Returns the target node's admitted ingress mode.
    #[must_use]
    pub const fn ingress_mode(&self) -> IngressMode {
        self.ingress_mode
    }

    /// Returns every static edge admitted as incoming to the target node.
    #[must_use]
    pub const fn incoming_edge_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.incoming_edge_ids
    }

    /// Returns the exact static edges realized by the witnessed packages.
    #[must_use]
    pub const fn realized_edge_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.realized_edge_ids
    }
}

/// How a proposed output obtains its carried authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutputAuthority {
    /// Carry the activation's governing authority unchanged.
    Carry,
    /// Apply an admitted transition and carry its target authority.
    Transition(Authority),
}

/// One requested package birth, optionally delivered through an edge immediately.
///
/// Its payload bytes exist only through admission. Accepted state replaces them
/// with a kernel-computed [`ContentDigest`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Emission {
    pub(super) destination: EmissionDestination,
    pub(super) authority: OutputAuthority,
    pub(super) payload: Payload,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum EmissionDestination {
    Delivered(Arc<str>),
    Outbound(Arc<str>),
}

impl Emission {
    /// Creates a package birth and delivery as one admitted operation.
    #[must_use]
    pub fn new(edge_id: impl Into<Arc<str>>, authority: OutputAuthority, payload: Payload) -> Self {
        Self {
            destination: EmissionDestination::Delivered(edge_id.into()),
            authority,
            payload,
        }
    }

    /// Creates a typed package at its producer in the outbound phase.
    ///
    /// Production checks the schema and authority transition. An exact edge
    /// contract is checked later when a transfer is requested. No route is
    /// required at birth; a subsequent rewrite applies frontier cleanup.
    #[must_use]
    pub fn outbound(
        object_type: impl Into<Arc<str>>,
        authority: OutputAuthority,
        payload: Payload,
    ) -> Self {
        Self {
            destination: EmissionDestination::Outbound(object_type.into()),
            authority,
            payload,
        }
    }

    /// Returns the delivery edge, or `None` for an outbound birth.
    #[must_use]
    pub fn edge_id(&self) -> Option<&str> {
        match &self.destination {
            EmissionDestination::Delivered(edge_id) => Some(edge_id),
            EmissionDestination::Outbound(_) => None,
        }
    }

    /// Returns the declared object type of an outbound birth, or `None` for a
    /// delivered one, whose type is the edge contract's.
    #[must_use]
    pub fn outbound_type(&self) -> Option<&str> {
        match &self.destination {
            EmissionDestination::Delivered(_) => None,
            EmissionDestination::Outbound(object_type) => Some(object_type),
        }
    }

    /// Returns how the package obtains its carried authority.
    #[must_use]
    pub const fn authority(&self) -> &OutputAuthority {
        &self.authority
    }

    /// Returns the requested payload bytes.
    #[must_use]
    pub const fn payload(&self) -> &Payload {
        &self.payload
    }
}

/// One requested atomic activation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ActivationProposal {
    pub(super) trigger: Trigger,
    pub(super) result: Payload,
    pub(super) emissions: Vec<Emission>,
}

impl ActivationProposal {
    /// Requests a nullary root activation.
    #[must_use]
    pub fn root(node_id: impl Into<Arc<str>>, authority: Authority, result: Payload) -> Self {
        Self {
            trigger: Trigger::Orig {
                node_id: node_id.into(),
                authority,
            },
            result,
            emissions: Vec::new(),
        }
    }

    /// Requests an activation triggered by one pending package occurrence.
    #[must_use]
    pub fn package(package_id: PackageId, result: Payload) -> Self {
        Self::join([package_id], result)
    }

    /// Requests one activation jointly triggered by package occurrences.
    ///
    /// Admission rejects an empty set, packages at different nodes, packages
    /// carrying unequal authority, or a set outside the node's ingress mode.
    #[must_use]
    pub fn join<I>(package_ids: I, result: Payload) -> Self
    where
        I: IntoIterator<Item = PackageId>,
    {
        Self {
            trigger: Trigger::Pkgs {
                package_ids: package_ids.into_iter().collect(),
            },
            result,
            emissions: Vec::new(),
        }
    }

    /// Adds one output package request.
    pub fn emit(&mut self, emission: Emission) {
        self.emissions.push(emission);
    }

    /// Returns the proposed package inputs, or `None` for a root.
    #[must_use]
    pub const fn package_ids(&self) -> Option<&BTreeSet<PackageId>> {
        self.trigger.inputs()
    }

    /// Returns the payload bytes of every requested emission, in order.
    #[must_use]
    pub fn emission_payloads(&self) -> impl ExactSizeIterator<Item = &Payload> {
        self.emissions.iter().map(|emission| &emission.payload)
    }
}

/// Failure to restore persisted activation-owned occurrence records.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum StateRestoreError {
    /// Fixed-graph history cannot encode a state changed by rewriting, transfer,
    /// retirement, or vocabulary extension.
    #[error(
        "fixed-graph history export cannot encode rewrites, transfers, retirements, or extensions"
    )]
    UnsupportedDynamicState,
    /// Persisted definition binding does not match the reconstructing kernel.
    #[error(
        "persisted definition {actual_id}@{actual_fingerprint} does not match kernel definition {expected_id}@{expected_fingerprint}"
    )]
    DefinitionMismatch {
        /// Kernel definition identity.
        expected_id: DefinitionId,
        /// Persisted definition identity.
        actual_id: DefinitionId,
        /// Kernel structural fingerprint.
        expected_fingerprint: DefinitionFingerprint,
        /// Persisted structural fingerprint.
        actual_fingerprint: DefinitionFingerprint,
    },
    /// A persisted activation is rejected by canonical activation validation.
    #[error("invalid persisted activation {activation_id}: {source}")]
    InvalidActivation {
        /// Invalid activation identity.
        activation_id: ActivationId,
        /// Canonical activation rejection.
        #[source]
        source: Box<Reject>,
    },
    /// No external bytes were supplied for a persisted package commitment.
    #[error("missing payload evidence for persisted package {package_id} ({content_digest})")]
    MissingPayloadEvidence {
        /// Package whose committed bytes are unavailable.
        package_id: PackageId,
        /// Accepted content commitment requiring evidence.
        content_digest: ContentDigest,
    },
    /// Supplied external bytes do not match a persisted package commitment.
    #[error(
        "payload evidence for persisted package {package_id} hashes to {actual}, expected {expected}"
    )]
    PayloadEvidenceMismatch {
        /// Package whose supplied bytes do not match.
        package_id: PackageId,
        /// Persisted content commitment.
        expected: ContentDigest,
        /// Commitment computed from the supplied evidence.
        actual: ContentDigest,
    },
    /// More than one activation consumes one package edge occurrence.
    #[error("persisted package {package_id} has multiple consumers")]
    DuplicateConsumer {
        /// Multiply consumed package.
        package_id: PackageId,
    },
    /// Activation/package causality contains a cycle instead of a rooted DAG.
    #[error("persisted activation {activation_id} is in or blocked by a causal cycle")]
    CausalCycle {
        /// Activation left with positive causal indegree after cycle detection.
        activation_id: ActivationId,
    },
}

impl StateRestoreError {
    pub(super) fn invalid(activation_id: ActivationId, source: Reject) -> Self {
        Self::InvalidActivation {
            activation_id,
            source: Box::new(source),
        }
    }
}

/// Dynamic activation rejection. Rejection leaves the predecessor unchanged.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum Reject {
    /// The monotone state revision cannot advance without wrapping.
    #[error("state revision is exhausted")]
    RevisionExhausted,
    /// State belongs to another static workflow definition.
    #[error(
        "state definition {actual_id}@{actual_fingerprint} does not match kernel definition {expected_id}@{expected_fingerprint}"
    )]
    StateMismatch {
        /// Kernel definition identity.
        expected_id: DefinitionId,
        /// State definition identity.
        actual_id: DefinitionId,
        /// Kernel definition fingerprint.
        expected_fingerprint: DefinitionFingerprint,
        /// State definition fingerprint.
        actual_fingerprint: DefinitionFingerprint,
    },
    /// Requested root node does not exist.
    #[error("unknown node: {node_id}")]
    UnknownNode {
        /// Requested node.
        node_id: Arc<str>,
    },
    /// Requested triggering package does not exist.
    #[error("unknown package: {package_id}")]
    UnknownPackage {
        /// Requested package occurrence.
        package_id: PackageId,
    },
    /// A historical unconsumed package has been removed from the live frontier.
    #[error("package {package_id} has been retired")]
    PackageRetired {
        /// Retired package identity.
        package_id: PackageId,
    },
    /// A package has not yet been admitted as a delivered input.
    #[error("package {package_id} is not a delivered input")]
    PackageNotDelivered {
        /// Undelivered package identity.
        package_id: PackageId,
    },
    /// A package birth names an object type absent from the schema.
    #[error("unknown output object type: {object_type}")]
    UnknownObjectType {
        /// Requested object type.
        object_type: Arc<str>,
    },
    /// A package's immutable type differs from the selected edge contract's type.
    #[error("package {package_id} has type {actual}, expected {expected}")]
    PackageTypeMismatch {
        /// Package whose type was rejected.
        package_id: PackageId,
        /// Selected contract's object type.
        expected: Arc<str>,
        /// Immutable package object type.
        actual: Arc<str>,
    },
    /// A package-triggered activation contains no packages.
    #[error("package-triggered activation requires at least one package")]
    EmptyPackageTrigger,
    /// A package identity does not name the activation that contains it.
    #[error("package {package_id} is not owned by activation {activation_id}")]
    InvalidPackageIdentity {
        /// Misowned package occurrence.
        package_id: PackageId,
        /// Activation record containing the package.
        activation_id: ActivationId,
    },
    /// Triggering package has already activated a node.
    #[error("package {package_id} already triggered activation {activation_id}")]
    AlreadyActivated {
        /// Consumed package.
        package_id: PackageId,
        /// Existing consuming activation.
        activation_id: ActivationId,
    },
    /// Packages proposed for one join do not target the same node.
    #[error("package {package_id} targets node {actual}, not join node {expected}")]
    JoinTargetMismatch {
        /// Package targeting a different node.
        package_id: PackageId,
        /// Target selected by the first package.
        expected: Arc<str>,
        /// Mismatched package target.
        actual: Arc<str>,
    },
    /// Packages proposed for one join do not carry equal authority.
    #[error("package {package_id} carries authority incompatible with the join")]
    JoinAuthorityMismatch {
        /// Package carrying different authority.
        package_id: PackageId,
        /// Authority selected by the first package.
        expected: Authority,
        /// Mismatched package authority.
        actual: Authority,
    },
    /// More than one proposed package realizes the same static ingress edge.
    #[error("join at node {node_id} contains more than one package on edge {edge_id}")]
    DuplicateJoinEdge {
        /// Join node.
        node_id: Arc<str>,
        /// Duplicated ingress edge.
        edge_id: Arc<str>,
    },
    /// A single-input node was proposed with several packages.
    #[error("node {node_id} admits one package, not {input_count}")]
    JoinNotAllowed {
        /// Single-input node.
        node_id: Arc<str>,
        /// Proposed package count.
        input_count: usize,
    },
    /// A join does not contain exactly one package from every incoming edge.
    #[error("join at node {node_id} does not match its incoming edge set")]
    JoinEdgeMismatch {
        /// Join node.
        node_id: Arc<str>,
        /// Statically required incoming edges.
        expected: BTreeSet<Arc<str>>,
        /// Incoming edges represented by the proposal.
        actual: BTreeSet<Arc<str>>,
    },
    /// Requested root node is outside the root-policy domain.
    #[error("node {node_id} is not permitted to initiate a causal component")]
    RootNotAllowed {
        /// Requested node.
        node_id: Arc<str>,
    },
    /// Requested root authority lies above the node's root ceiling.
    #[error("root authority at node {node_id} exceeds its ceiling")]
    RootAuthorityExceeded {
        /// Root node.
        node_id: Arc<str>,
        /// Requested initial authority.
        requested: Authority,
        /// Maximum admitted initial authority.
        ceiling: Authority,
    },
    /// Requested authority contains a tag outside the schema.
    #[error("authority requested at node {node_id} lies outside the schema")]
    AuthorityOutsideSchema {
        /// Governing node.
        node_id: Arc<str>,
        /// Invalid authority.
        authority: Authority,
    },
    /// Node result violates its exact result contract.
    #[error("node {node_id} result contract {contract_id} rejected payload: {source}")]
    ResultContract {
        /// Executing node.
        node_id: Arc<str>,
        /// Rejected contract.
        contract_id: Arc<str>,
        /// Exact-contract violation.
        source: ContractViolation,
    },
    /// Requested authority transition is absent from the sealed policy.
    #[error("node {node_id} is not authorized to establish the requested authority transition")]
    UnauthorizedAuthorityTransition {
        /// Executing node.
        node_id: Arc<str>,
        /// Governing authority.
        from: Authority,
        /// Requested output authority.
        to: Authority,
    },
    /// An output refers to no admitted concrete edge.
    #[error("unknown edge: {edge_id}")]
    UnknownEdge {
        /// Requested edge.
        edge_id: Arc<str>,
    },
    /// An output edge does not originate at the executing node.
    #[error("edge {edge_id} starts at {actual}, not executing node {expected}")]
    WrongSource {
        /// Requested edge.
        edge_id: Arc<str>,
        /// Executing node.
        expected: Arc<str>,
        /// Actual edge source.
        actual: Arc<str>,
    },
    /// Selected output authority does not satisfy the static edge tag rule.
    #[error("authority selected for edge {edge_id} does not satisfy its authority-tag rule")]
    EdgeAuthorityMismatch {
        /// Requested edge.
        edge_id: Arc<str>,
        /// Authority tags required by the edge.
        required: BTreeSet<AuthorityTag>,
        /// Rule used to compare the edge tags with the selected authority.
        authority_match: AuthorityMatch,
        /// Selected output authority.
        authority: Authority,
    },
    /// Output payload violates the selected edge's exact package contract.
    #[error(
        "edge {edge} target {target_node} package contract {contract_id} rejected payload: {source}"
    )]
    PayloadContract {
        /// Requested edge.
        edge: Arc<str>,
        /// Static edge target.
        target_node: Arc<str>,
        /// Exact edge package contract.
        contract_id: Arc<str>,
        /// Exact-contract violation.
        source: ContractViolation,
    },
}
