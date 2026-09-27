//! Transitions: the single way a state changes, and the adapter contract.
//!
//! Evaluators are pure functions from a view of a state to a [`Transition`].
//! A transition is one of five kinds, so what a transition may contain is a
//! fact of the type, not of the evaluator that built it. [`Transition::verify`]
//! checks every precondition of a transition against a view and the current
//! kernel; [`State::apply`] verifies, then mutates, and advances the revision
//! by exactly one. A storage adapter runs the same `verify` over its rows and
//! then writes the same facts, so one checker guards every representation.
//!
//! `verify` enforces the state invariants I1 through I7, including the
//! graph-dependent ones: every delivery names an admitted edge leaving the
//! producer's node and arriving at the receiver, and every live holder is a
//! node of the graph. It contains no admission law: whether a transition is
//! *lawful* is decided by the evaluators; whether its result is *well-formed*
//! is decided here, for any view, faithful or not.
//!
//! A transition is sealed: only an evaluator constructs one. Facts the
//! evaluators establish by construction (one record per output, one
//! retirement per package, the successor revision stamp on every retirement,
//! the reason each kind admits, the node set of a replacement graph, and the
//! executing node's presence in the graph) are asserted in debug builds and
//! are not part of [`ApplyError`], which names only the preconditions a
//! faithful state can fail.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use thiserror::Error;

use super::admission_api::Reject;
use super::definition::Kernel;
use super::extension::ExtensionError;
use super::frontier::{Delivery, Retirement, RetirementReason};
use super::occurrence::{
    Activation, ActivationId, PackageId, PackageRecord, PackageStatus, State, Trigger, fresh_nonce,
};
use super::retire::RetireError;
use super::rewrite::{RewriteError, TransferError};
use crate::graph::{Authority, DefinitionFingerprint, DefinitionId};

/// The exact state a transition was evaluated against.
///
/// The nonce changes on every applied transition, so a binding identifies one
/// state value even when cloned states share a revision. Adapters that own
/// their state exclusively may report a constant nonce and fence on revision.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binding {
    pub(crate) definition_id: DefinitionId,
    pub(crate) definition_fingerprint: DefinitionFingerprint,
    pub(crate) revision: u64,
    pub(crate) nonce: u128,
}

impl Binding {
    /// Constructs a binding from durable fields.
    #[must_use]
    pub const fn new(
        definition_id: DefinitionId,
        definition_fingerprint: DefinitionFingerprint,
        revision: u64,
        nonce: u128,
    ) -> Self {
        Self {
            definition_id,
            definition_fingerprint,
            revision,
            nonce,
        }
    }

    /// Returns the bound workflow-definition identity.
    #[must_use]
    pub const fn definition_id(&self) -> &DefinitionId {
        &self.definition_id
    }

    /// Returns the bound definition fingerprint.
    #[must_use]
    pub const fn definition_fingerprint(&self) -> &DefinitionFingerprint {
        &self.definition_fingerprint
    }

    /// Returns the bound revision.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns the bound nonce.
    #[must_use]
    pub const fn nonce(&self) -> u128 {
        self.nonce
    }

    fn names(&self, kernel: &Kernel) -> bool {
        self.definition_id == *kernel.id() && self.definition_fingerprint == *kernel.fingerprint()
    }
}

/// A view's binding does not admit evaluation against this kernel.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum BindingError {
    /// The view belongs to another definition or definition version.
    #[error(
        "state definition {actual_id}@{actual_fingerprint} does not match kernel definition {expected_id}@{expected_fingerprint}"
    )]
    DefinitionMismatch {
        /// Kernel definition identity.
        expected_id: DefinitionId,
        /// View definition identity.
        actual_id: DefinitionId,
        /// Kernel definition fingerprint.
        expected_fingerprint: DefinitionFingerprint,
        /// View definition fingerprint.
        actual_fingerprint: DefinitionFingerprint,
    },
    /// The monotone revision cannot advance.
    #[error("state revision is exhausted")]
    RevisionExhausted,
}

impl From<BindingError> for Reject {
    fn from(error: BindingError) -> Self {
        match error {
            BindingError::DefinitionMismatch {
                expected_id,
                actual_id,
                expected_fingerprint,
                actual_fingerprint,
            } => Self::StateMismatch {
                expected_id,
                actual_id,
                expected_fingerprint,
                actual_fingerprint,
            },
            BindingError::RevisionExhausted => Self::RevisionExhausted,
        }
    }
}

impl From<BindingError> for RewriteError {
    fn from(error: BindingError) -> Self {
        match error {
            BindingError::DefinitionMismatch { .. } => Self::StateMismatch,
            BindingError::RevisionExhausted => Self::RevisionExhausted,
        }
    }
}

impl From<BindingError> for TransferError {
    fn from(error: BindingError) -> Self {
        Self::Admission(RewriteError::from(error))
    }
}

impl From<BindingError> for RetireError {
    fn from(error: BindingError) -> Self {
        Self::Admission(RewriteError::from(error))
    }
}

impl From<BindingError> for ExtensionError {
    fn from(error: BindingError) -> Self {
        Self::Admission(RewriteError::from(error))
    }
}

impl Kernel {
    /// Checks that a view's binding names this definition and that its
    /// revision can advance, returning the successor revision.
    ///
    /// Every evaluator starts here, so no transition ever carries a base that
    /// names another definition or an exhausted revision.
    pub(crate) fn check_binding(&self, binding: &Binding) -> Result<u64, BindingError> {
        if !binding.names(self) {
            return Err(BindingError::DefinitionMismatch {
                expected_id: self.id().clone(),
                actual_id: binding.definition_id.clone(),
                expected_fingerprint: *self.fingerprint(),
                actual_fingerprint: binding.definition_fingerprint,
            });
        }
        binding
            .revision
            .checked_add(1)
            .ok_or(BindingError::RevisionExhausted)
    }
}

/// What one transition does. Exactly one kind per transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransitionKind {
    /// Accept an activation, insert its outputs live, and consume its inputs.
    Activation {
        /// Fresh activation identity.
        id: ActivationId,
        /// The complete activation record; its trigger names the consumed inputs.
        activation: Activation,
        /// One live record per output, keyed by the output's identity.
        outputs: Vec<(PackageId, PackageRecord)>,
        /// Exact input records whose metadata established the admission proof.
        inputs: BTreeMap<PackageId, PackageRecord>,
    },
    /// Deliver one live, undelivered package along an admitted edge.
    Transfer {
        /// The delivered package.
        package: PackageId,
        /// The admitted delivery.
        delivery: Delivery,
        /// Exact outbound record whose type, authority, and payload were proved.
        source: PackageRecord,
    },
    /// Retire one live package explicitly.
    Retire {
        /// The retired package.
        package: PackageId,
        /// The retirement record; its reason is [`RetirementReason::Explicit`].
        retirement: Retirement,
    },
    /// Replace the graph: retire what cleanup removed and admit fresh identities.
    Rewrite {
        /// Structural retirements, stamped with the successor revision.
        retirements: Vec<(PackageId, Retirement)>,
        /// Node identities never used before in this workflow.
        fresh_node_ids: BTreeSet<Arc<str>>,
        /// Edge identities never used before in this workflow.
        fresh_edge_ids: BTreeSet<Arc<str>>,
        /// Every node of the replacement graph, so custody can be checked.
        next_nodes: BTreeSet<Arc<str>>,
        /// Incoming routes of every `All` receiver in the replacement graph.
        next_all_routes: BTreeMap<Arc<str>, BTreeSet<Arc<str>>>,
        /// The replacement definition's fingerprint.
        next_fingerprint: DefinitionFingerprint,
    },
    /// Extend the vocabulary; graph and frontier are unchanged.
    Extension {
        /// The extended definition's fingerprint.
        next_fingerprint: DefinitionFingerprint,
    },
}

/// An evaluated change bound to the exact state it was evaluated against.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Transition {
    pub(crate) base: Binding,
    pub(crate) kind: TransitionKind,
}

impl Transition {
    /// Returns the binding this transition was evaluated against.
    #[must_use]
    pub const fn base(&self) -> &Binding {
        &self.base
    }

    /// Returns what this transition does.
    #[must_use]
    pub const fn kind(&self) -> &TransitionKind {
        &self.kind
    }

    /// Returns the definition fingerprint installed by this transition, if it
    /// changes the definition.
    #[must_use]
    pub const fn next_fingerprint(&self) -> Option<&DefinitionFingerprint> {
        match &self.kind {
            TransitionKind::Rewrite {
                next_fingerprint, ..
            }
            | TransitionKind::Extension { next_fingerprint } => Some(next_fingerprint),
            _ => None,
        }
    }

    /// Returns the revision the successor state will carry.
    ///
    /// Every evaluator checks the base revision through
    /// [`Kernel::check_binding`], so the successor exists for every transition.
    pub(crate) fn successor_revision(&self) -> u64 {
        self.base
            .revision
            .checked_add(1)
            .expect("evaluators reject an exhausted revision before building a transition")
    }

    /// Projects the packages this transition retires and why.
    #[must_use]
    pub fn retirements(&self) -> BTreeMap<PackageId, RetirementReason> {
        match &self.kind {
            TransitionKind::Retire {
                package,
                retirement,
            } => BTreeMap::from([(*package, retirement.reason())]),
            TransitionKind::Rewrite { retirements, .. } => retirements
                .iter()
                .map(|(package, retirement)| (*package, retirement.reason()))
                .collect(),
            _ => BTreeMap::new(),
        }
    }

    /// Verifies every precondition against `view` and `kernel`, mutating nothing.
    ///
    /// A transition that verifies produces a well-formed successor from the
    /// state behind `view`, whatever view it was evaluated over. Adapters call
    /// this before writing anything.
    ///
    /// # Errors
    ///
    /// Returns the first violated precondition.
    pub fn verify(&self, kernel: &Kernel, view: &dyn FrontierView) -> Result<(), ApplyError> {
        if !self.base.names(kernel) {
            return Err(ApplyError::DefinitionMismatch);
        }
        if self.base != view.binding() {
            return Err(ApplyError::BindingMismatch);
        }
        let successor = self.successor_revision();
        match &self.kind {
            TransitionKind::Activation {
                id,
                activation,
                outputs,
                inputs,
            } => verify_activation(kernel, view, *id, activation, outputs, inputs),
            TransitionKind::Transfer {
                package,
                delivery,
                source,
            } => {
                let record = require_live(view, *package)?;
                if record.delivery.is_some() {
                    return Err(ApplyError::AlreadyDelivered(*package));
                }
                verify_incidence(kernel, *package, record.producer_node(), delivery)?;
                if &record != source {
                    return Err(ApplyError::InputRecordMismatch(*package));
                }
                Ok(())
            }
            TransitionKind::Retire {
                package,
                retirement,
            } => {
                debug_assert_eq!(retirement.reason(), RetirementReason::Explicit);
                let record = require_live(view, *package)?;
                verify_retirement(view, *package, &record, retirement, successor)
            }
            TransitionKind::Rewrite { .. } => verify_rewrite(kernel, view, self),
            TransitionKind::Extension { .. } => Ok(()),
        }
    }
}

fn require_live(view: &dyn PackageView, package: PackageId) -> Result<PackageRecord, ApplyError> {
    let record = view
        .record(package)
        .ok_or(ApplyError::UnknownPackage(package))?;
    if !record.is_live() {
        return Err(ApplyError::NotLive(package));
    }
    Ok(record)
}

/// The delivery names an admitted edge from `source` to its receiver (I3).
fn verify_incidence(
    kernel: &Kernel,
    package: PackageId,
    source: &str,
    delivery: &Delivery,
) -> Result<(), ApplyError> {
    let admitted = kernel
        .graph()
        .edge(delivery.edge_id())
        .is_some_and(|edge| edge.source() == source && edge.target() == delivery.receiver());
    if admitted {
        Ok(())
    } else {
        Err(ApplyError::EdgeIncidence(package))
    }
}

fn verify_retirement(
    view: &dyn PackageView,
    package: PackageId,
    record: &PackageRecord,
    retirement: &Retirement,
    successor: u64,
) -> Result<(), ApplyError> {
    debug_assert_eq!(retirement.revision(), successor);
    if !retirement.admits(record.phase()) {
        return Err(ApplyError::RetirementInconsistent(package));
    }
    if let Some(evidence) = retirement.evidence()
        && !view.activation_known(evidence)
    {
        return Err(ApplyError::UnknownEvidence(evidence));
    }
    Ok(())
}

fn verify_activation(
    kernel: &Kernel,
    view: &dyn PackageView,
    id: ActivationId,
    activation: &Activation,
    outputs: &[(PackageId, PackageRecord)],
    inputs: &BTreeMap<PackageId, PackageRecord>,
) -> Result<(), ApplyError> {
    if view.activation_known(id) {
        return Err(ApplyError::ActivationExists(id));
    }
    // The evaluator admitted the recorded node against the same definition
    // `verify` checked above, so it is a node of the graph.
    debug_assert!(
        kernel.graph().node(activation.node_id()).is_some(),
        "an activation executes at a node of the graph"
    );
    // The executing node: a root's declared node, or the common holder of the
    // consumed inputs, which must all be live and delivered there (I2).
    let node: Arc<str> = match &activation.trigger {
        Trigger::Orig { node_id, .. } => Arc::clone(node_id),
        Trigger::Pkgs { package_ids } => {
            let mut holder: Option<Arc<str>> = None;
            let mut authority: Option<Authority> = None;
            for package in package_ids {
                let record = require_live(view, *package)?;
                let Some(delivery) = &record.delivery else {
                    return Err(ApplyError::NotDelivered(*package));
                };
                match &holder {
                    None => holder = Some(Arc::clone(&delivery.receiver)),
                    Some(current) if *current == delivery.receiver => {}
                    Some(_) => return Err(ApplyError::InputCustody(id)),
                }
                if authority.as_ref().is_some_and(|a| a != record.authority()) {
                    return Err(ApplyError::InputAuthority(id));
                }
                authority = Some(record.authority().clone());
            }
            holder.ok_or(ApplyError::InputCustody(id))?
        }
    };
    if node != activation.node_id {
        return Err(ApplyError::ExecutionNode(id));
    }
    for (package, expected) in inputs {
        if view.record(*package).as_ref() != Some(expected) {
            return Err(ApplyError::InputRecordMismatch(*package));
        }
    }
    debug_assert!(
        outputs.len() == activation.outputs.len()
            && outputs
                .iter()
                .map(|(package, _)| package)
                .collect::<BTreeSet<_>>()
                == activation.outputs.keys().collect::<BTreeSet<_>>(),
        "an activation transition carries one record per output"
    );
    for (package, record) in outputs {
        let Some(output) = activation.outputs.get(package) else {
            return Err(ApplyError::OutputMismatch(*package));
        };
        // At birth a record is delivered exactly when its output names a
        // delivery edge, on that edge, from the executing node (I1, I3).
        if package.producer() != id
            || !record.is_live()
            || record.object_type != output.object_type
            || record.authority != output.authority
            || record.content_digest != output.content_digest
            || record.producer_node != node
            || output.edge_id.as_ref() != record.delivery.as_ref().map(|delivery| &delivery.edge_id)
        {
            return Err(ApplyError::OutputMismatch(*package));
        }
        if let Some(delivery) = &record.delivery {
            verify_incidence(kernel, *package, &node, delivery)?;
        }
    }
    Ok(())
}

fn verify_rewrite(
    kernel: &Kernel,
    view: &dyn FrontierView,
    transition: &Transition,
) -> Result<(), ApplyError> {
    let TransitionKind::Rewrite {
        retirements,
        fresh_node_ids,
        fresh_edge_ids,
        next_nodes,
        next_all_routes,
        ..
    } = &transition.kind
    else {
        unreachable!("rewrite verification requires a rewrite transition");
    };
    let successor = transition.successor_revision();
    let used_node_ids = view.used_node_ids();
    let used_edge_ids = view.used_edge_ids();
    for id in fresh_node_ids {
        if id.is_empty() || used_node_ids.contains(id) {
            return Err(ApplyError::IdentityReused(Arc::clone(id)));
        }
    }
    for id in fresh_edge_ids {
        if id.is_empty() || used_edge_ids.contains(id) {
            return Err(ApplyError::IdentityReused(Arc::clone(id)));
        }
    }
    debug_assert!(
        next_nodes
            .iter()
            .all(|id| kernel.graph().node(id).is_some() || fresh_node_ids.contains(id)),
        "a replacement graph consists of current and fresh nodes"
    );
    let mut retired = BTreeSet::new();
    for (package, retirement) in retirements {
        debug_assert_ne!(retirement.reason(), RetirementReason::Explicit);
        let inserted = retired.insert(*package);
        debug_assert!(inserted, "cleanup retires a package once");
        let record = require_live(view, *package)?;
        if retirement.reason() == RetirementReason::HolderRemoved
            && next_nodes.contains(record.holder())
        {
            return Err(ApplyError::RetirementInconsistent(*package));
        }
        verify_retirement(view, *package, &record, retirement, successor)?;
    }
    // Every package still live afterwards is held by a node of the next graph (I5).
    for (package, record) in view.live() {
        if !retired.contains(&package) && !next_nodes.contains(record.holder()) {
            return Err(ApplyError::StrandedHolder(package));
        }
        if !retired.contains(&package)
            && let Some(routes) = next_all_routes.get(record.holder())
            && let Some(delivery) = record.delivery()
            && !routes.contains(delivery.edge_id())
        {
            return Err(ApplyError::ObsoleteReceipt(package));
        }
    }
    Ok(())
}

/// A precondition of [`Transition::verify`] failed. The state is unchanged.
///
/// Includes stale or unfaithful view errors, wrong-kernel errors, and
/// defensive checks on the sealed evaluator output.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum ApplyError {
    /// The transition was evaluated against another definition version than
    /// the kernel applying it.
    #[error("transition definition does not match the applying kernel")]
    DefinitionMismatch,
    /// The transition was evaluated against a different state.
    #[error("transition binding does not match the state")]
    BindingMismatch,
    /// The activation identity is already accepted.
    #[error("activation already exists: {0}")]
    ActivationExists(ActivationId),
    /// A referenced package is not recorded.
    #[error("unknown package: {0}")]
    UnknownPackage(PackageId),
    /// An output record disagrees with its activation's output or its owner.
    #[error("output record is inconsistent with its activation: {0}")]
    OutputMismatch(PackageId),
    /// A delivery names no admitted edge from the producer's node to its receiver.
    #[error("delivery of {0} does not match an admitted edge")]
    EdgeIncidence(PackageId),
    /// An activation's inputs are absent or are not all held at one node.
    #[error("activation {0} inputs are not held together at one node")]
    InputCustody(ActivationId),
    /// Join inputs do not carry one governing authority.
    #[error("activation {0} inputs carry different authorities")]
    InputAuthority(ActivationId),
    /// The node proved during evaluation differs from the true trigger node.
    #[error("activation {0} execution node differs from its trigger")]
    ExecutionNode(ActivationId),
    /// Input metadata differs from the record whose admission was proved.
    #[error("package {0} differs from its evaluated input record")]
    InputRecordMismatch(PackageId),
    /// A surviving live receipt at an `All` node has lost its incoming route.
    #[error("live receipt {0} names a removed route at an All receiver")]
    ObsoleteReceipt(PackageId),
    /// The package is not on the frontier.
    #[error("package is not live: {0}")]
    NotLive(PackageId),
    /// The package has not been delivered.
    #[error("package is not delivered: {0}")]
    NotDelivered(PackageId),
    /// The package was already delivered.
    #[error("package is already delivered: {0}")]
    AlreadyDelivered(PackageId),
    /// A retirement's reason does not admit the package's phase or evidence.
    #[error("retirement of {0} is inconsistent with its phase or evidence")]
    RetirementInconsistent(PackageId),
    /// Retirement evidence names no accepted activation.
    #[error("retirement evidence is not an accepted activation: {0}")]
    UnknownEvidence(ActivationId),
    /// A fresh identity was used before in this workflow.
    #[error("identity was already used in this workflow: {0}")]
    IdentityReused(Arc<str>),
    /// A package would stay live at a node the replacement graph lacks.
    #[error("package {0} would remain live at a removed node")]
    StrandedHolder(PackageId),
}

/// Read access to package records and accepted activations.
pub trait PackageView {
    /// Returns the record of one package, whatever its status.
    fn record(&self, package: PackageId) -> Option<PackageRecord>;
    /// Reports whether an activation is accepted.
    fn activation_known(&self, activation: ActivationId) -> bool;
    /// Returns the exact-state binding.
    fn binding(&self) -> Binding;
}

/// Read access to the whole live frontier and lifetime identities.
pub trait FrontierView: PackageView {
    /// Returns every live package with its record.
    fn live(&self) -> Vec<(PackageId, PackageRecord)>;
    /// Returns every node identity ever admitted.
    fn used_node_ids(&self) -> BTreeSet<Arc<str>>;
    /// Returns every edge identity ever admitted.
    fn used_edge_ids(&self) -> BTreeSet<Arc<str>>;
}

impl PackageView for State {
    fn record(&self, package: PackageId) -> Option<PackageRecord> {
        self.packages.get(&package).cloned()
    }

    fn activation_known(&self, activation: ActivationId) -> bool {
        self.activations.contains_key(&activation)
    }

    fn binding(&self) -> Binding {
        Self::binding(self)
    }
}

impl FrontierView for State {
    fn live(&self) -> Vec<(PackageId, PackageRecord)> {
        Self::live(self)
            .map(|(id, record)| (id, record.clone()))
            .collect()
    }

    fn used_node_ids(&self) -> BTreeSet<Arc<str>> {
        self.used_node_ids.clone()
    }

    fn used_edge_ids(&self) -> BTreeSet<Arc<str>> {
        self.used_edge_ids.clone()
    }
}

impl State {
    /// Applies one evaluated transition, or rejects it leaving the state unchanged.
    ///
    /// [`Transition::verify`] runs against this state and `kernel` before any
    /// mutation. On success the revision advances by exactly one and the nonce
    /// is refreshed.
    ///
    /// # Errors
    ///
    /// Returns [`ApplyError`] naming the first failed precondition.
    pub fn apply(&mut self, kernel: &Kernel, transition: &Transition) -> Result<(), ApplyError> {
        transition.verify(kernel, self)?;
        let revision = transition.successor_revision();
        if transition.next_fingerprint().is_some() {
            self.definition_changes += 1;
        }
        match &transition.kind {
            TransitionKind::Activation {
                id,
                activation,
                outputs,
                ..
            } => {
                for package in activation.inputs().into_iter().flatten() {
                    self.record_mut(*package).status = PackageStatus::Consumed(*id);
                    self.live.remove(package);
                }
                self.activations.insert(*id, activation.clone());
                for (package, record) in outputs {
                    self.packages.insert(*package, record.clone());
                    self.live.insert(*package);
                }
            }
            TransitionKind::Transfer {
                package, delivery, ..
            } => {
                self.record_mut(*package).delivery = Some(delivery.clone());
            }
            TransitionKind::Retire {
                package,
                retirement,
            } => self.retire_record(*package, retirement),
            TransitionKind::Rewrite {
                retirements,
                fresh_node_ids,
                fresh_edge_ids,
                next_fingerprint,
                ..
            } => {
                for (package, retirement) in retirements {
                    self.retire_record(*package, retirement);
                }
                self.used_node_ids.extend(fresh_node_ids.iter().cloned());
                self.used_edge_ids.extend(fresh_edge_ids.iter().cloned());
                self.definition_fingerprint = *next_fingerprint;
            }
            TransitionKind::Extension { next_fingerprint } => {
                self.definition_fingerprint = *next_fingerprint;
            }
        }
        self.revision = revision;
        self.nonce = fresh_nonce();
        Ok(())
    }

    fn retire_record(&mut self, package: PackageId, retirement: &Retirement) {
        self.record_mut(package).status = PackageStatus::Retired(retirement.clone());
        self.live.remove(&package);
    }

    fn record_mut(&mut self, package: PackageId) -> &mut PackageRecord {
        self.packages
            .get_mut(&package)
            .expect("verify checked that the package is recorded")
    }
}
