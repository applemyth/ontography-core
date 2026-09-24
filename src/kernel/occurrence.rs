//! Canonical occurrence records and definition-bound state.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use uuid::Uuid;

use super::admission_api::StateRestoreError;
use super::frontier::{Delivery, Phase, Position};
use crate::graph::{Authority, ContentDigest, DefinitionFingerprint, DefinitionId, Payload};

/// Opaque identity of one activation occurrence.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ActivationId(u128);

impl ActivationId {
    pub(crate) fn fresh() -> Self {
        Self(Uuid::new_v4().as_u128())
    }

    /// Reconstructs an activation identity from its durable integer form.
    #[must_use]
    pub const fn from_u128(value: u128) -> Self {
        Self(value)
    }

    /// Returns the durable integer form of this activation identity.
    #[must_use]
    pub const fn as_u128(self) -> u128 {
        self.0
    }
}

impl fmt::Display for ActivationId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        Uuid::from_u128(self.0).fmt(formatter)
    }
}

impl fmt::Debug for ActivationId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("ActivationId")
            .field(&Uuid::from_u128(self.0))
            .finish()
    }
}

/// Identity of one package occurrence, independent of its eventual delivery edge.
///
/// A package is an output occurrence owned by its producing activation. Its
/// identity therefore contains both the producer and an opaque producer-local
/// output identity.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct PackageId {
    producer: ActivationId,
    output: u128,
}

impl Ord for PackageId {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.producer, self.output).cmp(&(other.producer, other.output))
    }
}

impl PartialOrd for PackageId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PackageId {
    /// Reconstructs a durable package identity.
    #[must_use]
    pub const fn from_parts(producer: ActivationId, output: u128) -> Self {
        Self { producer, output }
    }

    /// Returns the activation that produced this package occurrence.
    #[must_use]
    pub const fn producer(self) -> ActivationId {
        self.producer
    }

    /// Returns the producer-local durable output identity.
    #[must_use]
    pub const fn output(self) -> u128 {
        self.output
    }
}

impl fmt::Display for PackageId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}/{}",
            self.producer,
            Uuid::from_u128(self.output)
        )
    }
}

impl fmt::Debug for PackageId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PackageId")
            .field("producer", &self.producer)
            .field("output", &Uuid::from_u128(self.output))
            .finish()
    }
}

/// A derived package view, including its last holder and optional delivery edge.
///
/// Current liveness and phase are authoritative only in [`State::positions`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Package {
    pub(crate) edge_id: Option<Arc<str>>,
    pub(crate) object_type: Arc<str>,
    pub(crate) authority: Authority,
    pub(crate) content_digest: ContentDigest,
    pub(crate) node_id: Arc<str>,
}

impl Package {
    /// Returns the historical delivery edge, or `None` before delivery.
    #[must_use]
    pub fn edge_id(&self) -> Option<&str> {
        self.edge_id.as_deref()
    }

    /// Returns the immutable package object type.
    #[must_use]
    pub fn object_type(&self) -> &str {
        &self.object_type
    }

    /// Returns the tagged authority carried by this package.
    #[must_use]
    pub const fn authority(&self) -> &Authority {
        &self.authority
    }

    /// Returns the immutable commitment to the package payload.
    #[must_use]
    pub const fn content_digest(&self) -> ContentDigest {
        self.content_digest
    }

    /// Returns the last holder; consult the frontier for current liveness.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }
}

/// Root or package trigger of an accepted activation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Trigger {
    /// A nullary root activation carrying its initial authority.
    Orig {
        /// Executing static graph node.
        node_id: Arc<str>,
        /// Initial authority governing this activation.
        authority: Authority,
    },
    /// An activation atomically consuming one or more package occurrences.
    Pkgs {
        /// Non-empty canonical set of consumed packages.
        package_ids: BTreeSet<PackageId>,
    },
}

impl Trigger {
    /// Borrows the non-empty package input set, or `None` for a root.
    #[must_use]
    pub const fn inputs(&self) -> Option<&BTreeSet<PackageId>> {
        match self {
            Self::Orig { .. } => None,
            Self::Pkgs { package_ids } => Some(package_ids),
        }
    }
}

/// One produced package and the concrete static edge it realizes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EdgeUse {
    package_id: PackageId,
    edge_id: Arc<str>,
}

impl EdgeUse {
    /// Returns the produced package occurrence.
    #[must_use]
    pub const fn package_id(&self) -> PackageId {
        self.package_id
    }

    /// Returns the realized concrete edge.
    #[must_use]
    pub fn edge_id(&self) -> &str {
        &self.edge_id
    }
}

/// One accepted digest-bearing package output owned by an activation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Output {
    pub(super) edge_id: Option<Arc<str>>,
    pub(super) object_type: Arc<str>,
    pub(super) authority: Authority,
    pub(super) content_digest: ContentDigest,
}

impl Output {
    /// Reconstructs an output record for later validation by
    /// [`crate::Kernel::restore_state`], which must receive matching payload evidence.
    #[must_use]
    pub fn new(
        edge_id: impl Into<Arc<str>>,
        object_type: impl Into<Arc<str>>,
        authority: Authority,
        content_digest: ContentDigest,
    ) -> Self {
        Self {
            edge_id: Some(edge_id.into()),
            object_type: object_type.into(),
            authority,
            content_digest,
        }
    }

    /// Reconstructs an outbound birth for subsequent validated restoration.
    #[must_use]
    pub fn outbound(
        object_type: impl Into<Arc<str>>,
        authority: Authority,
        content_digest: ContentDigest,
    ) -> Self {
        Self {
            edge_id: None,
            object_type: object_type.into(),
            authority,
            content_digest,
        }
    }

    /// Returns an immediate delivery edge; later transfers are recorded separately.
    #[must_use]
    pub fn edge_id(&self) -> Option<&str> {
        self.edge_id.as_deref()
    }

    /// Returns the immutable package object type.
    #[must_use]
    pub fn object_type(&self) -> &str {
        &self.object_type
    }

    /// Returns the tagged authority carried by the package occurrence.
    #[must_use]
    pub const fn authority(&self) -> &Authority {
        &self.authority
    }

    /// Returns the commitment to the package payload.
    #[must_use]
    pub const fn content_digest(&self) -> ContentDigest {
        self.content_digest
    }
}

/// One complete accepted activation vertex.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Activation {
    pub(super) trigger: Trigger,
    pub(super) result: Payload,
    pub(super) outputs: BTreeMap<PackageId, Output>,
}

impl Activation {
    /// Reconstructs an activation record for later validation by
    /// [`crate::Kernel::restore_state`].
    #[must_use]
    pub fn new(trigger: Trigger, result: Payload, outputs: BTreeMap<PackageId, Output>) -> Self {
        Self {
            trigger,
            result,
            outputs,
        }
    }

    /// Returns the root or package trigger.
    #[must_use]
    pub const fn trigger(&self) -> &Trigger {
        &self.trigger
    }

    /// Returns the activation-local result.
    #[must_use]
    pub const fn result(&self) -> &Payload {
        &self.result
    }

    /// Returns the activation-owned package outputs.
    #[must_use]
    pub const fn package_outputs(&self) -> &BTreeMap<PackageId, Output> {
        &self.outputs
    }

    /// Borrows the activation's non-empty package input set, or `None` for a root.
    #[must_use]
    pub const fn inputs(&self) -> Option<&BTreeSet<PackageId>> {
        self.trigger.inputs()
    }

    /// Projects packages delivered atomically with this activation and their edges.
    /// Later explicit transfers appear in [`State::edge_uses`].
    pub fn edge_uses(&self) -> impl Iterator<Item = EdgeUse> + '_ {
        self.outputs.iter().filter_map(|(package_id, output)| {
            output.edge_id.as_ref().map(|edge_id| EdgeUse {
                package_id: *package_id,
                edge_id: Arc::clone(edge_id),
            })
        })
    }

    /// Projects the finite set of output package occurrences.
    #[must_use]
    pub fn outputs(&self) -> impl ExactSizeIterator<Item = PackageId> + '_ {
        self.outputs.keys().copied()
    }
}

/// Current frontier and accepted activation history.
///
/// Package and consumer collections are derived historical views.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State {
    pub(super) definition_id: DefinitionId,
    pub(super) definition_fingerprint: DefinitionFingerprint,
    pub(super) activations: BTreeMap<ActivationId, Activation>,
    pub(super) packages: BTreeMap<PackageId, Package>,
    pub(super) consumed_by: BTreeMap<PackageId, ActivationId>,
    pub(super) positions: BTreeMap<PackageId, Position>,
    pub(super) deliveries: BTreeMap<PackageId, Delivery>,
    pub(super) revision: u64,
    pub(super) used_node_ids: BTreeSet<Arc<str>>,
    pub(super) used_edge_ids: BTreeSet<Arc<str>>,
}

/// Accepted activation records for validation under one fixed graph.
///
/// This format omits native graph rewrites and explicit transfers. The checked
/// state export methods reject states containing either operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateParts {
    pub(super) definition_id: DefinitionId,
    pub(super) definition_fingerprint: DefinitionFingerprint,
    pub(super) activations: BTreeMap<ActivationId, Activation>,
}

/// One kernel-admitted extension awaiting atomic installation by a state owner.
pub(crate) struct AdmissionDelta {
    pub(crate) id: ActivationId,
    pub(crate) node_id: Arc<str>,
    pub(crate) package_targets: Vec<(PackageId, Arc<str>)>,
    pub(crate) deliveries: BTreeMap<PackageId, Delivery>,
    pub(crate) activation: Activation,
}

impl StateParts {
    /// Constructs untrusted activation records for fixed-graph validation.
    #[must_use]
    pub const fn new(
        definition_id: DefinitionId,
        definition_fingerprint: DefinitionFingerprint,
        activations: BTreeMap<ActivationId, Activation>,
    ) -> Self {
        Self {
            definition_id,
            definition_fingerprint,
            activations,
        }
    }

    /// Returns the persisted workflow-definition identity.
    #[must_use]
    pub const fn definition_id(&self) -> &DefinitionId {
        &self.definition_id
    }

    /// Returns the persisted static-definition fingerprint.
    #[must_use]
    pub const fn definition_fingerprint(&self) -> &DefinitionFingerprint {
        &self.definition_fingerprint
    }

    /// Returns the canonical activation records.
    #[must_use]
    pub const fn activations(&self) -> &BTreeMap<ActivationId, Activation> {
        &self.activations
    }
}

impl State {
    /// Returns the stable workflow-definition identity.
    #[must_use]
    pub const fn definition_id(&self) -> &DefinitionId {
        &self.definition_id
    }

    /// Returns the fingerprint of the current graph definition.
    #[must_use]
    pub const fn definition_fingerprint(&self) -> &DefinitionFingerprint {
        &self.definition_fingerprint
    }

    /// Returns historical package views, including consumed and retired packages.
    #[must_use]
    pub const fn packages(&self) -> &BTreeMap<PackageId, Package> {
        &self.packages
    }

    /// Returns the canonical activation vertices.
    #[must_use]
    pub const fn activations(&self) -> &BTreeMap<ActivationId, Activation> {
        &self.activations
    }

    /// Clones accepted activation records for fixed-graph persistence.
    ///
    /// # Errors
    /// Rejects states changed by rewriting or explicit transfer.
    pub fn to_parts(&self) -> Result<StateParts, StateRestoreError> {
        self.check_fixed_history()?;
        Ok(StateParts::new(
            self.definition_id.clone(),
            self.definition_fingerprint,
            self.activations.clone(),
        ))
    }

    /// Consumes this state into accepted records for fixed-graph persistence.
    ///
    /// # Errors
    /// Rejects states changed by rewriting or explicit transfer.
    pub fn into_parts(self) -> Result<StateParts, StateRestoreError> {
        self.check_fixed_history()?;
        Ok(StateParts::new(
            self.definition_id,
            self.definition_fingerprint,
            self.activations,
        ))
    }

    pub(crate) fn check_fixed_history(&self) -> Result<(), StateRestoreError> {
        if usize::try_from(self.revision).ok() != Some(self.activations.len()) {
            return Err(StateRestoreError::UnsupportedDynamicState);
        }
        Ok(())
    }

    /// Looks up a historical package occurrence, including consumed or retired work.
    #[must_use]
    pub fn package(&self, id: PackageId) -> Option<&Package> {
        self.packages.get(&id)
    }

    /// Looks up an activation vertex.
    #[must_use]
    pub fn activation(&self, id: ActivationId) -> Option<&Activation> {
        self.activations.get(&id)
    }

    /// Returns the producer encoded by a known package identity.
    #[must_use]
    pub fn package_producer(&self, id: PackageId) -> Option<ActivationId> {
        self.packages.contains_key(&id).then_some(id.producer())
    }

    /// Returns the activation that consumed a package, if any.
    #[must_use]
    pub fn package_consumer(&self, id: PackageId) -> Option<ActivationId> {
        self.consumed_by.get(&id).copied()
    }

    /// Returns every live package's authoritative holder and phase.
    #[must_use]
    pub const fn positions(&self) -> &BTreeMap<PackageId, Position> {
        &self.positions
    }

    /// Returns one live package's authoritative position.
    #[must_use]
    pub fn position(&self, package_id: PackageId) -> Option<&Position> {
        self.positions.get(&package_id)
    }

    /// Returns accepted transfer provenance, including for retired/consumed packages.
    #[must_use]
    pub const fn deliveries(&self) -> &BTreeMap<PackageId, Delivery> {
        &self.deliveries
    }

    /// Returns the monotone revision of this state.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Reports whether no package remains live.
    #[must_use]
    pub fn is_quiescent(&self) -> bool {
        self.positions.is_empty()
    }

    /// Projects every realized static edge occurrence.
    pub fn edge_uses(&self) -> impl Iterator<Item = (ActivationId, EdgeUse)> + '_ {
        self.deliveries.iter().map(|(package_id, delivery)| {
            (
                package_id.producer(),
                EdgeUse {
                    package_id: *package_id,
                    edge_id: delivery.edge_id.clone(),
                },
            )
        })
    }

    pub(super) fn commit(&mut self, admitted: AdmissionDelta) -> ActivationId {
        let AdmissionDelta {
            id: activation_id,
            node_id,
            package_targets,
            deliveries,
            activation,
        } = admitted;

        let next_revision = self
            .revision
            .checked_add(1)
            .expect("admission proved available revision");

        assert!(
            !self.activations.contains_key(&activation_id),
            "accepted activation identity must be fresh"
        );
        assert!(
            activation
                .outputs()
                .all(|package_id| package_id.producer() == activation_id),
            "every output identity must name its owning activation"
        );
        assert_eq!(
            activation.package_outputs().len(),
            package_targets.len(),
            "derived package index must equal activation-owned outputs"
        );
        assert!(
            activation
                .package_outputs()
                .keys()
                .copied()
                .eq(package_targets.iter().map(|(package_id, _)| *package_id)),
            "derived package index must equal activation-owned outputs"
        );
        for (package_id, _) in &package_targets {
            assert!(
                !self.packages.contains_key(package_id),
                "accepted package identity must be fresh"
            );
        }
        if let Some(inputs) = activation.inputs() {
            for package_id in inputs {
                assert!(
                    self.positions.get(package_id).is_some_and(|position| {
                        position.phase == Phase::In && position.holder == node_id
                    }),
                    "admission proved every input is delivered at the executing incarnation"
                );
                assert!(
                    !self.consumed_by.contains_key(package_id),
                    "admission proved unique input consumption"
                );
            }
        }

        for ((package_id, output), (_, holder)) in
            activation.package_outputs().iter().zip(package_targets)
        {
            let phase = if deliveries.contains_key(package_id) {
                Phase::In
            } else {
                Phase::Out
            };
            let previous = self.packages.insert(
                *package_id,
                Package {
                    edge_id: output.edge_id.clone(),
                    object_type: output.object_type.clone(),
                    authority: output.authority.clone(),
                    content_digest: output.content_digest,
                    node_id: holder.clone(),
                },
            );
            assert!(previous.is_none(), "admission proved package freshness");
            self.positions
                .insert(*package_id, Position { holder, phase });
        }
        self.deliveries.extend(deliveries);
        let previous = self.activations.insert(activation_id, activation);
        assert!(previous.is_none(), "admission proved activation freshness");
        let activation = self
            .activations
            .get(&activation_id)
            .expect("accepted activation was just inserted");
        if let Some(inputs) = activation.inputs() {
            for package_id in inputs {
                let previous = self.consumed_by.insert(*package_id, activation_id);
                assert!(previous.is_none(), "admission proved pending input");
                self.positions.remove(package_id);
            }
        }
        self.revision = next_revision;
        activation_id
    }
}
