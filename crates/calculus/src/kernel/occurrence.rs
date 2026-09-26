//! Canonical occurrence records and definition-bound state.
//!
//! Every package has exactly one [`PackageRecord`] whose [`PackageStatus`] is
//! a sum type: a package is live, consumed, or retired by construction. The
//! live frontier is a derived index maintained by [`State::apply`].

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use uuid::Uuid;

use super::admission_api::StateRestoreError;
use super::frontier::{Delivery, Phase, Position, Retirement};
use super::transition::Binding;
use crate::graph::{Authority, ContentDigest, DefinitionFingerprint, DefinitionId, Payload};

/// Opaque identity of one activation occurrence.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ActivationId(u128);

impl ActivationId {
    /// Mints a fresh random activation identity. The kernel mints identities
    /// for the activations it commits in memory; a storage adapter mints the
    /// identity it will commit and lets the kernel verify it is unused.
    #[must_use]
    pub fn fresh() -> Self {
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

/// The exclusive lifecycle status of one package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageStatus {
    /// On the frontier: awaiting transfer or awaiting consumption.
    Live,
    /// Consumed as an input of the named activation.
    Consumed(ActivationId),
    /// Removed from the frontier without consumption.
    Retired(Retirement),
}

/// The single canonical record of one package occurrence.
///
/// The immutable fields are fixed at birth. `delivery` is set at most once,
/// at birth or by one transfer. `status` is the package's exclusive lifecycle
/// state. Holder and phase are derived: a delivered package is held by its
/// receiver in phase `In`; an undelivered one by its producer node in phase
/// `Out`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageRecord {
    pub(crate) object_type: Arc<str>,
    pub(crate) authority: Authority,
    pub(crate) content_digest: ContentDigest,
    pub(crate) producer_node: Arc<str>,
    pub(crate) delivery: Option<Delivery>,
    pub(crate) status: PackageStatus,
}

impl PackageRecord {
    /// Reconstructs a package record from durable fields.
    ///
    /// Adapters use this to decode stored rows. Consistency with the
    /// producing activation is checked by [`crate::Kernel::restore_checkpoint`].
    #[must_use]
    pub fn new(
        object_type: impl Into<Arc<str>>,
        authority: Authority,
        content_digest: ContentDigest,
        producer_node: impl Into<Arc<str>>,
        delivery: Option<Delivery>,
        status: PackageStatus,
    ) -> Self {
        Self {
            object_type: object_type.into(),
            authority,
            content_digest,
            producer_node: producer_node.into(),
            delivery,
            status,
        }
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

    /// Returns the node incarnation that produced this package.
    #[must_use]
    pub fn producer_node(&self) -> &str {
        &self.producer_node
    }

    /// Returns the single admitted delivery, or `None` while undelivered.
    #[must_use]
    pub const fn delivery(&self) -> Option<&Delivery> {
        self.delivery.as_ref()
    }

    /// Returns the exclusive lifecycle status.
    #[must_use]
    pub const fn status(&self) -> &PackageStatus {
        &self.status
    }

    /// Reports whether the package is on the frontier.
    #[must_use]
    pub const fn is_live(&self) -> bool {
        matches!(self.status, PackageStatus::Live)
    }

    /// Returns the consuming activation, if consumed.
    #[must_use]
    pub const fn consumer(&self) -> Option<ActivationId> {
        match self.status {
            PackageStatus::Consumed(consumer) => Some(consumer),
            PackageStatus::Live | PackageStatus::Retired(_) => None,
        }
    }

    /// Returns the retirement record, if retired.
    #[must_use]
    pub const fn retirement(&self) -> Option<&Retirement> {
        match &self.status {
            PackageStatus::Retired(retirement) => Some(retirement),
            PackageStatus::Live | PackageStatus::Consumed(_) => None,
        }
    }

    /// Returns the node incarnation currently or last holding the package.
    #[must_use]
    pub fn holder(&self) -> &str {
        self.delivery
            .as_ref()
            .map_or(&self.producer_node, |delivery| &delivery.receiver)
    }

    /// Returns whether the package is awaiting transfer or has been delivered.
    #[must_use]
    pub const fn phase(&self) -> Phase {
        if self.delivery.is_some() {
            Phase::In
        } else {
            Phase::Out
        }
    }

    /// Returns the derived holder and phase.
    #[must_use]
    pub fn position(&self) -> Position {
        Position::new(self.holder(), self.phase())
    }
}

/// Root or package trigger of an activation.
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

/// One accepted digest-bearing package output owned by an activation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Output {
    pub(crate) edge_id: Option<Arc<str>>,
    pub(crate) object_type: Arc<str>,
    pub(crate) authority: Authority,
    pub(crate) content_digest: ContentDigest,
}

impl Output {
    /// Reconstructs an output delivered at birth, for later validation by
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

    /// Returns the edge of an immediate delivery; later transfers appear on the record.
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
    pub(crate) trigger: Trigger,
    pub(crate) result: Payload,
    pub(crate) outputs: BTreeMap<PackageId, Output>,
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

    /// Projects the finite set of output package occurrences.
    #[must_use]
    pub fn outputs(&self) -> impl ExactSizeIterator<Item = PackageId> + '_ {
        self.outputs.keys().copied()
    }
}

/// Current frontier and accepted activation history.
///
/// `packages` holds one record per package; `live` is the derived index of
/// records whose status is [`PackageStatus::Live`]. Only [`State::apply`]
/// mutates a state.
#[derive(Clone, Debug)]
pub struct State {
    pub(crate) definition_id: DefinitionId,
    pub(crate) definition_fingerprint: DefinitionFingerprint,
    pub(crate) activations: BTreeMap<ActivationId, Activation>,
    pub(crate) packages: BTreeMap<PackageId, PackageRecord>,
    pub(crate) live: BTreeSet<PackageId>,
    pub(crate) used_node_ids: BTreeSet<Arc<str>>,
    pub(crate) used_edge_ids: BTreeSet<Arc<str>>,
    pub(crate) revision: u64,
    pub(crate) nonce: u128,
}

/// Equality of content. The nonce is an identity fence, not content, and two
/// states with equal content compare equal whatever their nonces.
impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.definition_id == other.definition_id
            && self.definition_fingerprint == other.definition_fingerprint
            && self.revision == other.revision
            && self.activations == other.activations
            && self.packages == other.packages
            && self.live == other.live
            && self.used_node_ids == other.used_node_ids
            && self.used_edge_ids == other.used_edge_ids
    }
}

impl Eq for State {}

/// Accepted activation records for validation under one fixed graph.
///
/// This format omits graph rewrites, explicit transfers, retirements, and
/// vocabulary extensions. The checked state export rejects states containing
/// any of them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateParts {
    pub(crate) definition_id: DefinitionId,
    pub(crate) definition_fingerprint: DefinitionFingerprint,
    pub(crate) activations: BTreeMap<ActivationId, Activation>,
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

pub(crate) fn fresh_nonce() -> u128 {
    Uuid::new_v4().as_u128()
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

    /// Returns the exact-state binding: definition, revision, and nonce.
    #[must_use]
    pub fn binding(&self) -> Binding {
        Binding {
            definition_id: self.definition_id.clone(),
            definition_fingerprint: self.definition_fingerprint,
            revision: self.revision,
            nonce: self.nonce,
        }
    }

    /// Returns every package record, including consumed and retired packages.
    #[must_use]
    pub const fn packages(&self) -> &BTreeMap<PackageId, PackageRecord> {
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
    /// Rejects states changed by rewriting, explicit transfer, retirement, or
    /// vocabulary extension.
    pub fn to_parts(&self) -> Result<StateParts, StateRestoreError> {
        self.check_fixed_history()?;
        Ok(StateParts::new(
            self.definition_id.clone(),
            self.definition_fingerprint,
            self.activations.clone(),
        ))
    }

    pub(crate) fn check_fixed_history(&self) -> Result<(), StateRestoreError> {
        if usize::try_from(self.revision).ok() != Some(self.activations.len()) {
            return Err(StateRestoreError::UnsupportedDynamicState);
        }
        Ok(())
    }

    /// Looks up a package record, including consumed or retired work.
    #[must_use]
    pub fn package(&self, id: PackageId) -> Option<&PackageRecord> {
        self.packages.get(&id)
    }

    /// Looks up an activation vertex.
    #[must_use]
    pub fn activation(&self, id: ActivationId) -> Option<&Activation> {
        self.activations.get(&id)
    }

    /// Returns the activation that consumed a package, if any.
    #[must_use]
    pub fn package_consumer(&self, id: PackageId) -> Option<ActivationId> {
        self.packages.get(&id).and_then(PackageRecord::consumer)
    }

    /// Returns one live package's holder and phase.
    #[must_use]
    pub fn position(&self, id: PackageId) -> Option<Position> {
        self.packages
            .get(&id)
            .filter(|record| record.is_live())
            .map(PackageRecord::position)
    }

    /// Returns every live package with its holder and phase, derived from
    /// the live index.
    #[must_use]
    pub fn positions(&self) -> BTreeMap<PackageId, Position> {
        self.live()
            .map(|(id, record)| (id, record.position()))
            .collect()
    }

    /// Returns every delivered package's delivery, whatever its status.
    #[must_use]
    pub fn deliveries(&self) -> BTreeMap<PackageId, Delivery> {
        self.packages
            .iter()
            .filter_map(|(id, record)| record.delivery().map(|delivery| (*id, delivery.clone())))
            .collect()
    }

    /// Returns every retired package's retirement record.
    #[must_use]
    pub fn retirements(&self) -> BTreeMap<PackageId, Retirement> {
        self.retired()
            .filter_map(|(id, record)| record.retirement().map(|r| (id, r.clone())))
            .collect()
    }

    /// Returns the producer encoded by a known package identity.
    #[must_use]
    pub fn package_producer(&self, id: PackageId) -> Option<ActivationId> {
        self.packages.contains_key(&id).then_some(id.producer())
    }

    /// Consumes this state into accepted records for fixed-graph persistence.
    ///
    /// # Errors
    /// Rejects states changed by rewriting, explicit transfer, retirement, or
    /// vocabulary extension.
    pub fn into_parts(self) -> Result<StateParts, StateRestoreError> {
        self.check_fixed_history()?;
        Ok(StateParts::new(
            self.definition_id,
            self.definition_fingerprint,
            self.activations,
        ))
    }

    /// Returns every live package record: the frontier.
    ///
    /// # Panics
    ///
    /// Panics if the live index names an unrecorded package, which no
    /// transition can produce.
    pub fn live(&self) -> impl Iterator<Item = (PackageId, &PackageRecord)> + '_ {
        self.live.iter().map(|id| {
            (
                *id,
                self.packages
                    .get(id)
                    .expect("the live index names only recorded packages"),
            )
        })
    }

    /// Returns every retired package record.
    pub fn retired(&self) -> impl Iterator<Item = (PackageId, &PackageRecord)> + '_ {
        self.packages
            .iter()
            .filter(|(_, record)| record.retirement().is_some())
            .map(|(id, record)| (*id, record))
    }

    /// Looks up one package's retirement record, if it was retired.
    #[must_use]
    pub fn retirement(&self, id: PackageId) -> Option<&Retirement> {
        self.packages.get(&id).and_then(PackageRecord::retirement)
    }

    /// Looks up one package's delivery, if it was delivered.
    #[must_use]
    pub fn delivery(&self, id: PackageId) -> Option<&Delivery> {
        self.packages.get(&id).and_then(PackageRecord::delivery)
    }

    /// Returns the monotone revision of this state.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Reports whether no package remains live.
    #[must_use]
    pub fn is_quiescent(&self) -> bool {
        self.live.is_empty()
    }

    /// Returns every node identity ever admitted in this workflow's lifetime.
    #[must_use]
    pub const fn used_node_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.used_node_ids
    }

    /// Returns every edge identity ever admitted in this workflow's lifetime.
    #[must_use]
    pub const fn used_edge_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.used_edge_ids
    }
}
