//! Package custody vocabulary and the local rewrite cleanup rule.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::occurrence::{ActivationId, PackageId, PackageRecord};

/// Whether a live package is awaiting transfer or has reached its receiver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Phase {
    /// Held at its producing node, awaiting one outgoing transfer.
    Out,
    /// Delivered to its receiver, possibly undergoing speculative processing.
    In,
}

/// The holder and phase of one live package, derived from its record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    holder: Arc<str>,
    phase: Phase,
}

impl Position {
    /// Identifies one package holder and its transfer phase.
    #[must_use]
    pub(crate) fn new(holder: impl Into<Arc<str>>, phase: Phase) -> Self {
        Self {
            holder: holder.into(),
            phase,
        }
    }

    /// Returns the node incarnation holding the package.
    #[must_use]
    pub fn holder(&self) -> &str {
        &self.holder
    }

    /// Returns whether transfer is pending or completed.
    #[must_use]
    pub const fn phase(&self) -> Phase {
        self.phase
    }
}

/// The single admitted delivery of one package: its edge and receiver.
///
/// The delivery source is always the record's producer node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Delivery {
    pub(crate) edge_id: Arc<str>,
    pub(crate) receiver: Arc<str>,
}

impl Delivery {
    /// Reconstructs a delivery from durable fields.
    #[must_use]
    pub fn new(edge_id: impl Into<Arc<str>>, receiver: impl Into<Arc<str>>) -> Self {
        Self {
            edge_id: edge_id.into(),
            receiver: receiver.into(),
        }
    }

    /// Returns the historical edge used for delivery.
    #[must_use]
    pub fn edge_id(&self) -> &str {
        &self.edge_id
    }

    /// Returns the receiving node incarnation.
    #[must_use]
    pub fn receiver(&self) -> &str {
        &self.receiver
    }
}

/// Why a package left the live frontier without being consumed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RetirementReason {
    /// Its node incarnation was deleted or replaced by a rewrite.
    HolderRemoved,
    /// A rewrite changed its producer's outgoing edges and none accepts it.
    NoAcceptingEdge,
    /// A rewrite removed the edge that delivered it to a surviving `All`
    /// receiver, so no current-edge join can ever include it.
    RouteRemoved,
    /// An admitted retire operation removed it.
    Explicit,
}

/// Canonical record of one package's departure from the live frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Retirement {
    pub(crate) reason: RetirementReason,
    pub(crate) revision: u64,
    pub(crate) evidence: Option<ActivationId>,
}

impl Retirement {
    /// Reconstructs a retirement from durable fields.
    #[must_use]
    pub const fn new(
        reason: RetirementReason,
        revision: u64,
        evidence: Option<ActivationId>,
    ) -> Self {
        Self {
            reason,
            revision,
            evidence,
        }
    }

    /// Returns why the package was retired.
    #[must_use]
    pub const fn reason(&self) -> RetirementReason {
        self.reason
    }

    /// Returns the state revision that recorded the retirement.
    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Returns the activation cited as evidence by an explicit retirement.
    #[must_use]
    pub const fn evidence(&self) -> Option<ActivationId> {
        self.evidence
    }

    /// Reports whether the reason admits the retired package's phase and
    /// whether evidence is permitted for the reason.
    #[must_use]
    pub const fn admits(&self, phase: Phase) -> bool {
        match self.reason {
            RetirementReason::HolderRemoved => self.evidence.is_none(),
            RetirementReason::NoAcceptingEdge => {
                matches!(phase, Phase::Out) && self.evidence.is_none()
            }
            RetirementReason::RouteRemoved => matches!(phase, Phase::In) && self.evidence.is_none(),
            RetirementReason::Explicit => true,
        }
    }
}

/// Classifies every live package after separately validated structural admission.
///
/// A package whose holder is deleted is retired as `HolderRemoved`. Otherwise
/// `accepts` decides an `Out` package (`NoAcceptingEdge` on `false`) and
/// `retains_receipt` decides an `In` package (`RouteRemoved` on `false`).
/// Surviving holders keep their identity, so retained packages keep their
/// positions unchanged. Returns exactly the retired packages.
pub(super) fn cleanup<'a, E>(
    live: impl IntoIterator<Item = (PackageId, &'a PackageRecord)>,
    deleted_nodes: &BTreeSet<Arc<str>>,
    mut accepts: impl FnMut(PackageId, &PackageRecord) -> Result<bool, E>,
    mut retains_receipt: impl FnMut(PackageId, &PackageRecord) -> Result<bool, E>,
) -> Result<BTreeMap<PackageId, RetirementReason>, E> {
    let mut retired = BTreeMap::new();
    for (package, record) in live {
        if deleted_nodes.contains(record.holder()) {
            retired.insert(package, RetirementReason::HolderRemoved);
            continue;
        }
        let (retained, reason) = match record.phase() {
            Phase::Out => (accepts(package, record)?, RetirementReason::NoAcceptingEdge),
            Phase::In => (
                retains_receipt(package, record)?,
                RetirementReason::RouteRemoved,
            ),
        };
        if !retained {
            retired.insert(package, reason);
        }
    }
    Ok(retired)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{Authority, ContentDigest};
    use crate::kernel::occurrence::PackageStatus;

    fn package(index: u128) -> PackageId {
        PackageId::from_parts(ActivationId::from_u128(1), index)
    }

    fn record(holder: &str, phase: Phase) -> PackageRecord {
        let delivery = match phase {
            Phase::Out => None,
            Phase::In => Some(Delivery::new("edge", holder)),
        };
        let producer = if phase == Phase::Out {
            holder
        } else {
            "producer"
        };
        PackageRecord::new(
            "type",
            Authority::default(),
            ContentDigest::compute(b""),
            producer,
            delivery,
            PackageStatus::Live,
        )
    }

    /// Every frontier of up to two packages over two holders, every deletion
    /// set, and every acceptance and receipt decision: the result partitions
    /// the frontier by the stated rule and a second pass retires nothing.
    #[test]
    fn exhaustive_two_package_cleanup_matches_partition_and_idempotence() {
        let holders = [Arc::<str>::from("a"), Arc::from("b")];
        let positions = [
            None,
            Some(("a", Phase::Out)),
            Some(("a", Phase::In)),
            Some(("b", Phase::Out)),
            Some(("b", Phase::In)),
        ];
        let mut worlds = 0;
        for deletion in 0_u8..4 {
            let deleted: BTreeSet<Arc<str>> = holders
                .iter()
                .enumerate()
                .filter(|(index, _)| deletion & (1 << index) != 0)
                .map(|(_, holder)| Arc::clone(holder))
                .collect();
            for masks in 0_u16..256 {
                let (acceptance, receipts) = (masks & 15, masks >> 4);
                let bit = |record: &PackageRecord, p: PackageId| -> u16 {
                    1 << (u128::from(record.holder() != "a") * 2 + p.output())
                };
                let accepts = |p: PackageId, r: &PackageRecord| -> Result<bool, ()> {
                    Ok(acceptance & bit(r, p) != 0)
                };
                let retains = |p: PackageId, r: &PackageRecord| -> Result<bool, ()> {
                    Ok(receipts & bit(r, p) != 0)
                };
                for first in &positions {
                    for second in &positions {
                        let frontier: BTreeMap<PackageId, PackageRecord> = [first, second]
                            .into_iter()
                            .enumerate()
                            .filter_map(|(index, position)| {
                                position.map(|(holder, phase)| {
                                    (package(index as u128), record(holder, phase))
                                })
                            })
                            .collect();
                        let mut expected = BTreeMap::new();
                        for (id, record) in &frontier {
                            if deleted.contains(record.holder()) {
                                expected.insert(*id, RetirementReason::HolderRemoved);
                                continue;
                            }
                            let (mask, reason) = match record.phase() {
                                Phase::Out => (acceptance, RetirementReason::NoAcceptingEdge),
                                Phase::In => (receipts, RetirementReason::RouteRemoved),
                            };
                            if mask & bit(record, *id) == 0 {
                                expected.insert(*id, reason);
                            }
                        }
                        let retired = cleanup(
                            frontier.iter().map(|(id, record)| (*id, record)),
                            &deleted,
                            accepts,
                            retains,
                        )
                        .unwrap();
                        assert_eq!(retired, expected);
                        let survivors = frontier
                            .iter()
                            .filter(|(id, _)| !retired.contains_key(id))
                            .map(|(id, record)| (*id, record));
                        let again = cleanup(survivors, &BTreeSet::new(), accepts, retains).unwrap();
                        assert!(again.is_empty());
                        worlds += 1;
                    }
                }
            }
        }
        assert_eq!(worlds, 25_600);
    }

    #[test]
    fn callbacks_are_consulted_only_for_surviving_holders_by_phase() {
        let deleted = BTreeSet::from([Arc::<str>::from("gone")]);
        let frontier = BTreeMap::from([
            (package(0), record("s", Phase::Out)),
            (package(1), record("s", Phase::In)),
            (package(2), record("gone", Phase::In)),
            (package(3), record("gone", Phase::Out)),
        ]);
        let mut asked_out = Vec::new();
        let mut asked_in = Vec::new();
        let retired = cleanup(
            frontier.iter().map(|(id, record)| (*id, record)),
            &deleted,
            |p, _| {
                asked_out.push(p);
                Ok::<_, ()>(true)
            },
            |p, _| {
                asked_in.push(p);
                Ok(false)
            },
        )
        .unwrap();
        assert_eq!(asked_out, vec![package(0)]);
        assert_eq!(asked_in, vec![package(1)]);
        assert_eq!(
            retired,
            BTreeMap::from([
                (package(1), RetirementReason::RouteRemoved),
                (package(2), RetirementReason::HolderRemoved),
                (package(3), RetirementReason::HolderRemoved),
            ])
        );
    }

    #[test]
    fn exhaustive_three_step_cleanup_cannot_resurrect_packages() {
        for phase in [Phase::Out, Phase::In] {
            for choices in 0_u8..64 {
                let mut frontier = BTreeMap::from([(package(0), record("holder", phase))]);
                let mut holder_alive = true;
                let mut ever_retired = false;
                for step in 0..3 {
                    let choice = (choices >> (step * 2)) & 3;
                    holder_alive &= choice & 1 != 0;
                    let deleted = if holder_alive {
                        BTreeSet::new()
                    } else {
                        BTreeSet::from([Arc::<str>::from("holder")])
                    };
                    let retired = cleanup(
                        frontier.iter().map(|(id, record)| (*id, record)),
                        &deleted,
                        |_, _| Ok::<_, ()>(choice & 2 != 0),
                        |_, _| Ok(true),
                    )
                    .unwrap();
                    assert!(retired.keys().all(|id| frontier.contains_key(id)));
                    if ever_retired {
                        assert!(frontier.is_empty());
                    }
                    ever_retired |= !retired.is_empty();
                    frontier.retain(|id, _| !retired.contains_key(id));
                }
            }
        }
    }
}
