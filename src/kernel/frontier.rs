//! Canonical package positions and the deterministic rewrite cleanup rule.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::occurrence::{ActivationId, PackageId};

/// Whether a live package is awaiting transfer or has reached its receiver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Phase {
    /// Held at its producing node, awaiting one outgoing transfer.
    Out,
    /// Delivered to its receiver, possibly undergoing speculative processing.
    In,
}

/// The authoritative holder and phase of one live package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub(crate) holder: Arc<str>,
    pub(crate) phase: Phase,
}

impl Position {
    /// Identifies one package holder and its transfer phase.
    #[must_use]
    pub fn new(holder: impl Into<Arc<str>>, phase: Phase) -> Self {
        Self {
            holder: holder.into(),
            phase,
        }
    }

    /// Returns the actual node incarnation holding the package.
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

/// Immutable evidence of the single admitted transfer of one package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Delivery {
    pub(crate) edge_id: Arc<str>,
    pub(crate) source: Arc<str>,
    pub(crate) receiver: Arc<str>,
}

impl Delivery {
    pub(crate) fn new(
        edge_id: impl Into<Arc<str>>,
        source: impl Into<Arc<str>>,
        receiver: impl Into<Arc<str>>,
    ) -> Self {
        Self {
            edge_id: edge_id.into(),
            source: source.into(),
            receiver: receiver.into(),
        }
    }

    /// Returns the historical edge used for delivery.
    #[must_use]
    pub fn edge_id(&self) -> &str {
        &self.edge_id
    }

    /// Returns the producing node incarnation.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
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
    /// Its previous node incarnation was deleted or replaced by a rewrite.
    HolderRemoved,
    /// A rewrite changed its surviving producer's outgoing edges and none
    /// accepts this package.
    NoAcceptingEdge,
    /// A rewrite removed the edge that delivered it to a surviving `All`
    /// receiver, so no current-edge join can ever include it.
    RouteRemoved,
    /// An admitted retire operation removed it.
    Explicit,
}

/// Canonical record of one package's departure from the live frontier.
///
/// Live packages have a [`Position`], consumed packages have a consumer, and
/// every other package has exactly one retirement. The three sets partition
/// the package population of a valid state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Retirement {
    pub(crate) reason: RetirementReason,
    pub(crate) holder: Arc<str>,
    pub(crate) phase: Phase,
    pub(crate) revision: u64,
    pub(crate) evidence: Option<ActivationId>,
}

impl Retirement {
    /// Returns why the package was retired.
    #[must_use]
    pub const fn reason(&self) -> RetirementReason {
        self.reason
    }

    /// Returns the node incarnation holding the package when it was retired.
    #[must_use]
    pub fn holder(&self) -> &str {
        &self.holder
    }

    /// Returns the package's phase when it was retired.
    #[must_use]
    pub const fn phase(&self) -> Phase {
        self.phase
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

    /// Reports whether the reason admits this phase and evidence.
    pub(crate) const fn is_consistent(&self) -> bool {
        match self.reason {
            RetirementReason::HolderRemoved => self.evidence.is_none(),
            RetirementReason::NoAcceptingEdge => {
                matches!(self.phase, Phase::Out) && self.evidence.is_none()
            }
            RetirementReason::RouteRemoved => {
                matches!(self.phase, Phase::In) && self.evidence.is_none()
            }
            RetirementReason::Explicit => true,
        }
    }
}

pub(super) struct Cleanup {
    pub(super) positions: BTreeMap<PackageId, Position>,
    pub(super) retired: BTreeMap<PackageId, RetirementReason>,
}

/// Classifies every live package after separately validated structural admission.
///
/// `accepts` is invoked only for `Out` packages with a surviving holder and
/// `retains_receipt` only for `In` packages with a surviving holder. Neither
/// is consulted for removed holders.
pub(super) fn cleanup<E>(
    positions: &BTreeMap<PackageId, Position>,
    survivors: &BTreeMap<Arc<str>, Arc<str>>,
    mut accepts: impl FnMut(&str, PackageId) -> Result<bool, E>,
    mut retains_receipt: impl FnMut(&str, PackageId) -> Result<bool, E>,
) -> Result<Cleanup, E> {
    let mut kept = BTreeMap::new();
    let mut retired = BTreeMap::new();
    for (&package, position) in positions {
        let Some(holder) = survivors.get(&position.holder) else {
            retired.insert(package, RetirementReason::HolderRemoved);
            continue;
        };
        let retained = match position.phase {
            Phase::Out => accepts(holder, package)?,
            Phase::In => retains_receipt(holder, package)?,
        };
        if retained {
            kept.insert(
                package,
                Position {
                    holder: Arc::clone(holder),
                    phase: position.phase,
                },
            );
        } else {
            let reason = match position.phase {
                Phase::Out => RetirementReason::NoAcceptingEdge,
                Phase::In => RetirementReason::RouteRemoved,
            };
            retired.insert(package, reason);
        }
    }
    Ok(Cleanup {
        positions: kept,
        retired,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::occurrence::ActivationId;

    fn package(index: u128) -> PackageId {
        PackageId::from_parts(ActivationId::from_u128(1), index)
    }

    #[test]
    fn exhaustive_two_package_cleanup_matches_partition_and_idempotence() {
        let old = [Arc::<str>::from("old-a"), Arc::from("old-b")];
        let new = [Arc::<str>::from("new-a"), Arc::from("new-b")];
        let positions = [
            None,
            Some(Position::new(old[0].clone(), Phase::Out)),
            Some(Position::new(old[0].clone(), Phase::In)),
            Some(Position::new(old[1].clone(), Phase::Out)),
            Some(Position::new(old[1].clone(), Phase::In)),
        ];
        let identity = new
            .iter()
            .map(|node| (node.clone(), node.clone()))
            .collect();
        let mut worlds = 0;
        for a in 0..3 {
            for b in 0..3 {
                if a != 0 && a == b {
                    continue;
                }
                let survivors: BTreeMap<_, _> = [a, b]
                    .into_iter()
                    .enumerate()
                    .filter(|(_, destination)| *destination != 0)
                    .map(|(source, destination)| {
                        (old[source].clone(), new[destination - 1].clone())
                    })
                    .collect();
                for masks in 0_u16..256 {
                    let (acceptance, receipts) = (masks & 15, masks >> 4);
                    let bit = |holder: &str, p: PackageId| -> u16 {
                        1 << (u128::from(holder != &*new[0]) * 2 + p.output())
                    };
                    let accepts = |holder: &str, p: PackageId| -> Result<bool, ()> {
                        Ok(acceptance & bit(holder, p) != 0)
                    };
                    let retain = |holder: &str, p: PackageId| -> Result<bool, ()> {
                        Ok(receipts & bit(holder, p) != 0)
                    };
                    for first in &positions {
                        for second in &positions {
                            let frontier: BTreeMap<_, _> = [first, second]
                                .into_iter()
                                .enumerate()
                                .filter_map(|(index, pos)| {
                                    pos.clone().map(|p| (package(index as u128), p))
                                })
                                .collect();
                            let original = frontier.clone();
                            let mut expected_kept = BTreeMap::new();
                            let mut expected_retired = BTreeMap::new();
                            for (id, position) in &frontier {
                                match survivors.get(&position.holder) {
                                    None => {
                                        expected_retired
                                            .insert(*id, RetirementReason::HolderRemoved);
                                    }
                                    Some(holder) => {
                                        let (mask, reason) = match position.phase {
                                            Phase::Out => {
                                                (acceptance, RetirementReason::NoAcceptingEdge)
                                            }
                                            Phase::In => (receipts, RetirementReason::RouteRemoved),
                                        };
                                        if mask & bit(holder, *id) != 0 {
                                            expected_kept.insert(
                                                *id,
                                                Position::new(holder.clone(), position.phase),
                                            );
                                        } else {
                                            expected_retired.insert(*id, reason);
                                        }
                                    }
                                }
                            }
                            let cleaned = cleanup(&frontier, &survivors, accepts, retain).unwrap();
                            assert_eq!(cleaned.positions, expected_kept);
                            assert_eq!(cleaned.retired, expected_retired);
                            assert_eq!(
                                cleaned.positions.len() + cleaned.retired.len(),
                                frontier.len()
                            );
                            assert!(
                                cleaned
                                    .positions
                                    .keys()
                                    .all(|id| !cleaned.retired.contains_key(id))
                            );
                            assert_eq!(frontier, original);
                            let again =
                                cleanup(&cleaned.positions, &identity, accepts, retain).unwrap();
                            assert_eq!(again.positions, cleaned.positions);
                            assert!(again.retired.is_empty());
                            worlds += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(worlds, 44_800);
    }

    #[test]
    fn receipt_callback_governs_only_received_packages_at_survivors() {
        let survivors = BTreeMap::from([(Arc::<str>::from("s"), Arc::<str>::from("s"))]);
        let frontier = BTreeMap::from([
            (package(0), Position::new("s", Phase::Out)),
            (package(1), Position::new("s", Phase::In)),
            (package(2), Position::new("gone", Phase::In)),
            (package(3), Position::new("gone", Phase::Out)),
        ]);
        let mut asked_out = Vec::new();
        let mut asked_in = Vec::new();
        let cleaned = cleanup(
            &frontier,
            &survivors,
            |holder, p| {
                asked_out.push((holder.to_owned(), p));
                Ok::<_, ()>(true)
            },
            |holder, p| {
                asked_in.push((holder.to_owned(), p));
                Ok(false)
            },
        )
        .unwrap();
        assert_eq!(asked_out, vec![("s".to_owned(), package(0))]);
        assert_eq!(asked_in, vec![("s".to_owned(), package(1))]);
        assert_eq!(
            cleaned.positions,
            BTreeMap::from([(package(0), Position::new("s", Phase::Out))])
        );
        assert_eq!(
            cleaned.retired,
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
                let mut frontier = BTreeMap::from([(package(0), Position::new("holder", phase))]);
                let mut holder_alive = true;
                let mut ever_retired = false;
                for step in 0..3 {
                    let choice = (choices >> (step * 2)) & 3;
                    holder_alive &= choice & 1 != 0;
                    let survives = if holder_alive {
                        BTreeMap::from([(Arc::from("holder"), Arc::from("holder"))])
                    } else {
                        BTreeMap::new()
                    };
                    let cleaned = cleanup(
                        &frontier,
                        &survives,
                        |_, _| Ok::<_, ()>(choice & 2 != 0),
                        |_, _| Ok(true),
                    )
                    .unwrap();
                    assert!(cleaned.positions.keys().all(|id| frontier.contains_key(id)));
                    if ever_retired {
                        assert!(cleaned.positions.is_empty());
                    }
                    ever_retired |= !cleaned.retired.is_empty();
                    frontier = cleaned.positions;
                }
            }
        }
    }
}
