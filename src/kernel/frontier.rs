//! Canonical package positions and the deterministic rewrite cleanup rule.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::occurrence::PackageId;

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

/// Why a combined rewrite removes a package from the live frontier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RetirementReason {
    /// Its previous node incarnation was deleted or replaced.
    HolderRemoved,
    /// Its surviving producer has no outgoing edge accepting this package.
    NoAcceptingEdge,
}

pub(super) struct Cleanup {
    pub(super) positions: BTreeMap<PackageId, Position>,
    pub(super) retired: BTreeMap<PackageId, RetirementReason>,
}

/// Classifies every live package after separately validated structural admission.
/// The callback is invoked only for Out packages with a surviving holder.
pub(super) fn cleanup<E>(
    positions: &BTreeMap<PackageId, Position>,
    survivors: &BTreeMap<Arc<str>, Arc<str>>,
    mut accepts: impl FnMut(&str, PackageId) -> Result<bool, E>,
) -> Result<Cleanup, E> {
    let mut kept = BTreeMap::new();
    let mut retired = BTreeMap::new();
    for (&package, position) in positions {
        let Some(holder) = survivors.get(&position.holder) else {
            retired.insert(package, RetirementReason::HolderRemoved);
            continue;
        };
        if position.phase == Phase::Out && !accepts(holder, package)? {
            retired.insert(package, RetirementReason::NoAcceptingEdge);
        } else {
            kept.insert(
                package,
                Position {
                    holder: Arc::clone(holder),
                    phase: position.phase,
                },
            );
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
                for acceptance in 0_u8..16 {
                    let accepts = |holder: &str, p: PackageId| -> Result<bool, ()> {
                        let holder_index = u128::from(holder != &*new[0]);
                        Ok(acceptance & (1 << (holder_index * 2 + p.output())) != 0)
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
                                        let index =
                                            new.iter().position(|node| node == holder).unwrap();
                                        let supported = acceptance
                                            & (1 << (index * 2
                                                + usize::try_from(id.output()).unwrap()))
                                            != 0;
                                        if position.phase == Phase::In || supported {
                                            expected_kept.insert(
                                                *id,
                                                Position::new(holder.clone(), position.phase),
                                            );
                                        } else {
                                            expected_retired
                                                .insert(*id, RetirementReason::NoAcceptingEdge);
                                        }
                                    }
                                }
                            }
                            let cleaned = cleanup(&frontier, &survivors, accepts).unwrap();
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
                            let again = cleanup(&cleaned.positions, &identity, accepts).unwrap();
                            assert_eq!(again.positions, cleaned.positions);
                            assert!(again.retired.is_empty());
                            worlds += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(worlds, 2_800);
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
                    let cleaned =
                        cleanup(&frontier, &survives, |_, _| Ok::<_, ()>(choice & 2 != 0)).unwrap();
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
