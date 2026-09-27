//! Trusted-store integrity: checkpoint validation and definition encoding.
//!
//! A checkpoint is the adapter's view of a whole state. Restoring it checks
//! the definition binding, the invariants I1 through I7 of the state model,
//! causal acyclicity, and two consequences of rewrite cleanup. The state keeps
//! no historical incidence, so I3 and I7 are checked as far as it records
//! them: a delivery on a current edge must match that edge's incidence, a
//! delivery on a removed edge must name a used edge identity and receiver,
//! deliveries over one edge identity must agree on its endpoints, and edge
//! identities need some node identity for those endpoints. These checks are
//! exactly the invariants: the Lean model's `checkpoint_sound` proves that
//! some well-formed state records every checkpoint they accept. Restoring does
//! not rerun contracts or cleanup, so it establishes integrity of a trusted
//! store, not historical reachability.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::graph::{
    Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, DefinitionError,
    DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition, IngressMode, Node, NodeDefinition,
    RootRule,
};

use super::definition::Kernel;
use super::frontier::RetirementReason;
use super::occurrence::{
    Activation, ActivationId, PackageId, PackageRecord, PackageStatus, State, Trigger, fresh_nonce,
};
use super::rewrite::RewriteFragment;

/// The whole of one state as an adapter stores it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Checkpoint {
    /// Number of accepted rewrites and vocabulary extensions, including no-ops.
    pub definition_changes: u64,
    /// The workflow definition the state is bound to.
    pub definition_id: DefinitionId,
    /// The fingerprint of the definition version the state is bound to.
    pub definition_fingerprint: DefinitionFingerprint,
    /// Every accepted activation.
    pub activations: BTreeMap<ActivationId, Activation>,
    /// One record per package.
    pub packages: BTreeMap<PackageId, PackageRecord>,
    /// Every node identity ever admitted.
    pub used_node_ids: BTreeSet<Arc<str>>,
    /// Every edge identity ever admitted.
    pub used_edge_ids: BTreeSet<Arc<str>>,
    /// The state revision.
    pub revision: u64,
}

/// A checkpoint violates a state invariant. Each variant is one invariant
/// family; the detail names the specific check.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum CheckpointError {
    /// The checkpoint is bound to another definition or definition version.
    #[error(
        "checkpoint definition {actual_id}@{actual_fingerprint} does not match kernel definition {expected_id}@{expected_fingerprint}"
    )]
    DefinitionMismatch {
        /// Kernel definition identity.
        expected_id: DefinitionId,
        /// Checkpoint definition identity.
        actual_id: DefinitionId,
        /// Kernel definition fingerprint.
        expected_fingerprint: DefinitionFingerprint,
        /// Checkpoint definition fingerprint.
        actual_fingerprint: DefinitionFingerprint,
    },
    /// Lifetime identity allocations are malformed or omit current identities (I7).
    #[error("identity allocation: {0}")]
    Identity(&'static str),
    /// A record and its producing activation disagree (I1).
    #[error("ownership: {0}")]
    Ownership(&'static str),
    /// An activation record is malformed.
    #[error("activation: {0}")]
    Activation(&'static str),
    /// Consumption and activation inputs disagree (I2).
    #[error("consumption: {0}")]
    Consumption(&'static str),
    /// A delivery disagrees with the graph or the birth edge (I3).
    #[error("delivery: {0}")]
    Delivery(&'static str),
    /// A live package is held where no package can be live (I5).
    #[error("custody: {0}")]
    Custody(&'static str),
    /// A retirement disagrees with its package or its evidence (I4).
    #[error("retirement: {0}")]
    Retirement(&'static str),
    /// The revision differs from what the recorded operations require (I6).
    #[error("revision: {0}")]
    Revision(&'static str),
    /// The consumption relation is not a rooted DAG.
    #[error("accepted activation references contain a causal cycle at {0}")]
    Cycle(ActivationId),
}

impl State {
    /// Exports the state as a checkpoint.
    #[must_use]
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            definition_changes: self.definition_changes,
            definition_id: self.definition_id.clone(),
            definition_fingerprint: self.definition_fingerprint,
            activations: self.activations.clone(),
            packages: self.packages.clone(),
            used_node_ids: self.used_node_ids.clone(),
            used_edge_ids: self.used_edge_ids.clone(),
            revision: self.revision,
        }
    }
}

impl Kernel {
    /// Checks a trusted checkpoint's invariants and rebuilds the state.
    ///
    /// This verifies the definition binding, ownership, custody, consumption,
    /// retirement consistency, identity allocation, exact revision accounting,
    /// causal acyclicity, join-authority equality, schema membership of every
    /// root authority, object type, and carried authority, current-edge
    /// incidence of every delivery, and one incidence per edge identity across
    /// deliveries. Allocated edge identities require an allocated node
    /// identity. It does not rerun contracts or cleanup.
    ///
    /// # Errors
    ///
    /// Returns the first violated invariant.
    pub fn restore_checkpoint(&self, checkpoint: Checkpoint) -> Result<State, CheckpointError> {
        let Checkpoint {
            definition_changes,
            definition_id,
            definition_fingerprint,
            activations,
            packages,
            used_node_ids,
            used_edge_ids,
            revision,
        } = checkpoint;
        if &definition_id != self.id() || &definition_fingerprint != self.fingerprint() {
            return Err(CheckpointError::DefinitionMismatch {
                expected_id: self.id().clone(),
                actual_id: definition_id,
                expected_fingerprint: *self.fingerprint(),
                actual_fingerprint: definition_fingerprint,
            });
        }
        if used_node_ids
            .iter()
            .chain(&used_edge_ids)
            .any(|id| id.is_empty())
            || self
                .graph()
                .nodes()
                .iter()
                .any(|node| !used_node_ids.contains(node.id()))
            || self
                .graph()
                .edges()
                .iter()
                .any(|edge| !used_edge_ids.contains(edge.id()))
        {
            return Err(CheckpointError::Identity(
                "current graph identities are missing or malformed in lifetime allocations",
            ));
        }
        // Every admitted edge had admitted endpoints. The lifetime sets keep no
        // incidence, so this is all they can record of it.
        if used_node_ids.is_empty() && !used_edge_ids.is_empty() {
            return Err(CheckpointError::Identity(
                "edge identities are allocated without any node identity",
            ));
        }
        if activations
            .values()
            .map(|activation| activation.outputs.len())
            .sum::<usize>()
            != packages.len()
        {
            return Err(CheckpointError::Ownership(
                "package records do not correspond to activation outputs",
            ));
        }

        let mut explicit_transfers = 0_u64;
        let mut explicit_retirements = 0_u64;
        let mut structural_revisions = BTreeSet::new();
        let mut explicit_revisions = BTreeSet::new();
        let mut incidences = BTreeMap::new();
        consumption_order(&activations).map_err(CheckpointError::Cycle)?;
        for (&id, activation) in &activations {
            let node = match &activation.trigger {
                Trigger::Orig { node_id, authority } => {
                    if !self.schema().admits_authority(authority) {
                        return Err(CheckpointError::Activation(
                            "root authority is outside the schema",
                        ));
                    }
                    Arc::clone(node_id)
                }
                Trigger::Pkgs { package_ids } => {
                    let mut anchor: Option<(Arc<str>, &Authority)> = None;
                    for package in package_ids {
                        let input = packages
                            .get(package)
                            .ok_or(CheckpointError::Consumption("activation input is unknown"))?;
                        let Some(delivery) = &input.delivery else {
                            return Err(CheckpointError::Consumption(
                                "activation input was never delivered",
                            ));
                        };
                        if input.status != PackageStatus::Consumed(id) {
                            return Err(CheckpointError::Consumption(
                                "activation input is not consumed by it",
                            ));
                        }
                        match &anchor {
                            None => {
                                anchor = Some((Arc::clone(&delivery.receiver), &input.authority));
                            }
                            Some((receiver, authority)) => {
                                if *receiver != delivery.receiver || *authority != &input.authority
                                {
                                    return Err(CheckpointError::Consumption(
                                        "activation inputs disagree on custody or authority",
                                    ));
                                }
                            }
                        }
                    }
                    anchor
                        .map(|(receiver, _)| receiver)
                        .ok_or(CheckpointError::Activation(
                            "activation has no input packages",
                        ))?
                }
            };
            if activation.node_id != node {
                return Err(CheckpointError::Consumption(
                    "recorded execution node disagrees with trigger",
                ));
            }
            if !used_node_ids.contains(&node) {
                return Err(CheckpointError::Identity(
                    "execution node is absent from lifetime allocations",
                ));
            }
            for (&package_id, output) in &activation.outputs {
                let record = packages
                    .get(&package_id)
                    .ok_or(CheckpointError::Ownership("activation output is absent"))?;
                if package_id.producer() != id
                    || record.object_type != output.object_type
                    || record.authority != output.authority
                    || record.content_digest != output.content_digest
                    || record.producer_node != node
                    || !self.schema().admits_object_type(record.object_type())
                    || !self.schema().admits_authority(record.authority())
                {
                    return Err(CheckpointError::Ownership(
                        "package record disagrees with its producing activation",
                    ));
                }
                match &record.delivery {
                    Some(delivery) => {
                        if output
                            .edge_id
                            .as_ref()
                            .is_some_and(|edge| *edge != delivery.edge_id)
                            || !used_edge_ids.contains(&delivery.edge_id)
                            || !used_node_ids.contains(&delivery.receiver)
                            || self.graph().edge(&delivery.edge_id).is_some_and(|edge| {
                                edge.source() != &*node || edge.target() != &*delivery.receiver
                            })
                        {
                            return Err(CheckpointError::Delivery(
                                "delivery is inconsistent with package custody",
                            ));
                        }
                        // An edge identity keeps one incidence for its lifetime,
                        // so every delivery over it agrees on its endpoints, even
                        // once the edge is removed.
                        let incidence = (&record.producer_node, &delivery.receiver);
                        if *incidences.entry(&delivery.edge_id).or_insert(incidence) != incidence {
                            return Err(CheckpointError::Delivery(
                                "deliveries over one edge disagree on its endpoints",
                            ));
                        }
                        if output.edge_id.is_none() {
                            explicit_transfers += 1;
                        }
                    }
                    None => {
                        if output.edge_id.is_some() {
                            return Err(CheckpointError::Delivery(
                                "birth delivery is missing from the record",
                            ));
                        }
                    }
                }
                match &record.status {
                    PackageStatus::Live => {
                        if self.graph().node(record.holder()).is_none() {
                            return Err(CheckpointError::Custody(
                                "live package holder is absent from the graph",
                            ));
                        }
                        // Cleanup retires a receipt at an `All` receiver whose
                        // delivery edge left the incoming set; one that is still
                        // live can only come from a store that skipped cleanup.
                        if let Some(delivery) = &record.delivery
                            && self
                                .node_definition(record.holder())
                                .is_some_and(|node| node.ingress_mode() == IngressMode::All)
                            && !self
                                .incoming_edge_ids(record.holder())
                                .contains(&delivery.edge_id)
                        {
                            return Err(CheckpointError::Custody(
                                "live receipt at an All receiver names a route that is no longer incoming",
                            ));
                        }
                    }
                    PackageStatus::Consumed(consumer) => {
                        if record.delivery.is_none()
                            || !activations
                                .get(consumer)
                                .and_then(Activation::inputs)
                                .is_some_and(|inputs| inputs.contains(&package_id))
                        {
                            return Err(CheckpointError::Consumption(
                                "consumed package is not an input of its consumer",
                            ));
                        }
                    }
                    PackageStatus::Retired(retirement) => {
                        if !retirement.admits(record.phase())
                            || retirement.revision() == 0
                            || retirement.revision() > revision
                            || retirement
                                .evidence()
                                .is_some_and(|evidence| !activations.contains_key(&evidence))
                        {
                            return Err(CheckpointError::Retirement(
                                "retirement is inconsistent with package history",
                            ));
                        }
                        // Identities never re-enter the graph, so a removed
                        // holder cannot be a current node.
                        if retirement.reason() == RetirementReason::HolderRemoved
                            && self.graph().node(record.holder()).is_some()
                        {
                            return Err(CheckpointError::Retirement(
                                "holder-removed retirement names a current node",
                            ));
                        }
                        if retirement.reason() == RetirementReason::Explicit {
                            if !explicit_revisions.insert(retirement.revision()) {
                                return Err(CheckpointError::Retirement(
                                    "explicit retirements share a revision",
                                ));
                            }
                            explicit_retirements += 1;
                        } else {
                            structural_revisions.insert(retirement.revision());
                        }
                    }
                }
            }
        }

        if !explicit_revisions.is_disjoint(&structural_revisions)
            || u64::try_from(structural_revisions.len())
                .map_or(true, |count| count > definition_changes)
        {
            return Err(CheckpointError::Revision(
                "retirement revisions disagree with definition changes",
            ));
        }
        let expected_revision = u64::try_from(activations.len())
            .ok()
            .and_then(|count| count.checked_add(explicit_transfers))
            .and_then(|count| count.checked_add(explicit_retirements))
            .and_then(|count| count.checked_add(definition_changes))
            .ok_or(CheckpointError::Revision("revision overflow"))?;
        if revision != expected_revision {
            return Err(CheckpointError::Revision(
                "state revision disagrees with its activations, transfers, retirements, or definition changes",
            ));
        }
        let live = packages
            .iter()
            .filter(|(_, record)| record.is_live())
            .map(|(id, _)| *id)
            .collect();
        Ok(State {
            definition_changes,
            definition_id,
            definition_fingerprint,
            activations,
            packages,
            live,
            used_node_ids,
            used_edge_ids,
            revision,
            nonce: fresh_nonce(),
        })
    }
}

/// Orders activations so that every producer precedes every consumer of its
/// packages, or names an activation left in a cycle.
///
/// Every input package must be produced by an activation of the map; an
/// input from an absent producer keeps its consumer unreachable and is
/// reported as a cycle. Callers that need a finer diagnosis check producers
/// first. The order is deterministic: among ready activations the least
/// identity goes first.
pub(super) fn consumption_order(
    activations: &BTreeMap<ActivationId, Activation>,
) -> Result<Vec<ActivationId>, ActivationId> {
    let mut indegree = BTreeMap::new();
    let mut children = BTreeMap::<ActivationId, Vec<ActivationId>>::new();
    for (&id, activation) in activations {
        indegree.insert(id, activation.inputs().map_or(0, BTreeSet::len));
        for package in activation.inputs().into_iter().flatten() {
            children.entry(package.producer()).or_default().push(id);
        }
    }
    let mut ready: BTreeSet<_> = indegree
        .iter()
        .filter_map(|(&id, &degree)| (degree == 0).then_some(id))
        .collect();
    let mut order = Vec::with_capacity(activations.len());
    while let Some(id) = ready.pop_first() {
        order.push(id);
        for child in children.get(&id).into_iter().flatten() {
            let degree = indegree.get_mut(child).expect("every consumer was indexed");
            *degree -= 1;
            if *degree == 0 {
                ready.insert(*child);
            }
        }
    }
    if order.len() == activations.len() {
        Ok(order)
    } else {
        Err(indegree
            .into_iter()
            .find_map(|(id, degree)| (degree != 0).then_some(id))
            .expect("an incomplete traversal leaves an activation"))
    }
}

/// The persisted encoding of a definition fragment.
///
/// This is the only serialization of graph annotations. Decoding passes
/// through the checked constructors, so a stored fragment cannot describe a
/// definition the kernel would refuse, and refuses any field this version
/// does not define.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FragmentData {
    /// Encoding version; currently 1.
    pub version: u32,
    nodes: Vec<NodeData>,
    edges: Vec<EdgeData>,
    node_definitions: Vec<NodeDefinitionData>,
    edge_definitions: Vec<EdgeDefinitionData>,
    authority_transitions: Vec<TransitionData>,
    roots: Vec<RootData>,
}

/// The encoding version this crate writes.
pub const FRAGMENT_ENCODING_VERSION: u32 = 1;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct NodeData {
    id: Arc<str>,
}
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct EdgeData {
    id: Arc<str>,
    source: Arc<str>,
    target: Arc<str>,
}
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
enum IngressModeData {
    Any,
    All,
}
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
enum AuthorityMatchData {
    AnyOf,
    AllOf,
}
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct NodeDefinitionData {
    node_id: Arc<str>,
    types: BTreeSet<Arc<str>>,
    result_contract: Arc<str>,
    ingress_mode: IngressModeData,
}
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct EdgeDefinitionData {
    edge_id: Arc<str>,
    types: BTreeSet<Arc<str>>,
    source_requirements: BTreeSet<Arc<str>>,
    target_requirements: BTreeSet<Arc<str>>,
    package_contract: Arc<str>,
    authority_tags: Vec<Arc<str>>,
    authority_match: AuthorityMatchData,
}
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct TransitionData {
    node_id: Arc<str>,
    from: Authority,
    to: Authority,
}
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct RootData {
    node_id: Arc<str>,
    ceiling: Authority,
}

/// A stored fragment cannot be decoded into a definition.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum FragmentDecodeError {
    /// The encoding version is not one this crate reads.
    #[error("unsupported fragment encoding version {0}")]
    Version(u32),
    /// A decoded value fails a definition constructor.
    #[error(transparent)]
    Definition(#[from] DefinitionError),
}

impl From<&RewriteFragment> for FragmentData {
    fn from(fragment: &RewriteFragment) -> Self {
        Self {
            version: FRAGMENT_ENCODING_VERSION,
            nodes: fragment
                .nodes
                .iter()
                .map(|node| NodeData { id: node.id_arc() })
                .collect(),
            edges: fragment
                .edges
                .iter()
                .map(|edge| EdgeData {
                    id: edge.id_arc(),
                    source: Arc::from(edge.source()),
                    target: edge.target_arc(),
                })
                .collect(),
            node_definitions: fragment
                .node_definitions
                .iter()
                .map(|node| NodeDefinitionData {
                    node_id: Arc::from(node.node_id()),
                    types: node.types().clone(),
                    result_contract: Arc::from(node.result_contract()),
                    ingress_mode: match node.ingress_mode() {
                        IngressMode::Any => IngressModeData::Any,
                        IngressMode::All => IngressModeData::All,
                    },
                })
                .collect(),
            edge_definitions: fragment
                .edge_definitions
                .iter()
                .map(|edge| EdgeDefinitionData {
                    edge_id: Arc::from(edge.edge_id()),
                    types: edge.types().clone(),
                    source_requirements: edge.source_requirements().clone(),
                    target_requirements: edge.target_requirements().clone(),
                    package_contract: Arc::from(edge.package_contract()),
                    authority_tags: edge
                        .authority_tags()
                        .iter()
                        .map(|tag| Arc::from(tag.id()))
                        .collect(),
                    authority_match: match edge.authority_match() {
                        AuthorityMatch::AnyOf => AuthorityMatchData::AnyOf,
                        AuthorityMatch::AllOf => AuthorityMatchData::AllOf,
                    },
                })
                .collect(),
            authority_transitions: fragment
                .authority_transitions
                .iter()
                .map(|rule| TransitionData {
                    node_id: Arc::from(rule.node_id()),
                    from: rule.from().clone(),
                    to: rule.to().clone(),
                })
                .collect(),
            roots: fragment
                .roots
                .iter()
                .map(|root| RootData {
                    node_id: Arc::from(root.node_id()),
                    ceiling: root.ceiling().clone(),
                })
                .collect(),
        }
    }
}

impl TryFrom<FragmentData> for RewriteFragment {
    type Error = FragmentDecodeError;

    fn try_from(data: FragmentData) -> Result<Self, Self::Error> {
        if data.version != FRAGMENT_ENCODING_VERSION {
            return Err(FragmentDecodeError::Version(data.version));
        }
        let fragment = Self::new(
            data.nodes
                .into_iter()
                .map(|node| Node::new(node.id))
                .collect::<Result<_, _>>()?,
            data.edges
                .into_iter()
                .map(|edge| Edge::new(edge.id, edge.source, edge.target))
                .collect::<Result<_, _>>()?,
            data.node_definitions
                .into_iter()
                .map(|node| {
                    Ok::<_, DefinitionError>(
                        NodeDefinition::new(node.node_id, node.types, node.result_contract)?
                            .with_ingress_mode(match node.ingress_mode {
                                IngressModeData::Any => IngressMode::Any,
                                IngressModeData::All => IngressMode::All,
                            }),
                    )
                })
                .collect::<Result<_, _>>()?,
            data.edge_definitions
                .into_iter()
                .map(|edge| {
                    let authority_tags = edge
                        .authority_tags
                        .into_iter()
                        .map(AuthorityTag::new)
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok::<_, DefinitionError>(
                        EdgeDefinition::new(
                            edge.edge_id,
                            edge.types,
                            edge.source_requirements,
                            edge.target_requirements,
                            edge.package_contract,
                            authority_tags,
                        )?
                        .with_authority_match(
                            match edge.authority_match {
                                AuthorityMatchData::AnyOf => AuthorityMatch::AnyOf,
                                AuthorityMatchData::AllOf => AuthorityMatch::AllOf,
                            },
                        ),
                    )
                })
                .collect::<Result<_, _>>()?,
            data.authority_transitions
                .into_iter()
                .map(|rule| AuthorityTransitionRule::new(rule.node_id, rule.from, rule.to))
                .collect::<Result<_, _>>()?,
            data.roots
                .into_iter()
                .map(|root| RootRule::new(root.node_id, root.ceiling))
                .collect::<Result<_, _>>()?,
        );
        Ok(fragment)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        ActivationProposal, Contract, Emission, Graph, OutputAuthority, Payload, Phase,
        RetirementReason, RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest, Schema,
    };

    fn fixture() -> (Kernel, Arc<AtomicUsize>) {
        let calls = Arc::new(AtomicUsize::new(0));
        let validator_calls = Arc::clone(&calls);
        let tag = AuthorityTag::new("run").unwrap();
        let authority = Authority::new([tag.clone()]);
        let kernel = Kernel::admit(
            DefinitionId::new("checkpoint").unwrap(),
            Schema::new(["node"], ["value"], [tag.clone()]).unwrap(),
            Graph::new(
                [Node::new("A").unwrap(), Node::new("B").unwrap()],
                [Edge::new("ab", "A", "B").unwrap()],
            )
            .unwrap(),
            [Contract::new("value", "value", move |_| {
                validator_calls.fetch_add(1, Ordering::Relaxed);
                Ok(())
            })
            .unwrap()],
            ["A", "B"].map(|node| NodeDefinition::new(node, ["node"], "value").unwrap()),
            [EdgeDefinition::new("ab", ["flow"], ["node"], ["node"], "value", [tag]).unwrap()],
            [],
            ["A", "B"].map(|node| RootRule::new(node, authority.clone()).unwrap()),
        )
        .unwrap();
        (kernel, calls)
    }

    fn emit(kernel: &Kernel, state: &mut State, delivered: bool) -> PackageId {
        let bytes: Payload = Arc::from(b"value".as_slice());
        let mut proposal = ActivationProposal::root(
            "A",
            Authority::new([AuthorityTag::new("run").unwrap()]),
            Arc::clone(&bytes),
        );
        proposal.emit(if delivered {
            Emission::new("ab", OutputAuthority::Carry, bytes)
        } else {
            Emission::outbound("value", OutputAuthority::Carry, bytes)
        });
        let activation = kernel.activate(state, proposal).unwrap();
        state
            .activation(activation)
            .unwrap()
            .outputs()
            .next()
            .unwrap()
    }

    #[test]
    fn current_checkpoint_preserves_retirement_old_delivery_and_unsupported_outbound() {
        let (initial, calls) = fixture();
        let mut state = initial.empty_state();
        let retired = emit(&initial, &mut state, false);
        let received = emit(&initial, &mut state, true);
        let right = RewriteFragment::new(
            initial.graph().nodes().to_vec(),
            vec![],
            initial.node_definitions().to_vec(),
            vec![],
            vec![],
            initial.roots().to_vec(),
        );
        let names: BTreeSet<Arc<str>> = [Arc::from("A"), Arc::from("B")].into();
        let grammar = RewriteGrammar::new([RewriteProduction::new(
            "disconnect",
            RewriteFragment::from_kernel(&initial),
            names.clone(),
            BTreeSet::new(),
            right,
        )
        .unwrap()])
        .unwrap();
        let request = RewriteRequest::new(
            "disconnect",
            RewriteMatch::new(
                names.into_iter().map(|node| (node.clone(), node)).collect(),
                BTreeMap::from([(Arc::from("ab"), Arc::from("ab"))]),
                BTreeMap::new(),
                BTreeMap::new(),
            ),
        );
        let prepared = initial
            .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
            .unwrap();
        let current = initial.commit_rewrite(&mut state, prepared).unwrap();
        let unsupported = emit(&current, &mut state, false);
        let before_calls = calls.load(Ordering::Relaxed);
        let restored = current.restore_checkpoint(state.checkpoint()).unwrap();
        assert_eq!(restored, state);
        assert_eq!(calls.load(Ordering::Relaxed), before_calls);
        assert!(restored.position(retired).is_none());
        assert_eq!(restored.position(received).unwrap().phase(), Phase::In);
        assert_eq!(restored.position(unsupported).unwrap().phase(), Phase::Out);
        assert!(current.graph().edge("ab").is_none());

        // The checkpoint is bound to the current definition version.
        assert!(matches!(
            initial.restore_checkpoint(state.checkpoint()),
            Err(CheckpointError::DefinitionMismatch { .. })
        ));

        // `ab` is no longer current, so its absence from the lifetime set is
        // caught where the historical delivery is checked.
        let mut invalid = state.checkpoint();
        invalid.used_edge_ids.remove("ab");
        assert!(matches!(
            current.restore_checkpoint(invalid),
            Err(CheckpointError::Delivery(_))
        ));
        let mut invalid = state.checkpoint();
        invalid.used_node_ids.remove("A");
        assert!(matches!(
            current.restore_checkpoint(invalid),
            Err(CheckpointError::Identity(_))
        ));
        let mut invalid = state.checkpoint();
        invalid.packages.get_mut(&unsupported).unwrap().object_type = Arc::from("changed");
        assert!(matches!(
            current.restore_checkpoint(invalid),
            Err(CheckpointError::Ownership(_))
        ));
        let mut invalid = state.checkpoint();
        invalid
            .activations
            .get_mut(&received.producer())
            .unwrap()
            .trigger = Trigger::Pkgs {
            package_ids: BTreeSet::from([received]),
        };
        invalid.packages.get_mut(&received).unwrap().status =
            PackageStatus::Consumed(received.producer());
        assert_eq!(
            current.restore_checkpoint(invalid).unwrap_err(),
            CheckpointError::Cycle(received.producer())
        );
    }

    #[test]
    fn checkpoint_validates_retirement_records_against_package_history() {
        let (kernel, _) = fixture();
        let mut state = kernel.empty_state();
        let outbound = emit(&kernel, &mut state, false);
        let received = emit(&kernel, &mut state, true);
        let evidence = received.producer();
        kernel.retire(&mut state, received, Some(evidence)).unwrap();
        kernel.retire(&mut state, outbound, None).unwrap();
        assert!(state.is_quiescent());
        assert_eq!(
            kernel.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        let rejects = |mutate: &dyn Fn(&mut Checkpoint)| {
            let mut invalid = state.checkpoint();
            mutate(&mut invalid);
            kernel.restore_checkpoint(invalid).unwrap_err()
        };
        let retire = |c: &mut Checkpoint,
                      id: PackageId,
                      f: &dyn Fn(&mut super::super::frontier::Retirement)| {
            let record = c.packages.get_mut(&id).unwrap();
            let PackageStatus::Retired(retirement) = &mut record.status else {
                panic!("retired fixture");
            };
            f(retirement);
        };

        let inconsistent =
            CheckpointError::Retirement("retirement is inconsistent with package history");
        assert_eq!(
            rejects(&|c| {
                retire(c, received, &|r| {
                    r.reason = RetirementReason::NoAcceptingEdge;
                });
            }),
            inconsistent
        );
        assert_eq!(
            rejects(&|c| {
                retire(c, outbound, &|r| r.reason = RetirementReason::RouteRemoved);
            }),
            inconsistent
        );
        assert_eq!(
            rejects(&|c| {
                retire(c, outbound, &|r| r.reason = RetirementReason::HolderRemoved);
            }),
            CheckpointError::Retirement("holder-removed retirement names a current node")
        );
        assert_eq!(
            rejects(&|c| {
                retire(c, outbound, &|r| {
                    r.evidence = Some(ActivationId::from_u128(7));
                });
            }),
            inconsistent
        );
        assert_eq!(
            rejects(&|c| {
                retire(c, outbound, &|r| r.revision = 0);
            }),
            inconsistent
        );
        assert_eq!(
            rejects(&|c| {
                let too_far = c.revision + 1;
                retire(c, outbound, &|r| r.revision = too_far);
            }),
            inconsistent
        );
        // Lowering the revision below the last retirement's stamp trips the
        // retirement check; lowering it below the operation count trips I6.
        assert_eq!(
            rejects(&|c| {
                c.revision -= 1;
            }),
            inconsistent
        );
        assert!(matches!(
            rejects(&|c| {
                retire(c, received, &|r| r.revision = 1);
                retire(c, outbound, &|r| r.revision = 2);
                c.revision = 3;
            }),
            CheckpointError::Revision(_)
        ));
        assert!(matches!(
            rejects(&|c| {
                c.packages.get_mut(&outbound).unwrap().producer_node = Arc::from("B");
            }),
            CheckpointError::Ownership(_)
        ));
    }

    #[test]
    fn checkpoint_validates_activation_triggers_against_consumption_records() {
        let run = AuthorityTag::new("run").unwrap();
        let spare = AuthorityTag::new("spare").unwrap();
        let wide = Authority::new([run.clone(), spare.clone()]);
        let kernel = Kernel::admit(
            DefinitionId::new("inputs").unwrap(),
            Schema::new(["node"], ["value"], [run.clone(), spare]).unwrap(),
            Graph::new(
                ["A", "B", "C"].map(|node| Node::new(node).unwrap()),
                [
                    Edge::new("ab", "A", "B").unwrap(),
                    Edge::new("ac", "A", "C").unwrap(),
                ],
            )
            .unwrap(),
            [Contract::new("value", "value", |_| Ok(())).unwrap()],
            ["A", "B", "C"].map(|node| NodeDefinition::new(node, ["node"], "value").unwrap()),
            ["ab", "ac"].map(|edge| {
                EdgeDefinition::new(edge, ["flow"], ["node"], ["node"], "value", [run.clone()])
                    .unwrap()
            }),
            [],
            [RootRule::new("A", wide.clone()).unwrap()],
        )
        .unwrap();
        let bytes: Payload = Arc::from(b"value".as_slice());
        let deliver = |state: &mut State, edge: &str, authority: Authority| {
            let mut proposal = ActivationProposal::root("A", authority, Arc::clone(&bytes));
            proposal.emit(Emission::new(
                edge,
                OutputAuthority::Carry,
                Arc::clone(&bytes),
            ));
            let root = kernel.activate(state, proposal).unwrap();
            state.activation(root).unwrap().outputs().next().unwrap()
        };
        let mut state = kernel.empty_state();
        let outbound = emit(&kernel, &mut state, false);
        let input = emit(&kernel, &mut state, true);
        let elsewhere = deliver(&mut state, "ac", Authority::new([run]));
        let wider = deliver(&mut state, "ab", wide);
        // The greatest identity sorts last, so every producer's records are
        // checked before the consumer's trigger.
        let consumer = ActivationId::from_u128(u128::MAX);
        let transition = kernel
            .evaluate_activation(&state, consumer, ActivationProposal::package(input, bytes))
            .unwrap();
        state.apply(&kernel, &transition).unwrap();
        assert_eq!(
            kernel.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        let rejects = |mutate: &dyn Fn(&mut Checkpoint)| {
            let mut invalid = state.checkpoint();
            mutate(&mut invalid);
            kernel.restore_checkpoint(invalid).unwrap_err()
        };
        // The consumer claims one more input, recorded as consumed by it or not.
        let claim = |c: &mut Checkpoint, package: PackageId, consumed: bool| {
            let Trigger::Pkgs { package_ids } =
                &mut c.activations.get_mut(&consumer).unwrap().trigger
            else {
                panic!("package-triggered fixture");
            };
            package_ids.insert(package);
            if consumed {
                c.packages.get_mut(&package).unwrap().status = PackageStatus::Consumed(consumer);
            }
        };
        let root = input.producer();

        assert_eq!(
            rejects(&|c| {
                c.activations.get_mut(&root).unwrap().trigger = Trigger::Orig {
                    node_id: Arc::from("A"),
                    authority: Authority::new([AuthorityTag::new("foreign").unwrap()]),
                };
            }),
            CheckpointError::Activation("root authority is outside the schema")
        );
        assert_eq!(
            rejects(&|c| {
                c.activations.get_mut(&root).unwrap().trigger = Trigger::Pkgs {
                    package_ids: BTreeSet::new(),
                };
            }),
            CheckpointError::Activation("activation has no input packages")
        );
        // The claim names a known producer, so consumption stays acyclic, but
        // that producer recorded no such output.
        assert_eq!(
            rejects(&|c| claim(c, PackageId::from_parts(root, input.output() + 1), false)),
            CheckpointError::Consumption("activation input is unknown")
        );
        assert_eq!(
            rejects(&|c| claim(c, outbound, false)),
            CheckpointError::Consumption("activation input was never delivered")
        );
        assert_eq!(
            rejects(&|c| c.packages.get_mut(&input).unwrap().status = PackageStatus::Live),
            CheckpointError::Consumption("activation input is not consumed by it")
        );
        // `elsewhere` differs from `input` only in custody, `wider` only in
        // authority.
        let disagree =
            CheckpointError::Consumption("activation inputs disagree on custody or authority");
        assert_eq!(rejects(&|c| claim(c, elsewhere, true)), disagree);
        assert_eq!(rejects(&|c| claim(c, wider, true)), disagree);
        for (id, node) in [(root, "B"), (consumer, "A")] {
            assert_eq!(
                rejects(&|c| c.activations.get_mut(&id).unwrap().node_id = Arc::from(node)),
                CheckpointError::Consumption("recorded execution node disagrees with trigger")
            );
        }
        // A consumed package must be delivered and an input of an accepted
        // package-triggered consumer. The undelivered claim is caught at its
        // producer, which precedes the consumer.
        let unclaimed =
            CheckpointError::Consumption("consumed package is not an input of its consumer");
        for claimant in [consumer, root, ActivationId::from_u128(7)] {
            assert_eq!(
                rejects(&|c| {
                    c.packages.get_mut(&elsewhere).unwrap().status =
                        PackageStatus::Consumed(claimant);
                }),
                unclaimed
            );
        }
        assert_eq!(rejects(&|c| claim(c, outbound, true)), unclaimed);
    }

    #[test]
    fn checkpoint_accepts_a_removed_holder_recorded_by_node_replacement() {
        let (initial, _) = fixture();
        let mut state = initial.empty_state();
        let received = emit(&initial, &mut state, true);
        let tag = AuthorityTag::new("run").unwrap();
        let right = RewriteFragment::new(
            vec![Node::new("A").unwrap(), Node::new("B2").unwrap()],
            vec![Edge::new("ab2", "A", "B2").unwrap()],
            ["A", "B2"]
                .map(|node| NodeDefinition::new(node, ["node"], "value").unwrap())
                .to_vec(),
            vec![
                EdgeDefinition::new("ab2", ["flow"], ["node"], ["node"], "value", [tag.clone()])
                    .unwrap(),
            ],
            vec![],
            vec![RootRule::new("A", Authority::new([tag])).unwrap()],
        );
        let grammar = RewriteGrammar::new([RewriteProduction::new(
            "replace-b",
            RewriteFragment::from_kernel(&initial),
            BTreeSet::from([Arc::from("A")]),
            BTreeSet::new(),
            right,
        )
        .unwrap()])
        .unwrap();
        let request = RewriteRequest::new(
            "replace-b",
            RewriteMatch::new(
                BTreeMap::from([
                    (Arc::from("A"), Arc::from("A")),
                    (Arc::from("B"), Arc::from("B")),
                ]),
                BTreeMap::from([(Arc::from("ab"), Arc::from("ab"))]),
                BTreeMap::from([(Arc::from("B2"), Arc::from("B2"))]),
                BTreeMap::from([(Arc::from("ab2"), Arc::from("ab2"))]),
            ),
        );
        let prepared = initial
            .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
            .unwrap();
        assert_eq!(
            prepared.retirements().get(&received),
            Some(&RetirementReason::HolderRemoved)
        );
        let current = initial.commit_rewrite(&mut state, prepared).unwrap();
        assert!(current.graph().node("B").is_none());
        let record = state.package(received).unwrap();
        assert_eq!(record.holder(), "B");
        assert_eq!(record.phase(), Phase::In);
        assert!(record.retirement().is_some());
        assert_eq!(
            current.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        // `B` is no longer current; its absence from the lifetime set is caught
        // where the historical delivery to it is checked.
        let mut invalid = state.checkpoint();
        invalid.used_node_ids.remove("B");
        assert!(matches!(
            current.restore_checkpoint(invalid),
            Err(CheckpointError::Delivery(_))
        ));
    }

    #[test]
    fn checkpoint_rejects_a_live_receipt_at_an_all_receiver_whose_route_was_removed() {
        let tag = AuthorityTag::new("run").unwrap();
        let authority = Authority::new([tag.clone()]);
        let initial = Kernel::admit(
            DefinitionId::new("all-receipt").unwrap(),
            Schema::new(["node"], ["value"], [tag.clone()]).unwrap(),
            Graph::new(
                [Node::new("A").unwrap(), Node::new("B").unwrap()],
                [Edge::new("ab", "A", "B").unwrap()],
            )
            .unwrap(),
            [Contract::new("value", "value", |_| Ok(())).unwrap()],
            [
                NodeDefinition::new("A", ["node"], "value").unwrap(),
                NodeDefinition::new("B", ["node"], "value")
                    .unwrap()
                    .with_ingress_mode(IngressMode::All),
            ],
            [EdgeDefinition::new("ab", ["flow"], ["node"], ["node"], "value", [tag]).unwrap()],
            [],
            [RootRule::new("A", authority).unwrap()],
        )
        .unwrap();
        let mut state = initial.empty_state();
        let received = emit(&initial, &mut state, true);
        let right = RewriteFragment::new(
            initial.graph().nodes().to_vec(),
            vec![],
            initial.node_definitions().to_vec(),
            vec![],
            vec![],
            initial.roots().to_vec(),
        );
        let names: BTreeSet<Arc<str>> = [Arc::from("A"), Arc::from("B")].into();
        let grammar = RewriteGrammar::new([RewriteProduction::new(
            "disconnect",
            RewriteFragment::from_kernel(&initial),
            names.clone(),
            BTreeSet::new(),
            right,
        )
        .unwrap()])
        .unwrap();
        let request = RewriteRequest::new(
            "disconnect",
            RewriteMatch::new(
                names.into_iter().map(|node| (node.clone(), node)).collect(),
                BTreeMap::from([(Arc::from("ab"), Arc::from("ab"))]),
                BTreeMap::new(),
                BTreeMap::new(),
            ),
        );
        let prepared = initial
            .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
            .unwrap();
        assert_eq!(
            prepared.retirements().get(&received),
            Some(&RetirementReason::RouteRemoved)
        );
        let current = initial.commit_rewrite(&mut state, prepared).unwrap();
        assert_eq!(
            current.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        // The same rows with the receipt still live describe a state cleanup
        // would never produce.
        let mut invalid = state.checkpoint();
        invalid.packages.get_mut(&received).unwrap().status = PackageStatus::Live;
        assert_eq!(
            current.restore_checkpoint(invalid).unwrap_err(),
            CheckpointError::Custody(
                "live receipt at an All receiver names a route that is no longer incoming"
            )
        );
    }

    #[test]
    fn checkpoint_rejects_receipts_that_disagree_on_a_removed_edge() {
        let (initial, _) = fixture();
        let mut state = initial.empty_state();
        let first = emit(&initial, &mut state, true);
        let second = emit(&initial, &mut state, true);
        let right = RewriteFragment::new(
            initial.graph().nodes().to_vec(),
            vec![],
            initial.node_definitions().to_vec(),
            vec![],
            vec![],
            initial.roots().to_vec(),
        );
        let names: BTreeSet<Arc<str>> = [Arc::from("A"), Arc::from("B")].into();
        let grammar = RewriteGrammar::new([RewriteProduction::new(
            "disconnect",
            RewriteFragment::from_kernel(&initial),
            names.clone(),
            BTreeSet::new(),
            right,
        )
        .unwrap()])
        .unwrap();
        let request = RewriteRequest::new(
            "disconnect",
            RewriteMatch::new(
                names.into_iter().map(|node| (node.clone(), node)).collect(),
                BTreeMap::from([(Arc::from("ab"), Arc::from("ab"))]),
                BTreeMap::new(),
                BTreeMap::new(),
            ),
        );
        let prepared = initial
            .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
            .unwrap();
        let current = initial.commit_rewrite(&mut state, prepared).unwrap();
        // Both receipts crossed `ab` from `A` to `B` and stay live at `B`, but
        // the current graph no longer records the incidence of `ab`.
        assert!(current.graph().edge("ab").is_none());
        for receipt in [first, second] {
            let record = state.package(receipt).unwrap();
            assert!(record.is_live());
            assert_eq!(record.holder(), "B");
        }
        assert_eq!(
            current.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        let rejects = |mutate: &dyn Fn(&mut Checkpoint)| {
            let mut invalid = state.checkpoint();
            mutate(&mut invalid);
            current.restore_checkpoint(invalid).unwrap_err()
        };
        let disagree =
            CheckpointError::Delivery("deliveries over one edge disagree on its endpoints");
        // Each claim passes every other check: `A` and `B` are current `Any`
        // nodes and used identities, and `ab` is a used edge identity.
        assert_eq!(
            rejects(&|c| {
                let record = c.packages.get_mut(&second).unwrap();
                record.delivery.as_mut().unwrap().receiver = Arc::from("A");
            }),
            disagree
        );
        assert_eq!(
            rejects(&|c| {
                let root = c.activations.get_mut(&second.producer()).unwrap();
                root.node_id = Arc::from("B");
                let Trigger::Orig { node_id, .. } = &mut root.trigger else {
                    panic!("root fixture");
                };
                *node_id = Arc::from("B");
                c.packages.get_mut(&second).unwrap().producer_node = Arc::from("B");
            }),
            disagree
        );
    }

    #[test]
    fn checkpoint_rejects_edge_identities_without_node_identities() {
        // With no current nodes, no current identity needs to be allocated.
        let kernel = Kernel::admit(
            DefinitionId::new("empty").unwrap(),
            Schema::new([] as [&str; 0], [] as [&str; 0], []).unwrap(),
            Graph::new([], []).unwrap(),
            [],
            [],
            [],
            [],
            [],
        )
        .unwrap();
        let state = kernel.empty_state();
        assert_eq!(
            kernel.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        let rejects = |mutate: &dyn Fn(&mut Checkpoint)| {
            let mut invalid = state.checkpoint();
            mutate(&mut invalid);
            kernel.restore_checkpoint(invalid).unwrap_err()
        };
        assert_eq!(
            rejects(&|c| {
                c.used_edge_ids.insert(Arc::from("ab"));
            }),
            CheckpointError::Identity("edge identities are allocated without any node identity")
        );
        // A node identity for its endpoints is all a removed edge needs.
        let mut valid = state.checkpoint();
        valid.used_node_ids.insert(Arc::from("A"));
        valid.used_edge_ids.insert(Arc::from("ab"));
        assert!(kernel.restore_checkpoint(valid).is_ok());
    }

    #[test]
    fn fragment_encoding_round_trips_and_decodes_through_checked_constructors() {
        let (kernel, _) = fixture();
        let data = FragmentData::from(&RewriteFragment::from_kernel(&kernel));
        assert_eq!(data.version, FRAGMENT_ENCODING_VERSION);
        let json = serde_json::to_value(&data).unwrap();
        let decoded: FragmentData = serde_json::from_value(json.clone()).unwrap();
        let fragment = RewriteFragment::try_from(decoded).unwrap();
        assert_eq!(
            kernel.admit_fragment(&fragment).unwrap().fingerprint(),
            kernel.fingerprint()
        );
        for field in ["node types", "edge authorities", "node identity", "version"] {
            let mut malformed = json.clone();
            match field {
                "node types" => malformed["node_definitions"][0]["types"] = serde_json::json!([]),
                "edge authorities" => {
                    malformed["edge_definitions"][0]["authority_tags"] = serde_json::json!([]);
                }
                "version" => malformed["version"] = serde_json::json!(2),
                _ => malformed["nodes"][0]["id"] = serde_json::json!(""),
            }
            let decoded: FragmentData = serde_json::from_value(malformed).unwrap();
            assert!(RewriteFragment::try_from(decoded).is_err(), "{field}");
        }
    }

    /// The encoding is the format: every field name at every level is pinned,
    /// and a document naming any other field is refused.
    #[test]
    fn fragment_encoding_is_the_pinned_golden_format() {
        let tag = AuthorityTag::new("run").unwrap();
        let kernel =
            Kernel::admit(
                DefinitionId::new("golden").unwrap(),
                Schema::new(["node"], ["value"], [tag.clone()]).unwrap(),
                Graph::new(
                    [Node::new("A").unwrap(), Node::new("B").unwrap()],
                    [Edge::new("ab", "A", "B").unwrap()],
                )
                .unwrap(),
                [Contract::new("value", "value", |_| Ok(())).unwrap()],
                [
                    NodeDefinition::new("A", ["node"], "value").unwrap(),
                    NodeDefinition::new("B", ["node"], "value")
                        .unwrap()
                        .with_ingress_mode(IngressMode::All),
                ],
                [EdgeDefinition::new(
                    "ab",
                    ["flow"],
                    ["node"],
                    [] as [&str; 0],
                    "value",
                    [tag.clone()],
                )
                .unwrap()
                .with_authority_match(AuthorityMatch::AllOf)],
                [AuthorityTransitionRule::new(
                    "A",
                    Authority::new([tag.clone()]),
                    Authority::new([]),
                )
                .unwrap()],
                [RootRule::new("A", Authority::new([tag])).unwrap()],
            )
            .unwrap();
        let data = FragmentData::from(&RewriteFragment::from_kernel(&kernel));
        let encoded = serde_json::to_string(&data).unwrap();
        let golden = concat!(
            r#"{"version":1,"#,
            r#""nodes":[{"id":"A"},{"id":"B"}],"#,
            r#""edges":[{"id":"ab","source":"A","target":"B"}],"#,
            r#""node_definitions":["#,
            r#"{"node_id":"A","types":["node"],"result_contract":"value","ingress_mode":"Any"},"#,
            r#"{"node_id":"B","types":["node"],"result_contract":"value","ingress_mode":"All"}],"#,
            r#""edge_definitions":[{"edge_id":"ab","types":["flow"],"source_requirements":["node"],"#,
            r#""target_requirements":[],"package_contract":"value","authority_tags":["run"],"#,
            r#""authority_match":"AllOf"}],"#,
            r#""authority_transitions":[{"node_id":"A","from":["run"],"to":[]}],"#,
            r#""roots":[{"node_id":"A","ceiling":["run"]}]}"#,
        );
        assert_eq!(encoded, golden);
        let decoded: FragmentData = serde_json::from_str(golden).unwrap();
        assert_eq!(decoded, data);
        assert_eq!(serde_json::to_string(&decoded).unwrap(), golden);

        for (level, extra) in [
            (
                "top",
                golden.replacen("{\"version\":1,", "{\"version\":1,\"colour\":1,", 1),
            ),
            (
                "node",
                golden.replacen("{\"id\":\"A\"}", "{\"id\":\"A\",\"colour\":1}", 1),
            ),
            (
                "root",
                golden.replacen(
                    "{\"node_id\":\"A\",\"ceiling\"",
                    "{\"node_id\":\"A\",\"x\":0,\"ceiling\"",
                    1,
                ),
            ),
        ] {
            assert!(
                serde_json::from_str::<FragmentData>(&extra).is_err(),
                "unknown field accepted at {level}"
            );
        }
        assert!(
            serde_json::from_str::<FragmentData>(&golden.replacen("\"version\":1,", "", 1))
                .is_err()
        );
    }
}
