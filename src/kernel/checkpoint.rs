//! Current accepted state for trusted storage, without historical rule replay.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::Deserialize;

use crate::graph::{
    Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, Edge, EdgeDefinition,
    IngressMode, Node, NodeDefinition, RootRule,
};

use super::definition::Kernel;
use super::frontier::{Delivery, Phase, Position, Retirement, RetirementReason};
use super::occurrence::{Activation, ActivationId, Package, PackageId, State, Trigger};
use super::rewrite::RewriteFragment;

pub(crate) struct Checkpoint {
    pub(crate) activations: BTreeMap<ActivationId, Activation>,
    pub(crate) packages: BTreeMap<PackageId, Package>,
    pub(crate) positions: BTreeMap<PackageId, Position>,
    pub(crate) deliveries: BTreeMap<PackageId, Delivery>,
    pub(crate) retirements: BTreeMap<PackageId, Retirement>,
    pub(crate) used_node_ids: BTreeSet<Arc<str>>,
    pub(crate) used_edge_ids: BTreeSet<Arc<str>>,
    pub(crate) revision: u64,
}

impl State {
    #[cfg(test)]
    pub(crate) fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            activations: self.activations.clone(),
            packages: self.packages.clone(),
            positions: self.positions.clone(),
            deliveries: self.deliveries.clone(),
            retirements: self.retirements.clone(),
            used_node_ids: self.used_node_ids.clone(),
            used_edge_ids: self.used_edge_ids.clone(),
            revision: self.revision,
        }
    }

    pub(crate) fn used_node_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.used_node_ids
    }

    pub(crate) fn used_edge_ids(&self) -> &BTreeSet<Arc<str>> {
        &self.used_edge_ids
    }
}

impl Kernel {
    /// Checks a trusted current snapshot's references and custody invariants.
    ///
    /// This does not establish historical reachability or rerun contracts or cleanup.
    pub(crate) fn restore_checkpoint(&self, checkpoint: Checkpoint) -> Result<State, &'static str> {
        let Checkpoint {
            activations,
            packages,
            positions,
            deliveries,
            retirements,
            used_node_ids,
            used_edge_ids,
            revision,
        } = checkpoint;
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
            return Err(
                "current graph identities are missing or malformed in lifetime allocation records",
            );
        }
        if activations
            .values()
            .map(|activation| activation.outputs.len())
            .sum::<usize>()
            != packages.len()
            || deliveries
                .keys()
                .any(|package| !packages.contains_key(package))
        {
            return Err("package records do not correspond to activation outputs");
        }
        let mut consumed_by = BTreeMap::new();
        let mut indegrees = BTreeMap::new();
        let mut children = BTreeMap::<ActivationId, Vec<ActivationId>>::new();
        let mut explicit_transfers = 0_u64;
        for (&id, activation) in &activations {
            let node = match &activation.trigger {
                Trigger::Orig { node_id, authority } => {
                    if !self.schema().admits_authority(authority) {
                        return Err("root authority is outside the fixed schema");
                    }
                    indegrees.insert(id, 0);
                    node_id
                }
                Trigger::Pkgs { package_ids } => {
                    let first = package_ids
                        .first()
                        .and_then(|package| packages.get(package))
                        .ok_or("activation has no existing input packages")?;
                    indegrees.insert(id, package_ids.len());
                    for package in package_ids {
                        let input = packages.get(package).ok_or("activation input is unknown")?;
                        if input.node_id != first.node_id
                            || input.authority != first.authority
                            || !deliveries.contains_key(package)
                            || consumed_by.insert(*package, id).is_some()
                        {
                            return Err(
                                "activation input custody or unique consumption is inconsistent",
                            );
                        }
                        children.entry(package.producer()).or_default().push(id);
                    }
                    &first.node_id
                }
            };
            if !used_node_ids.contains(node) {
                return Err("historical execution node is absent from lifetime allocations");
            }
            for (&package_id, output) in &activation.outputs {
                let package = packages
                    .get(&package_id)
                    .ok_or("activation output is absent")?;
                if package_id.producer() != id
                    || package.object_type != output.object_type
                    || package.authority != output.authority
                    || package.content_digest != output.content_digest
                    || !self.schema().admits_object_type(package.object_type())
                    || !self.schema().admits_authority(package.authority())
                {
                    return Err("package immutable fields disagree with its producing activation");
                }
                if let Some(delivery) = deliveries.get(&package_id) {
                    if delivery.source() != &**node
                        || package.node_id() != delivery.receiver()
                        || package.edge_id() != Some(delivery.edge_id())
                        || output
                            .edge_id()
                            .is_some_and(|edge| edge != delivery.edge_id())
                        || !used_node_ids.contains(delivery.receiver())
                        || !used_edge_ids.contains(delivery.edge_id())
                        || self.graph().edge(delivery.edge_id()).is_some_and(|edge| {
                            edge.source() != delivery.source()
                                || edge.target() != delivery.receiver()
                        })
                    {
                        return Err(
                            "delivery receipt is inconsistent with historical package custody",
                        );
                    }
                    if output.edge_id().is_none() {
                        explicit_transfers = explicit_transfers
                            .checked_add(1)
                            .ok_or("revision overflow")?;
                    }
                } else if output.edge_id().is_some()
                    || package.edge_id().is_some()
                    || package.node_id() != &**node
                {
                    return Err("undelivered package is inconsistent with its producing node");
                }
            }
        }
        let mut ready: Vec<_> = indegrees
            .iter()
            .filter_map(|(&id, &degree)| (degree == 0).then_some(id))
            .collect();
        let mut visited = 0;
        while let Some(id) = ready.pop() {
            visited += 1;
            for child in children.get(&id).into_iter().flatten() {
                let degree = indegrees
                    .get_mut(child)
                    .expect("every consumer was indexed");
                *degree -= 1;
                if *degree == 0 {
                    ready.push(*child);
                }
            }
        }
        if visited != activations.len() {
            return Err("accepted activation references contain a causal cycle");
        }
        for (id, position) in &positions {
            let package = packages
                .get(id)
                .ok_or("live frontier names an unknown package")?;
            if consumed_by.contains_key(id)
                || self.graph().node(position.holder()).is_none()
                || package.node_id() != position.holder()
                || (position.phase() == Phase::In) != deliveries.contains_key(id)
            {
                return Err("live frontier custody, phase or consumption is inconsistent");
            }
        }
        let mut explicit_retirements = 0_u64;
        let mut structural_retirements = false;
        for (id, retirement) in &retirements {
            let package = packages
                .get(id)
                .ok_or("retirement names an unknown package")?;
            if consumed_by.contains_key(id) || positions.contains_key(id) {
                return Err("retired package is consumed or live");
            }
            if !retirement.is_consistent()
                || package.node_id() != retirement.holder()
                || !used_node_ids.contains(retirement.holder())
                || (retirement.phase() == Phase::In) != deliveries.contains_key(id)
                || retirement.revision() == 0
                || retirement.revision() > revision
                || retirement
                    .evidence()
                    .is_some_and(|evidence| !activations.contains_key(&evidence))
            {
                return Err("retirement record is inconsistent with package history");
            }
            if retirement.reason() == RetirementReason::Explicit {
                explicit_retirements = explicit_retirements
                    .checked_add(1)
                    .ok_or("revision overflow")?;
            } else {
                structural_retirements = true;
            }
        }
        if positions.len() + consumed_by.len() + retirements.len() != packages.len() {
            return Err("packages are not partitioned into live, consumed, and retired");
        }
        // Structural retirements only arise from a rewrite, which is at least one
        // further revision; without it a fixed-graph export would drop them.
        let minimum_revision = u64::try_from(activations.len())
            .ok()
            .and_then(|count| count.checked_add(explicit_transfers))
            .and_then(|count| count.checked_add(explicit_retirements))
            .and_then(|count| count.checked_add(u64::from(structural_retirements)))
            .ok_or("revision overflow")?;
        if revision < minimum_revision {
            return Err(
                "state revision predates its accepted activations, transfers, or retirements",
            );
        }
        Ok(State {
            definition_id: self.id().clone(),
            definition_fingerprint: *self.fingerprint(),
            activations,
            packages,
            consumed_by,
            positions,
            deliveries,
            retirements,
            revision,
            used_node_ids,
            used_edge_ids,
        })
    }
}

// Decode persisted graph data through the same checked constructors as live definitions.
// Constrained public graph types deliberately do not gain unchecked Deserialize implementations.
#[derive(Deserialize)]
struct FragmentData {
    nodes: Vec<NodeData>,
    edges: Vec<EdgeData>,
    node_definitions: Vec<NodeDataDefinition>,
    edge_definitions: Vec<EdgeDataDefinition>,
    authority_transitions: Vec<TransitionData>,
    roots: Vec<RootData>,
}

#[derive(Deserialize)]
struct NodeData {
    id: Arc<str>,
}
#[derive(Deserialize)]
struct EdgeData {
    id: Arc<str>,
    source: Arc<str>,
    target: Arc<str>,
}
#[derive(Deserialize)]
struct NodeDataDefinition {
    node_id: Arc<str>,
    types: BTreeSet<Arc<str>>,
    result_contract: Arc<str>,
    ingress_mode: IngressMode,
}
#[derive(Deserialize)]
struct EdgeDataDefinition {
    edge_id: Arc<str>,
    types: BTreeSet<Arc<str>>,
    source_requirements: BTreeSet<Arc<str>>,
    target_requirements: BTreeSet<Arc<str>>,
    package_contract: Arc<str>,
    authority_tags: BTreeSet<AuthorityTag>,
    authority_match: AuthorityMatch,
}
#[derive(Deserialize)]
struct TransitionData {
    node_id: Arc<str>,
    from: Authority,
    to: Authority,
}
#[derive(Deserialize)]
struct RootData {
    node_id: Arc<str>,
    ceiling: Authority,
}

impl<'de> Deserialize<'de> for RewriteFragment {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let data = FragmentData::deserialize(deserializer)?;
        let build = || -> Result<Self, crate::graph::DefinitionError> {
            Ok(Self::new(
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
                        Ok(
                            NodeDefinition::new(node.node_id, node.types, node.result_contract)?
                                .with_ingress_mode(node.ingress_mode),
                        )
                    })
                    .collect::<Result<_, crate::graph::DefinitionError>>()?,
                data.edge_definitions
                    .into_iter()
                    .map(|edge| {
                        Ok(EdgeDefinition::new(
                            edge.edge_id,
                            edge.types,
                            edge.source_requirements,
                            edge.target_requirements,
                            edge.package_contract,
                            edge.authority_tags,
                        )?
                        .with_authority_match(edge.authority_match))
                    })
                    .collect::<Result<_, crate::graph::DefinitionError>>()?,
                data.authority_transitions
                    .into_iter()
                    .map(|rule| AuthorityTransitionRule::new(rule.node_id, rule.from, rule.to))
                    .collect::<Result<_, _>>()?,
                data.roots
                    .into_iter()
                    .map(|root| RootRule::new(root.node_id, root.ceiling))
                    .collect::<Result<_, _>>()?,
            ))
        };
        build().map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        ActivationProposal, Contract, DefinitionId, Emission, Graph, OutputAuthority, Payload,
        RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest, Schema,
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

        let mut invalid = state.checkpoint();
        invalid.used_edge_ids.remove("ab");
        assert!(current.restore_checkpoint(invalid).is_err());
        let mut invalid = state.checkpoint();
        invalid
            .positions
            .insert(unsupported, Position::new("B", Phase::Out));
        assert!(current.restore_checkpoint(invalid).is_err());
        let mut invalid = state.checkpoint();
        invalid.packages.get_mut(&unsupported).unwrap().object_type = Arc::from("changed");
        assert!(current.restore_checkpoint(invalid).is_err());
        let mut invalid = state.checkpoint();
        invalid
            .activations
            .get_mut(&received.producer())
            .unwrap()
            .trigger = Trigger::Pkgs {
            package_ids: BTreeSet::from([received]),
        };
        invalid.deliveries.get_mut(&received).unwrap().source = Arc::from("B");
        invalid.positions.remove(&received);
        assert_eq!(
            current.restore_checkpoint(invalid).unwrap_err(),
            "accepted activation references contain a causal cycle"
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
            kernel.restore_checkpoint(invalid).is_err()
        };
        assert!(rejects(&|c| {
            c.retirements.remove(&received);
        }));
        assert!(rejects(&|c| {
            c.positions.insert(received, Position::new("B", Phase::In));
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&received).unwrap().reason = RetirementReason::NoAcceptingEdge;
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().reason = RetirementReason::RouteRemoved;
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().evidence = Some(ActivationId::from_u128(7));
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().holder = Arc::from("B");
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().revision = 0;
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().revision = c.revision + 1;
        }));
        assert!(rejects(&|c| {
            c.retirements.get_mut(&outbound).unwrap().phase = Phase::In;
        }));
        assert!(rejects(&|c| {
            c.revision -= 1;
        }));
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
        let retirement = state.retirement(received).unwrap();
        assert_eq!(retirement.holder(), "B");
        assert_eq!(retirement.phase(), Phase::In);
        assert_eq!(
            current.restore_checkpoint(state.checkpoint()).unwrap(),
            state
        );

        let mut invalid = state.checkpoint();
        invalid.retirements.get_mut(&received).unwrap().holder = Arc::from("A");
        assert!(current.restore_checkpoint(invalid).is_err());
        let mut invalid = state.checkpoint();
        invalid.used_node_ids.remove("B");
        assert!(current.restore_checkpoint(invalid).is_err());
    }

    #[test]
    fn graph_checkpoint_decoding_preserves_constructor_invariants() {
        let (kernel, _) = fixture();
        let original = serde_json::to_value(RewriteFragment::from_kernel(&kernel)).unwrap();
        let fragment: RewriteFragment = serde_json::from_value(original.clone()).unwrap();
        assert_eq!(
            kernel.admit_fragment(&fragment).unwrap().fingerprint(),
            kernel.fingerprint()
        );
        for field in ["node types", "edge authorities", "node identity"] {
            let mut malformed = original.clone();
            match field {
                "node types" => malformed["node_definitions"][0]["types"] = serde_json::json!([]),
                "edge authorities" => {
                    malformed["edge_definitions"][0]["authority_tags"] = serde_json::json!([]);
                }
                _ => malformed["nodes"][0]["id"] = serde_json::json!(""),
            }
            assert!(serde_json::from_value::<RewriteFragment>(malformed).is_err());
        }
    }
}
