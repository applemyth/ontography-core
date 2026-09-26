//! The negative half of T1: a transition evaluated over a stale or unfaithful
//! view is rejected by `State::apply` against the true state, with the exact
//! `ApplyError` naming the violated precondition, and the state is unchanged.
//!
//! Every variant of `ApplyError` is reached here. Forgeries are views that lie
//! about records, accepted activations, the live frontier, lifetime
//! identities, or the binding; `DefinitionMismatch` needs no forgery, only a
//! kernel other than the evaluating one.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::storage::{
    ApplyError, Binding, FrontierView, PackageRecord, PackageStatus, PackageView, Transition,
};
use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, Contract, DefinitionId, Delivery,
    Edge, EdgeDefinition, Emission, Graph, IngressMode, Kernel, Node, NodeDefinition,
    OutputAuthority, PackageId, RewriteError, RewriteFragment, RewriteGrammar, RewriteMatch,
    RewriteProduction, RewriteRequest, RootRule, Schema, State,
};

fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

/// (edge, source, target, contract)
type EdgeSpec = (&'static str, &'static str, &'static str, &'static str);

const NODES: [&str; 3] = ["a", "b", "c"];
const EDGES: [EdgeSpec; 4] = [
    ("e1", "a", "b", "item"),
    ("e2", "a", "c", "item"),
    ("e3", "a", "c", "item"),
    ("e4", "b", "a", "item"),
];

/// `a` and `b` are rootable; `b` and `a` receive with `Any`, `c` with `All`
/// over `e2` and `e3`. The `note` contract accepts only `Note` payloads, so an
/// edge carrying it rejects every `Item` package on metadata alone.
fn admit(id: &str, nodes: &[&str], edges: &[EdgeSpec]) -> Kernel {
    Kernel::admit(
        DefinitionId::new(id).unwrap(),
        Schema::new(["Node"], ["Result", "Item", "Note"], [tag("route")]).unwrap(),
        Graph::new(
            nodes.iter().map(|node| Node::new(*node).unwrap()),
            edges
                .iter()
                .map(|(edge, source, target, _)| Edge::new(*edge, *source, *target).unwrap()),
        )
        .unwrap(),
        [
            Contract::new("result", "Result", |_| Ok(())).unwrap(),
            Contract::new("item", "Item", |_| Ok(())).unwrap(),
            Contract::new("note", "Note", |_| Ok(())).unwrap(),
        ],
        nodes.iter().map(|node| {
            let definition = NodeDefinition::new(*node, ["Node"], "result").unwrap();
            if *node == "c" {
                definition.with_ingress_mode(IngressMode::All)
            } else {
                definition
            }
        }),
        edges.iter().map(|(edge, _, _, contract)| {
            EdgeDefinition::new(
                *edge,
                ["Flow"],
                ["Node"],
                ["Node"],
                *contract,
                [tag("route")],
            )
            .unwrap()
        }),
        [],
        nodes
            .iter()
            .filter(|node| **node != "c")
            .map(|node| RootRule::new(*node, Authority::new([tag("route")])).unwrap()),
    )
    .unwrap()
}

fn kernel() -> Kernel {
    admit("verify", &NODES, &EDGES)
}

/// The sub-definition of `kernel` on `nodes` and `edges`, as a rule fragment.
fn fragment(kernel: &Kernel, nodes: &[&str], edges: &[&str]) -> RewriteFragment {
    let nodes: BTreeSet<&str> = nodes.iter().copied().collect();
    let edges: BTreeSet<&str> = edges.iter().copied().collect();
    RewriteFragment::new(
        kernel
            .graph()
            .nodes()
            .iter()
            .filter(|node| nodes.contains(node.id()))
            .cloned()
            .collect(),
        kernel
            .graph()
            .edges()
            .iter()
            .filter(|edge| edges.contains(edge.id()))
            .cloned()
            .collect(),
        kernel
            .node_definitions()
            .iter()
            .filter(|node| nodes.contains(node.node_id()))
            .cloned()
            .collect(),
        kernel
            .edge_definitions()
            .iter()
            .filter(|edge| edges.contains(edge.edge_id()))
            .cloned()
            .collect(),
        Vec::new(),
        kernel
            .roots()
            .iter()
            .filter(|root| nodes.contains(root.node_id()))
            .cloned()
            .collect(),
    )
}

fn ids(pairs: &[(&str, &str)]) -> BTreeMap<Arc<str>, Arc<str>> {
    pairs
        .iter()
        .map(|(symbol, actual)| (Arc::from(*symbol), Arc::from(*actual)))
        .collect()
}

fn names(values: &[&str]) -> BTreeSet<Arc<str>> {
    values.iter().map(|value| Arc::from(*value)).collect()
}

fn root(kernel: &Kernel, state: &mut State, node: &str, emissions: &[Emission]) -> ActivationId {
    let mut proposal =
        ActivationProposal::root(node, Authority::new([tag("route")]), bytes(b"result"));
    for emission in emissions {
        proposal.emit(emission.clone());
    }
    kernel.activate(state, proposal).unwrap()
}

fn outbound() -> Emission {
    Emission::outbound("Item", OutputAuthority::Carry, bytes(b"item"))
}

fn delivered(edge: &str) -> Emission {
    Emission::new(edge, OutputAuthority::Carry, bytes(b"item"))
}

/// The bytes every Item package in these fixtures carries.
fn payload()
-> impl FnMut(PackageId, ontography::ContentDigest) -> Result<Arc<[u8]>, RewriteError> + Copy {
    |_, _| Ok(bytes(b"item"))
}

/// A view over a real state that lies where told to.
#[derive(Default)]
struct Forgery {
    records: BTreeMap<PackageId, Option<PackageRecord>>,
    activations: BTreeMap<ActivationId, bool>,
    live: Option<Vec<(PackageId, PackageRecord)>>,
    used_node_ids: Option<BTreeSet<Arc<str>>>,
    used_edge_ids: Option<BTreeSet<Arc<str>>>,
    binding: Option<Binding>,
}

struct Forged<'a> {
    truth: &'a State,
    lie: Forgery,
}

impl PackageView for Forged<'_> {
    fn record(&self, package: PackageId) -> Option<PackageRecord> {
        match self.lie.records.get(&package) {
            Some(forged) => forged.clone(),
            None => self.truth.package(package).cloned(),
        }
    }

    fn activation_known(&self, activation: ActivationId) -> bool {
        self.lie
            .activations
            .get(&activation)
            .copied()
            .unwrap_or_else(|| self.truth.activation(activation).is_some())
    }

    fn binding(&self) -> Binding {
        self.lie
            .binding
            .clone()
            .unwrap_or_else(|| self.truth.binding())
    }
}

impl FrontierView for Forged<'_> {
    fn live(&self) -> Vec<(PackageId, PackageRecord)> {
        self.lie
            .live
            .clone()
            .unwrap_or_else(|| FrontierView::live(self.truth))
    }

    fn used_node_ids(&self) -> BTreeSet<Arc<str>> {
        self.lie
            .used_node_ids
            .clone()
            .unwrap_or_else(|| self.truth.used_node_ids().clone())
    }

    fn used_edge_ids(&self) -> BTreeSet<Arc<str>> {
        self.lie
            .used_edge_ids
            .clone()
            .unwrap_or_else(|| self.truth.used_edge_ids().clone())
    }
}

fn forged(truth: &State, lie: Forgery) -> Forged<'_> {
    Forged { truth, lie }
}

/// Applies `transition` to `state` under `kernel`, asserting the exact
/// rejection and that the state, including its binding, is untouched (T2).
fn rejects(kernel: &Kernel, state: &mut State, transition: &Transition, expected: ApplyError) {
    let before = state.clone();
    let binding = state.binding();
    assert_eq!(state.apply(kernel, transition), Err(expected));
    assert_eq!(*state, before);
    assert_eq!(state.binding(), binding);
}

fn out_record(state: &State, package: PackageId) -> PackageRecord {
    let record = state.package(package).unwrap();
    PackageRecord::new(
        record.object_type(),
        record.authority().clone(),
        record.content_digest(),
        record.producer_node(),
        None,
        PackageStatus::Live,
    )
}

fn record_at(state: &State, package: PackageId, edge: &str, receiver: &str) -> PackageRecord {
    let record = state.package(package).unwrap();
    PackageRecord::new(
        record.object_type(),
        record.authority().clone(),
        record.content_digest(),
        record.producer_node(),
        Some(Delivery::new(edge, receiver)),
        PackageStatus::Live,
    )
}

#[test]
fn a_faithful_view_applies_and_a_wrong_kernel_or_binding_is_refused() {
    let kernel = kernel();
    let mut state = kernel.empty_state();
    let package = PackageId::from_parts(root(&kernel, &mut state, "a", &[outbound()]), 0);

    let transition = kernel.evaluate_retire(&state, package, None).unwrap();
    let other = admit("other", &NODES, &EDGES);
    rejects(
        &other,
        &mut state,
        &transition,
        ApplyError::DefinitionMismatch,
    );

    let mut nonce_lie = Forgery::default();
    let binding = state.binding();
    nonce_lie.binding = Some(Binding::new(
        binding.definition_id().clone(),
        *binding.definition_fingerprint(),
        binding.revision(),
        binding.nonce() ^ 1,
    ));
    let view = forged(&state, nonce_lie);
    let forged_extension = kernel
        .evaluate_extension_transition(&view, &admit_extended(&kernel))
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &forged_extension,
        ApplyError::BindingMismatch,
    );

    // Clones share a binding until they diverge.
    let mut twin = state.clone();
    let shared = kernel.evaluate_retire(&twin, package, None).unwrap();
    state.apply(&kernel, &shared).unwrap();
    let mut diverged = twin.clone();
    root(&kernel, &mut diverged, "b", &[]);
    let from_twin = kernel.evaluate_retire(&twin, package, None).unwrap();
    rejects(
        &kernel,
        &mut diverged,
        &from_twin,
        ApplyError::BindingMismatch,
    );
    twin.apply(&kernel, &from_twin).unwrap();
    assert_eq!(twin, state);
}

/// The same definition with one more object type: a valid extension whose
/// contracts share the base kernel's validators.
fn admit_extended(kernel: &Kernel) -> Kernel {
    Kernel::admit(
        kernel.id().clone(),
        Schema::new(
            ["Node"],
            ["Result", "Item", "Note", "Extra"],
            [tag("route")],
        )
        .unwrap(),
        kernel.graph().clone(),
        kernel.contracts().to_vec(),
        kernel.node_definitions().to_vec(),
        kernel.edge_definitions().to_vec(),
        kernel.authority_transitions().to_vec(),
        kernel.roots().to_vec(),
    )
    .unwrap()
}

#[test]
fn activation_forgeries_are_rejected_by_the_true_state() {
    let kernel = kernel();
    let mut state = kernel.empty_state();
    let producer = root(
        &kernel,
        &mut state,
        "a",
        &[delivered("e1"), delivered("e1")],
    );
    let (p, q) = (
        PackageId::from_parts(producer, 0),
        PackageId::from_parts(producer, 1),
    );
    let unrouted = PackageId::from_parts(root(&kernel, &mut state, "a", &[outbound()]), 0);

    // ActivationExists: the identity is already accepted.
    let reused = kernel
        .evaluate_activation(
            &state,
            producer,
            ActivationProposal::package(p, bytes(b"result")),
        )
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &reused,
        ApplyError::ActivationExists(producer),
    );

    // NotDelivered: the view claims an outbound package was delivered.
    let mut lie = Forgery::default();
    lie.records
        .insert(unrouted, Some(record_at(&state, unrouted, "e1", "b")));
    let phantom_delivery = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(1),
            ActivationProposal::package(unrouted, bytes(b"result")),
        )
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &phantom_delivery,
        ApplyError::NotDelivered(unrouted),
    );

    // InputCustody: the view moves `q` to `c` so the All join evaluates there.
    let mut lie = Forgery::default();
    lie.records.insert(p, Some(record_at(&state, p, "e2", "c")));
    lie.records.insert(q, Some(record_at(&state, q, "e3", "c")));
    let mut lie_one_moved = Forgery::default();
    lie_one_moved
        .records
        .insert(q, Some(record_at(&state, q, "e3", "c")));
    let mut truth_p_at_c = state.clone();
    let _ = &mut truth_p_at_c;
    let join = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(2),
            ActivationProposal::join([p, q], bytes(b"result")),
        )
        .unwrap();
    // Both inputs are truly at `b`; the evaluator believed `c`. Without
    // outputs the custody is consistent, so the executing node disagrees only
    // where an output records it.
    let mut with_output = ActivationProposal::join([p, q], bytes(b"result"));
    with_output.emit(outbound());
    let mut lie = Forgery::default();
    lie.records.insert(p, Some(record_at(&state, p, "e2", "c")));
    lie.records.insert(q, Some(record_at(&state, q, "e3", "c")));
    let mismatched = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(3),
            with_output,
        )
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &mismatched,
        ApplyError::OutputMismatch(PackageId::from_parts(ActivationId::from_u128(3), 0)),
    );
    drop(join);

    // InputCustody proper: one input truly at `c`, the other truly at `b`.
    let at_c = PackageId::from_parts(root(&kernel, &mut state, "a", &[delivered("e2")]), 0);
    let mut lie = Forgery::default();
    lie.records.insert(q, Some(record_at(&state, q, "e3", "c")));
    let split = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(4),
            ActivationProposal::join([at_c, q], bytes(b"result")),
        )
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &split,
        ApplyError::InputCustody(ActivationId::from_u128(4)),
    );

    // UnknownPackage: the view invents a package.
    let phantom = PackageId::from_parts(ActivationId::from_u128(9), 0);
    let mut lie = Forgery::default();
    lie.records
        .insert(phantom, Some(record_at(&state, p, "e1", "b")));
    let invented = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(5),
            ActivationProposal::package(phantom, bytes(b"result")),
        )
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &invented,
        ApplyError::UnknownPackage(phantom),
    );

    // NotLive: the view resurrects a consumed package.
    kernel
        .activate(&mut state, ActivationProposal::package(p, bytes(b"result")))
        .unwrap();
    let mut lie = Forgery::default();
    lie.records.insert(p, Some(record_at(&state, p, "e1", "b")));
    let resurrected = kernel
        .evaluate_activation(
            &forged(&state, lie),
            ActivationId::from_u128(6),
            ActivationProposal::package(p, bytes(b"result")),
        )
        .unwrap();
    rejects(&kernel, &mut state, &resurrected, ApplyError::NotLive(p));
}

#[test]
fn transfer_and_retire_forgeries_are_rejected_by_the_true_state() {
    let kernel = kernel();
    let mut state = kernel.empty_state();
    let at_b = PackageId::from_parts(root(&kernel, &mut state, "b", &[outbound()]), 0);
    let received = PackageId::from_parts(root(&kernel, &mut state, "a", &[delivered("e1")]), 0);

    // EdgeIncidence: the view says `at_b` was produced at `a`, so `e1` looks
    // like a legal route; the true producer is `b`.
    let mut lie = Forgery::default();
    let record = state.package(at_b).unwrap();
    lie.records.insert(
        at_b,
        Some(PackageRecord::new(
            record.object_type(),
            record.authority().clone(),
            record.content_digest(),
            "a",
            None,
            PackageStatus::Live,
        )),
    );
    let misrouted = kernel
        .evaluate_transfer(&forged(&state, lie), at_b, "e1", payload())
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &misrouted,
        ApplyError::EdgeIncidence(at_b),
    );

    // AlreadyDelivered: the view hides a delivery.
    let mut lie = Forgery::default();
    lie.records
        .insert(received, Some(out_record(&state, received)));
    let redelivered = kernel
        .evaluate_transfer(&forged(&state, lie), received, "e1", payload())
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &redelivered,
        ApplyError::AlreadyDelivered(received),
    );

    // UnknownEvidence: the view vouches for an activation that does not exist.
    let unknown = ActivationId::from_u128(77);
    let mut lie = Forgery::default();
    lie.activations.insert(unknown, true);
    let vouched = kernel
        .evaluate_retire(&forged(&state, lie), at_b, Some(unknown))
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &vouched,
        ApplyError::UnknownEvidence(unknown),
    );

    // NotLive: retiring a package the view pretends is still live.
    kernel.retire(&mut state, at_b, None).unwrap();
    let mut lie = Forgery::default();
    lie.records.insert(at_b, Some(out_record(&state, at_b)));
    let twice = kernel
        .evaluate_retire(&forged(&state, lie), at_b, None)
        .unwrap();
    rejects(&kernel, &mut state, &twice, ApplyError::NotLive(at_b));
    let moved = kernel
        .evaluate_transfer(
            &forged(&state, Forgery::default()),
            received,
            "e1",
            payload(),
        )
        .unwrap_err();
    assert!(matches!(moved, ontography::TransferError::NotOutbound(_)));
}

#[test]
fn rewrite_forgeries_are_rejected_by_the_true_state() {
    let kernel = kernel();
    let mut state = kernel.empty_state();
    let received = PackageId::from_parts(root(&kernel, &mut state, "a", &[delivered("e1")]), 0);

    // Productions: `reroute` replaces every edge out of `a` with `e5`, whose
    // contract rejects Items; `drop_b` deletes `b` with its edges;
    // `drop_e4` deletes `e4`; `readd` adds an edge under a supplied identity.
    let all = fragment(&kernel, &NODES, &["e1", "e2", "e3", "e4"]);
    let mut rerouted = fragment(&kernel, &NODES, &["e4"]);
    rerouted = with_edge(rerouted, "e5", "a", "b", "note");
    let readd_right = with_edge(fragment(&kernel, &["a", "b"], &[]), "x", "b", "a", "item");
    let grammar = RewriteGrammar::new([
        RewriteProduction::new(
            "reroute",
            all.clone(),
            names(&NODES),
            names(&["e4"]),
            rerouted,
        )
        .unwrap(),
        RewriteProduction::new(
            "drop_b",
            all.clone(),
            names(&["a", "c"]),
            names(&["e2", "e3"]),
            fragment(&kernel, &["a", "c"], &["e2", "e3"]),
        )
        .unwrap(),
        RewriteProduction::new(
            "drop_e4",
            fragment(&kernel, &["a", "b"], &["e4"]),
            names(&["a", "b"]),
            BTreeSet::new(),
            fragment(&kernel, &["a", "b"], &[]),
        )
        .unwrap(),
        RewriteProduction::new(
            "readd",
            fragment(&kernel, &["a", "b"], &[]),
            names(&["a", "b"]),
            BTreeSet::new(),
            readd_right,
        )
        .unwrap(),
    ])
    .unwrap();
    let identity = ids(&[("a", "a"), ("b", "b"), ("c", "c")]);
    let all_edges = ids(&[("e1", "e1"), ("e2", "e2"), ("e3", "e3"), ("e4", "e4")]);

    // RetirementInconsistent: the view shows the receipt as still outbound at
    // `a`, so the reroute retires it as NoAcceptingEdge; it is truly In at `b`.
    let mut lie = Forgery::default();
    let as_out = out_record(&state, received);
    lie.records.insert(received, Some(as_out.clone()));
    lie.live = Some(vec![(received, as_out)]);
    let reroute = RewriteRequest::new(
        "reroute",
        RewriteMatch::new(
            identity.clone(),
            all_edges.clone(),
            ids(&[]),
            ids(&[("e5", "e5")]),
        ),
    );
    let (inconsistent, _) = kernel
        .evaluate_rewrite(&forged(&state, lie), &grammar, &reroute, payload())
        .unwrap();
    assert_eq!(
        inconsistent.retirements().get(&received),
        Some(&ontography::RetirementReason::NoAcceptingEdge)
    );
    rejects(
        &kernel,
        &mut state,
        &inconsistent,
        ApplyError::RetirementInconsistent(received),
    );

    // StrandedHolder: the view hides the live receipt at `b`, so deleting `b`
    // retires nothing; the true receipt would be stranded.
    let lie = Forgery {
        live: Some(Vec::new()),
        ..Forgery::default()
    };
    let drop_b = RewriteRequest::new(
        "drop_b",
        RewriteMatch::new(identity.clone(), all_edges.clone(), ids(&[]), ids(&[])),
    );
    let (stranding, _) = kernel
        .evaluate_rewrite(&forged(&state, lie), &grammar, &drop_b, payload())
        .unwrap();
    assert!(stranding.retirements().is_empty());
    rejects(
        &kernel,
        &mut state,
        &stranding,
        ApplyError::StrandedHolder(received),
    );

    // IdentityReused: after `e4` is deleted for real, the view forgets it was
    // ever used, and a production re-adds an edge under that identity.
    let drop_e4 = RewriteRequest::new(
        "drop_e4",
        RewriteMatch::new(
            ids(&[("a", "a"), ("b", "b")]),
            ids(&[("e4", "e4")]),
            ids(&[]),
            ids(&[]),
        ),
    );
    let prepared = kernel
        .prepare_rewrite_with_evidence(&state, &grammar, &drop_e4, payload())
        .unwrap();
    let kernel = kernel.commit_rewrite(&mut state, prepared).unwrap();
    assert!(state.used_edge_ids().contains("e4"));
    let lie = Forgery {
        used_edge_ids: Some(
            state
                .used_edge_ids()
                .iter()
                .filter(|id| &***id != "e4")
                .cloned()
                .collect(),
        ),
        ..Forgery::default()
    };
    let readd = RewriteRequest::new(
        "readd",
        RewriteMatch::new(
            ids(&[("a", "a"), ("b", "b")]),
            ids(&[]),
            ids(&[]),
            ids(&[("x", "e4")]),
        ),
    );
    let (reused, _) = kernel
        .evaluate_rewrite(&forged(&state, lie), &grammar, &readd, payload())
        .unwrap();
    rejects(
        &kernel,
        &mut state,
        &reused,
        ApplyError::IdentityReused(Arc::from("e4")),
    );
    // The faithful view refuses the same request at evaluation.
    assert!(matches!(
        kernel.evaluate_rewrite(&state, &grammar, &readd, payload()),
        Err(RewriteError::InvalidMatch(_))
    ));
}

/// Adds one edge with its definition to a fragment.
fn with_edge(
    fragment: RewriteFragment,
    edge: &str,
    source: &str,
    target: &str,
    contract: &str,
) -> RewriteFragment {
    let data = ontography::storage::FragmentData::from(&fragment);
    let mut fragment = RewriteFragment::try_from(data).unwrap();
    fragment = RewriteFragment::new(
        fragment_nodes(&fragment),
        fragment_edges(&fragment)
            .into_iter()
            .chain([Edge::new(edge, source, target).unwrap()])
            .collect(),
        fragment_node_definitions(&fragment),
        fragment_edge_definitions(&fragment)
            .into_iter()
            .chain([EdgeDefinition::new(
                edge,
                ["Flow"],
                ["Node"],
                ["Node"],
                contract,
                [tag("route")],
            )
            .unwrap()])
            .collect(),
        Vec::new(),
        fragment_roots(&fragment),
    );
    fragment
}

fn admitted(fragment: &RewriteFragment) -> Kernel {
    kernel().admit_fragment(fragment).unwrap()
}
fn fragment_nodes(fragment: &RewriteFragment) -> Vec<Node> {
    admitted(fragment).graph().nodes().to_vec()
}
fn fragment_edges(fragment: &RewriteFragment) -> Vec<Edge> {
    admitted(fragment).graph().edges().to_vec()
}
fn fragment_node_definitions(fragment: &RewriteFragment) -> Vec<NodeDefinition> {
    admitted(fragment).node_definitions().to_vec()
}
fn fragment_edge_definitions(fragment: &RewriteFragment) -> Vec<EdgeDefinition> {
    admitted(fragment).edge_definitions().to_vec()
}
fn fragment_roots(fragment: &RewriteFragment) -> Vec<RootRule> {
    admitted(fragment).roots().to_vec()
}
