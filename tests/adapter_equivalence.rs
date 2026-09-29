//! T3, adapter equivalence: random operation sequences drive an in-memory
//! `State` and a runtime session in lockstep. After every step the session's
//! snapshot equals the in-memory state, every rejection matches variant for
//! variant, and the session's readiness projection equals the one computed
//! from the in-memory frontier: the head of every (receiver, edge) group, the
//! `Any` trigger at every `Any` receiver, and the `All` trigger at `c`. The
//! two implementations share one set of evaluators, one transition vocabulary,
//! and one `verify`; this test pins that the `SQLite` applier and the
//! in-memory applier agree on every reachable state, including states reached
//! through stale plans, node creation and deletion with fresh identities,
//! outgoing edges swapped for rejecting ones so outbound work retires as
//! `NoAcceptingEdge`, route removal at the `All` receiver, composite edits
//! that combine several changes in one transition, and refused edits and
//! extensions. Refused edits cover every structural rejection, an admission
//! failure, and a policy denial. The snapshot itself runs the adapter's own
//! projection check, so a drifted index fails the step. A required prefix
//! constructs the rare retirement, stale-plan, and refusal cases before random
//! exploration, so coverage is independent of generated ids.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract,
    DefinitionId, Edge, EdgeDefinition, EditContext, EditPolicy, Emission, ExtensionError, Graph,
    GraphEdit, GraphFragment, IngressMode, Kernel, Node, NodeDefinition, OutputAuthority,
    PackageId, PackageRecord, Payload, PendingFrontier, Phase, PolicyDenial, Principal,
    ProposalDecision, ProposalRuntime, Retirement, RetirementReason, RewriteError, RewriteRequest,
    RootRule, Schema, SessionHandle, State,
};

/// Deterministic choice stream. Runtime-generated ids still affect the order
/// of candidate packages, so a seed alone does not reproduce an entire history.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % bound as u64).unwrap()
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
        (!items.is_empty()).then(|| &items[self.below(items.len())])
    }
}

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

fn edge_definition(edge: &str) -> EdgeDefinition {
    EdgeDefinition::new(edge, ["Flow"], ["Node"], ["Node"], "item", [tag("route")]).unwrap()
}

/// An edge whose contract refuses every payload.
fn rejecting_edge_definition(edge: &str) -> EdgeDefinition {
    EdgeDefinition::new(edge, ["Flow"], ["Node"], ["Node"], "reject", [tag("route")]).unwrap()
}

fn all_receiver(node: &str) -> NodeDefinition {
    NodeDefinition::new(node, ["Node"], "result")
        .unwrap()
        .with_ingress_mode(IngressMode::All)
}

/// Graph: `a` (root) → `b` (Any) on the current `ab*` edge; `a` → `c` on the
/// current `ac*` edge; `b` → `c` on the current `bc*` edge, when present; `c`
/// is an `All` receiver over its incoming edges. An edit may drop or re-add
/// the `b → c` edge, add a node `d*` (Any) fed by `c` on `cd*` and delete it
/// again, or swap `a`'s two outgoing edges for ones carrying the `reject`
/// contract and back, in any combination. Every edge carries the `route` tag.
fn initial_kernel(result: &Contract, item: &Contract, reject: &Contract) -> Kernel {
    Kernel::admit(
        DefinitionId::new("equivalence").unwrap(),
        Schema::new(["Node"], ["Result", "Item"], [tag("route")]).unwrap(),
        Graph::new(
            ["a", "b", "c"].map(|node| Node::new(node).unwrap()),
            [
                Edge::new("ab", "a", "b").unwrap(),
                Edge::new("ac", "a", "c").unwrap(),
                Edge::new("bc0", "b", "c").unwrap(),
            ],
        )
        .unwrap(),
        [result.clone(), item.clone(), reject.clone()],
        [
            NodeDefinition::new("a", ["Node"], "result").unwrap(),
            NodeDefinition::new("b", ["Node"], "result").unwrap(),
            all_receiver("c"),
        ],
        [
            edge_definition("ab"),
            edge_definition("ac"),
            edge_definition("bc0"),
        ],
        [],
        [RootRule::new("a", Authority::new([tag("route")])).unwrap()],
    )
    .unwrap()
}

/// The current definition with the `extra` tag added and nothing else changed.
fn extended_kernel(current: &Kernel) -> Kernel {
    Kernel::admit(
        current.id().clone(),
        Schema::new(["Node"], ["Result", "Item"], [tag("route"), tag("extra")]).unwrap(),
        current.graph().clone(),
        current.contracts().iter().cloned(),
        current.node_definitions().iter().cloned(),
        current.edge_definitions().iter().cloned(),
        current.authority_transitions().iter().cloned(),
        current.roots().iter().cloned(),
    )
    .unwrap()
}

/// The principal of every edit the suite expects to be admitted.
const TESTER: &str = "tester";

/// Admits every edit except those the principal `denied` asks for, so both
/// sides exercise a policy denial.
struct RefuseDenied;

impl EditPolicy for RefuseDenied {
    fn permits(&self, context: &EditContext<'_>) -> Result<(), PolicyDenial> {
        if context.principal.name() == "denied" {
            Err(PolicyDenial::new("the principal `denied` may not edit"))
        } else {
            Ok(())
        }
    }
}

/// Accumulates one graph edit.
#[derive(Default)]
struct EditBuilder {
    remove_nodes: BTreeSet<Arc<str>>,
    remove_edges: BTreeSet<Arc<str>>,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    node_definitions: Vec<NodeDefinition>,
    edge_definitions: Vec<EdgeDefinition>,
    roots: Vec<RootRule>,
}

impl EditBuilder {
    fn remove_node(mut self, node: &str) -> Self {
        self.remove_nodes.insert(Arc::from(node));
        self
    }

    fn remove_edge(mut self, edge: &str) -> Self {
        self.remove_edges.insert(Arc::from(edge));
        self
    }

    /// Adds an `Any` receiver.
    fn add_node(mut self, node: &str) -> Self {
        self.nodes.push(Node::new(node).unwrap());
        self.node_definitions
            .push(NodeDefinition::new(node, ["Node"], "result").unwrap());
        self
    }

    /// Adds the edge `definition` annotates, from `source` to `target`.
    fn add_edge(mut self, definition: EdgeDefinition, source: &str, target: &str) -> Self {
        self.edges
            .push(Edge::new(definition.edge_id(), source, target).unwrap());
        self.edge_definitions.push(definition);
        self
    }

    fn add_root(mut self, node: &str) -> Self {
        self.roots
            .push(RootRule::new(node, Authority::new([tag("route")])).unwrap());
        self
    }

    fn request(self, principal: &str) -> RewriteRequest {
        RewriteRequest::new(
            Principal::new(principal),
            GraphEdit::new(
                self.remove_nodes,
                self.remove_edges,
                GraphFragment::new(
                    self.nodes,
                    self.edges,
                    self.node_definitions,
                    self.edge_definitions,
                    Vec::new(),
                    self.roots,
                ),
            ),
        )
    }
}

fn payload(rng: &mut Rng) -> Payload {
    Arc::from(format!("item-{}", rng.below(4)).into_bytes())
}

/// The mirror keeps the in-memory state, the kernel it is bound to, the
/// payload evidence, the accepted activation ids, and the identities of the
/// dynamic parts of the graph.
struct Mirror {
    kernel: Arc<Kernel>,
    state: State,
    evidence: BTreeMap<ContentDigest, Payload>,
    activations: Vec<ActivationId>,
    /// The current `a → b` and `a → c` edges.
    ab_edge: String,
    ac_edge: String,
    bc_edge: Option<String>,
    /// The current `d` node and its feeding edge, when spawned.
    cd: Option<(String, String)>,
    fresh: usize,
    /// Which rarer shapes this seed exercised.
    saw: BTreeSet<Scenario>,
}

/// The rarer shapes every seed must reach; the required prefix builds each.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Scenario {
    StalePlan,
    HolderRemoved,
    NoAcceptingEdge,
    RouteRemoved,
}

impl Scenario {
    const ALL: [Self; 4] = [
        Self::StalePlan,
        Self::HolderRemoved,
        Self::NoAcceptingEdge,
        Self::RouteRemoved,
    ];

    /// The scenario a rewrite's retirement exhibits.
    fn retired(reason: RetirementReason) -> Option<Self> {
        match reason {
            RetirementReason::HolderRemoved => Some(Self::HolderRemoved),
            RetirementReason::NoAcceptingEdge => Some(Self::NoAcceptingEdge),
            RetirementReason::RouteRemoved => Some(Self::RouteRemoved),
            RetirementReason::Explicit => None,
        }
    }
}

impl Mirror {
    fn refresh_topology(&mut self) {
        let graph = self.kernel.graph();
        let from_a = |target: &str| {
            graph
                .edges()
                .iter()
                .find(|edge| edge.source() == "a" && edge.target() == target)
                .map(|edge| edge.id().to_owned())
                .expect("a keeps one edge to each of b and c")
        };
        self.ab_edge = from_a("b");
        self.ac_edge = from_a("c");
        self.bc_edge = graph
            .edges()
            .iter()
            .find(|edge| edge.source() == "b")
            .map(|edge| edge.id().to_owned());
        self.cd = graph
            .edges()
            .iter()
            .find(|edge| edge.source() == "c")
            .map(|edge| (edge.target().to_owned(), edge.id().to_owned()));
    }

    fn remember(&mut self, bytes: &Payload) {
        self.evidence
            .insert(ContentDigest::compute(bytes), bytes.clone());
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }
}

fn ids(frontier: &PendingFrontier) -> Vec<PackageId> {
    frontier.packages().iter().map(|(id, _)| *id).collect()
}

/// The least live package delivered on `edge` to `node`, from the mirror.
fn expected_edge_head(mirror: &Mirror, node: &str, edge: &str) -> Option<PackageId> {
    mirror
        .state
        .live()
        .filter(|(_, record)| {
            record.holder() == node
                && record
                    .delivery()
                    .is_some_and(|delivery| delivery.edge_id() == edge)
        })
        .map(|(id, _)| id)
        .min()
}

/// The next trigger at an `All` receiver, computed from the in-memory frontier:
/// for every authority whose live delivered packages cover every current
/// incoming edge, the least package on each edge forms a bundle; the bundle
/// whose least package is least wins. Bundles are disjoint, so that least
/// package alone orders them.
fn expected_all_trigger(mirror: &Mirror, node: &str) -> Vec<PackageId> {
    let incoming: BTreeSet<&str> = mirror
        .kernel
        .graph()
        .edges()
        .iter()
        .filter(|edge| edge.target() == node)
        .map(Edge::id)
        .collect();
    if incoming.is_empty() {
        return Vec::new();
    }
    let mut heads: BTreeMap<Authority, BTreeMap<&str, PackageId>> = BTreeMap::new();
    for (id, record) in mirror.state.live() {
        let Some(delivery) = record.delivery() else {
            continue;
        };
        if record.holder() != node || !incoming.contains(delivery.edge_id()) {
            continue;
        }
        let head = heads
            .entry(record.authority().clone())
            .or_default()
            .entry(delivery.edge_id())
            .or_insert(id);
        if id < *head {
            *head = id;
        }
    }
    heads
        .values()
        .filter(|edges| edges.len() == incoming.len())
        .map(|edges| edges.values().copied().collect::<Vec<_>>())
        .min_by_key(|bundle| bundle.iter().copied().min())
        .map(|mut bundle| {
            bundle.sort_unstable();
            bundle
        })
        .unwrap_or_default()
}

async fn check(session: &SessionHandle, mirror: &Mirror, step: usize, seed: u64) {
    let context = format!("seed {seed} step {step}");
    let snapshot = session.snapshot().await;
    assert_eq!(
        snapshot.state(),
        &mirror.state,
        "{context}: snapshot diverged from the in-memory state"
    );
    assert_eq!(snapshot.revision(), mirror.state.revision());
    assert_eq!(snapshot.kernel().fingerprint(), mirror.kernel.fingerprint());

    let graph = mirror.kernel.graph();
    let mut pending_total = session
        .outbound_page(None, None, usize::MAX)
        .await
        .unwrap()
        .packages()
        .len();
    for node in graph.nodes() {
        let pending = session.pending_at(node.id()).await.unwrap();
        pending_total += pending.packages().len();
        // `Any` receivers trigger on their least pending package.
        let mode = mirror
            .kernel
            .node_definition(node.id())
            .unwrap()
            .ingress_mode();
        if mode == IngressMode::Any {
            assert_eq!(
                ids(&session.next_trigger_at(node.id()).await.unwrap()),
                ids(&pending).into_iter().take(1).collect::<Vec<_>>(),
                "{context}: `Any` trigger at {} diverged",
                node.id()
            );
        }
    }
    assert_eq!(snapshot.state().live().count(), pending_total, "{context}");
    // Every (receiver, edge) head, and the `All` bundle at `c`.
    for edge in graph.edges() {
        let head = session
            .next_pending_on_edge_at(edge.target(), edge.id())
            .await
            .unwrap();
        assert_eq!(
            ids(&head).first().copied(),
            expected_edge_head(mirror, edge.target(), edge.id()),
            "{context}: head of edge {} diverged",
            edge.id()
        );
    }
    assert_eq!(
        ids(&session.next_trigger_at("c").await.unwrap()),
        expected_all_trigger(mirror, "c"),
        "{context}: `All` trigger at c diverged"
    );
}

/// Drops the current `b → c` edge, or adds a fresh one.
fn toggle_bc(edit: EditBuilder, mirror: &mut Mirror) -> EditBuilder {
    if let Some(current) = mirror.bc_edge.clone() {
        edit.remove_edge(&current)
    } else {
        let fresh = mirror.fresh_name("bc");
        edit.add_edge(edge_definition(&fresh), "b", "c")
    }
}

/// Reaps the current `d` with its feeding edge, retiring whatever it holds as
/// `HolderRemoved`, or spawns a fresh `d` fed by `c`.
fn toggle_cd(edit: EditBuilder, mirror: &mut Mirror) -> EditBuilder {
    if let Some((node, edge)) = mirror.cd.clone() {
        edit.remove_node(&node).remove_edge(&edge)
    } else {
        let node = mirror.fresh_name("d");
        let edge = mirror.fresh_name("cd");
        edit.add_node(&node)
            .add_edge(edge_definition(&edge), "c", &node)
    }
}

/// Swaps `a`'s outgoing edges for rejecting ones, or back, under fresh names.
fn swap_a(edit: EditBuilder, mirror: &mut Mirror) -> EditBuilder {
    let rejecting = mirror
        .kernel
        .edge_definition(&mirror.ab_edge)
        .unwrap()
        .package_contract()
        == "reject";
    let definition = if rejecting {
        edge_definition
    } else {
        rejecting_edge_definition
    };
    let (ab, ac) = (mirror.fresh_name("ab"), mirror.fresh_name("ac"));
    [mirror.ab_edge.clone(), mirror.ac_edge.clone()]
        .iter()
        .fold(edit, |edit, current| edit.remove_edge(current))
        .add_edge(definition(&ab), "a", "b")
        .add_edge(definition(&ac), "a", "c")
}

/// A random combination of the three changes, possibly none, as one edit.
fn composite_request(rng: &mut Rng, mirror: &mut Mirror) -> RewriteRequest {
    let mut edit = EditBuilder::default();
    if rng.below(2) == 0 {
        edit = toggle_bc(edit, mirror);
    }
    if rng.below(2) == 0 {
        edit = toggle_cd(edit, mirror);
    }
    if rng.below(2) == 0 {
        edit = swap_a(edit, mirror);
    }
    edit.request(TESTER)
}

/// An edit the kernel must refuse, with a test of the refusal it must give.
type Refusal = (RewriteRequest, fn(&RewriteError) -> bool);

/// Edits the kernel must refuse: every structural rejection, an admission
/// failure, and a policy denial.
fn refused_requests(mirror: &mut Mirror) -> Vec<Refusal> {
    let invalid: fn(&RewriteError) -> bool = |error| matches!(error, RewriteError::InvalidEdit(_));
    let unadmitted: fn(&RewriteError) -> bool =
        |error| matches!(error, RewriteError::Definition(_));
    let denied: fn(&RewriteError) -> bool = |error| matches!(error, RewriteError::Denied(_));
    let stray = mirror.fresh_name("stray");
    vec![
        // The edge to remove is absent.
        (
            EditBuilder::default()
                .remove_edge("no-such-edge")
                .request(TESTER),
            invalid,
        ),
        // `c` always keeps `a → c`, which would dangle.
        (
            EditBuilder::default().remove_node("c").request(TESTER),
            invalid,
        ),
        // `bc0` was used by the initial graph, whether or not it survives.
        (
            EditBuilder::default()
                .add_edge(edge_definition("bc0"), "b", "c")
                .request(TESTER),
            invalid,
        ),
        // A surviving node keeps its definition, root rule included.
        (
            EditBuilder::default().add_root("b").request(TESTER),
            invalid,
        ),
        // A fresh edge to a node that does not exist fails admission.
        (
            EditBuilder::default()
                .add_edge(edge_definition(&stray), "b", "ghost")
                .request(TESTER),
            unadmitted,
        ),
        // A structurally sound edit the policy refuses.
        (
            toggle_bc(EditBuilder::default(), mirror).request("denied"),
            denied,
        ),
    ]
}

/// Runs one rewrite on both sides and compares the outcome variant for
/// variant, returning the shared refusal when both refuse.
async fn rewrite_both(
    session: &SessionHandle,
    mirror: &mut Mirror,
    request: &RewriteRequest,
) -> Result<(), RewriteError> {
    let plan = session.prepare_rewrite(request).await.unwrap();
    let prepared =
        mirror
            .kernel
            .prepare_rewrite(&mirror.state, &RefuseDenied, request, &mirror.evidence);
    match (plan, prepared) {
        (Ok(plan), Ok(prepared)) => {
            let retirements = prepared.retirements().clone();
            assert_eq!(plan.retirements(), &retirements);
            let outcome = session.commit_rewrite(plan).await.unwrap().unwrap();
            mirror.kernel = mirror
                .kernel
                .commit_rewrite(&mut mirror.state, prepared)
                .unwrap();
            mirror.refresh_topology();
            assert_eq!(outcome.revision(), mirror.state.revision());
            assert_eq!(outcome.retirements(), &retirements);
            mirror
                .saw
                .extend(retirements.values().copied().filter_map(Scenario::retired));
            Ok(())
        }
        (Err(session_error), Err(mirror_error)) => {
            assert_eq!(session_error, mirror_error);
            Err(mirror_error)
        }
        (plan, prepared) => panic!("rewrite decisions diverged: {plan:?} versus {prepared:?}"),
    }
}

async fn step(rng: &mut Rng, session: &SessionHandle, mirror: &mut Mirror) {
    let live: Vec<(PackageId, PackageRecord)> = mirror
        .state
        .live()
        .map(|(id, record)| (id, record.clone()))
        .collect();
    let all: Vec<PackageId> = mirror.state.packages().keys().copied().collect();
    match rng.below(15) {
        // A root at `a` with zero to two emissions, sometimes on an edge.
        0..=2 => {
            let mut proposal = ActivationProposal::root(
                "a",
                Authority::new([tag("route")]),
                Arc::from(b"result".as_slice()),
            );
            let (ab, ac) = (mirror.ab_edge.clone(), mirror.ac_edge.clone());
            for _ in 0..rng.below(3) {
                let bytes = payload(rng);
                mirror.remember(&bytes);
                proposal.emit(match rng.below(3) {
                    0 => Emission::outbound("Item", OutputAuthority::Carry, bytes),
                    1 => Emission::new(ab.as_str(), OutputAuthority::Carry, bytes),
                    _ => Emission::new(ac.as_str(), OutputAuthority::Carry, bytes),
                });
            }
            submit(session, mirror, proposal).await;
        }
        // Consume a package, sometimes an illegal one; at `c` build the join
        // and sometimes feed `d`; at `b` sometimes feed `c`.
        3..=4 => {
            let Some(target) = rng.pick(&all).copied() else {
                return;
            };
            let holder = mirror.state.package(target).unwrap().holder().to_owned();
            let inputs: Vec<PackageId> = if holder == "c" && rng.below(4) != 0 {
                let mut by_edge = BTreeMap::new();
                for (id, record) in &live {
                    if record.holder() == "c" {
                        by_edge
                            .entry(record.delivery().unwrap().edge_id().to_owned())
                            .or_insert(*id);
                    }
                }
                by_edge.values().copied().collect()
            } else {
                vec![target]
            };
            let mut proposal = ActivationProposal::join(inputs, Arc::from(b"result".as_slice()));
            let feed = match holder.as_str() {
                "b" => mirror.bc_edge.clone(),
                "c" => mirror.cd.as_ref().map(|(_, edge)| edge.clone()),
                _ => None,
            };
            if let Some(edge) = feed
                && rng.below(2) == 0
            {
                let bytes = payload(rng);
                mirror.remember(&bytes);
                proposal.emit(Emission::new(edge.as_str(), OutputAuthority::Carry, bytes));
            }
            submit(session, mirror, proposal).await;
        }
        // Transfer a package along a random edge, legal or not.
        5..=6 => {
            let Some(target) = rng.pick(&all).copied() else {
                return;
            };
            let edges = [
                mirror.ab_edge.clone(),
                mirror.ac_edge.clone(),
                mirror.bc_edge.clone().unwrap_or_else(|| "none".to_owned()),
                mirror
                    .cd
                    .as_ref()
                    .map_or_else(|| "none".to_owned(), |(_, edge)| edge.clone()),
            ];
            let edge = edges[rng.below(edges.len())].clone();
            let record = mirror.state.package(target).unwrap().clone();
            let bytes = mirror
                .evidence
                .get(&record.content_digest())
                .cloned()
                .unwrap_or_else(|| Arc::from(b"absent".as_slice()));
            let session_result = session.transfer(target, &edge).await;
            let mirror_result = mirror
                .kernel
                .prepare_transfer(&mirror.state, target, &edge, &bytes)
                .and_then(|prepared| mirror.kernel.commit_transfer(&mut mirror.state, prepared));
            assert_eq!(session_result.unwrap(), mirror_result);
        }
        // Retire a package, with or without evidence, legal or not.
        7 => {
            let Some(target) = rng.pick(&all).copied() else {
                return;
            };
            let evidence = if rng.below(3) == 0 {
                Some(ActivationId::from_u128(rng.next().into()))
            } else {
                rng.pick(&mirror.activations).copied()
            };
            let session_result = session.retire(target, evidence).await;
            let mirror_result = mirror.kernel.retire(&mut mirror.state, target, evidence);
            assert_eq!(session_result.unwrap(), mirror_result);
        }
        // Edit: any combination of dropping or re-adding `b → c`, spawning or
        // reaping `d`, and swapping `a`'s edges, in one transition. The parts
        // touch disjoint elements, so every combination, the empty edit
        // included, is admissible.
        8 => {
            let request = composite_request(rng, mirror);
            rewrite_both(session, mirror, &request).await.unwrap();
        }
        // Edit: spawn a fresh node `d` fed by `c`, or reap the current one,
        // retiring whatever it holds as `HolderRemoved`.
        9 => {
            let request = toggle_cd(EditBuilder::default(), mirror).request(TESTER);
            rewrite_both(session, mirror, &request).await.unwrap();
        }
        // A plan prepared, then overtaken by an activation, is stale on both sides.
        10 => {
            let request = toggle_bc(EditBuilder::default(), mirror).request(TESTER);
            let plan = session.prepare_rewrite(&request).await.unwrap().unwrap();
            let prepared = mirror
                .kernel
                .prepare_rewrite(&mirror.state, &RefuseDenied, &request, &mirror.evidence)
                .unwrap();
            let root = ActivationProposal::root(
                "a",
                Authority::new([tag("route")]),
                Arc::from(b"result".as_slice()),
            );
            submit(session, mirror, root).await;
            assert_eq!(
                session.commit_rewrite(plan).await.unwrap().unwrap_err(),
                RewriteError::Stale
            );
            assert_eq!(
                mirror
                    .kernel
                    .commit_rewrite(&mut mirror.state, prepared)
                    .unwrap_err(),
                RewriteError::Stale
            );
            mirror.saw.insert(Scenario::StalePlan);
        }
        // Edit: swap `a`'s outgoing edges for rejecting ones, retiring every
        // outbound package at `a` as `NoAcceptingEdge`, or swap them back.
        11 => {
            let request = swap_a(EditBuilder::default(), mirror).request(TESTER);
            rewrite_both(session, mirror, &request).await.unwrap();
        }
        // Edits the kernel must refuse, compared variant for variant.
        12 => {
            let mut refused = refused_requests(mirror);
            let (request, refusal) = refused.swap_remove(rng.below(refused.len()));
            let error = rewrite_both(session, mirror, &request).await.unwrap_err();
            assert!(refusal(&error), "unexpected refusal {error:?}");
        }
        // Extend the vocabulary; a second attempt is rejected on both sides.
        _ => {
            let next = Arc::new(extended_kernel(&mirror.kernel));
            let session_result = session.extend(Arc::clone(&next)).await.unwrap();
            let mirror_result = mirror
                .kernel
                .prepare_extension(&mirror.state, Arc::clone(&next))
                .and_then(|prepared| mirror.kernel.commit_extension(&mut mirror.state, prepared));
            match (session_result, mirror_result) {
                (Ok(revision), Ok(kernel)) => {
                    mirror.kernel = kernel;
                    assert_eq!(revision, mirror.state.revision());
                }
                (Err(session_error), Err(mirror_error)) => {
                    assert_eq!(session_error, mirror_error);
                    assert_eq!(session_error, ExtensionError::Unchanged);
                }
                (session_result, mirror_result) => {
                    panic!(
                        "extension decisions diverged: {session_result:?} versus {mirror_result:?}"
                    );
                }
            }
        }
    }
}

async fn submit(session: &SessionHandle, mirror: &mut Mirror, proposal: ActivationProposal) {
    match session.submit(proposal.clone()).await.unwrap() {
        ProposalDecision::Committed(id) => {
            let transition = mirror
                .kernel
                .evaluate_activation(&mirror.state, id, proposal)
                .expect("the session accepted, so the mirror must");
            mirror.state.apply(&mirror.kernel, &transition).unwrap();
            mirror.activations.push(id);
        }
        ProposalDecision::Rejected(reject) => {
            let probe = ActivationId::from_u128(u128::MAX);
            let mirror_reject = mirror
                .kernel
                .evaluate_activation(&mirror.state, probe, proposal)
                .expect_err("the session rejected, so the mirror must");
            assert_eq!(mirror_reject, reject);
        }
    }
}

/// Establish every required coverage case by construction, and return the
/// number of checked steps it took. In particular, reaching `d` requires a
/// complete join at `c`; random choices of UUID-ordered packages cannot
/// guarantee that path before a later reap.
async fn required_prefix(session: &SessionHandle, mirror: &mut Mirror, seed: u64) -> usize {
    let spawn = toggle_cd(EditBuilder::default(), mirror).request(TESTER);
    rewrite_both(session, mirror, &spawn).await.unwrap();
    check(session, mirror, 0, seed).await;

    let request = toggle_bc(EditBuilder::default(), mirror).request(TESTER);
    let session_plan = session.prepare_rewrite(&request).await.unwrap().unwrap();
    let mirror_plan = mirror
        .kernel
        .prepare_rewrite(&mirror.state, &RefuseDenied, &request, &mirror.evidence)
        .unwrap();

    let bytes: Payload = Arc::from(b"prefix-item".as_slice());
    mirror.remember(&bytes);
    let mut root = ActivationProposal::root(
        "a",
        Authority::new([tag("route")]),
        Arc::from(b"result".as_slice()),
    );
    for edge in [&mirror.ab_edge, &mirror.ac_edge] {
        root.emit(Emission::new(
            edge.as_str(),
            OutputAuthority::Carry,
            bytes.clone(),
        ));
    }
    root.emit(Emission::outbound(
        "Item",
        OutputAuthority::Carry,
        bytes.clone(),
    ));
    submit(session, mirror, root).await;
    check(session, mirror, 1, seed).await;
    assert_eq!(
        session
            .commit_rewrite(session_plan)
            .await
            .unwrap()
            .unwrap_err(),
        RewriteError::Stale
    );
    assert_eq!(
        mirror
            .kernel
            .commit_rewrite(&mut mirror.state, mirror_plan)
            .unwrap_err(),
        RewriteError::Stale
    );
    mirror.saw.insert(Scenario::StalePlan);
    check(session, mirror, 2, seed).await;

    let at_b = mirror
        .state
        .live()
        .find(|(_, record)| record.holder() == "b")
        .unwrap()
        .0;
    let mut through_b = ActivationProposal::package(at_b, Arc::from(b"result".as_slice()));
    through_b.emit(Emission::new(
        mirror.bc_edge.as_deref().unwrap(),
        OutputAuthority::Carry,
        bytes.clone(),
    ));
    submit(session, mirror, through_b).await;
    check(session, mirror, 3, seed).await;

    let inputs = expected_all_trigger(mirror, "c");
    assert_eq!(inputs.len(), 2, "prefix must prepare the complete All join");
    let (holder, edge) = mirror.cd.clone().unwrap();
    let mut through_c = ActivationProposal::join(inputs, Arc::from(b"result".as_slice()));
    through_c.emit(Emission::new(edge, OutputAuthority::Carry, bytes.clone()));
    submit(session, mirror, through_c).await;
    check(session, mirror, 4, seed).await;
    let at_d = mirror
        .state
        .live()
        .find(|(_, record)| record.holder() == holder)
        .unwrap()
        .0;
    let reap = toggle_cd(EditBuilder::default(), mirror).request(TESTER);
    rewrite_both(session, mirror, &reap).await.unwrap();
    assert_eq!(
        mirror
            .state
            .package(at_d)
            .unwrap()
            .retirement()
            .map(Retirement::reason),
        Some(RetirementReason::HolderRemoved)
    );
    check(session, mirror, 5, seed).await;

    let outbound = mirror
        .state
        .live()
        .find(|(_, record)| record.holder() == "a")
        .unwrap()
        .0;
    let poison = swap_a(EditBuilder::default(), mirror).request(TESTER);
    rewrite_both(session, mirror, &poison).await.unwrap();
    assert_eq!(
        mirror
            .state
            .package(outbound)
            .unwrap()
            .retirement()
            .map(Retirement::reason),
        Some(RetirementReason::NoAcceptingEdge)
    );
    check(session, mirror, 6, seed).await;
    let cure = swap_a(EditBuilder::default(), mirror).request(TESTER);
    rewrite_both(session, mirror, &cure).await.unwrap();
    check(session, mirror, 7, seed).await;

    // A receipt at the `All` receiver `c` on `b → c`, with no partner on
    // `a → c`, retires as `RouteRemoved` when `b → c` is dropped.
    let mut root = ActivationProposal::root(
        "a",
        Authority::new([tag("route")]),
        Arc::from(b"result".as_slice()),
    );
    root.emit(Emission::new(
        mirror.ab_edge.as_str(),
        OutputAuthority::Carry,
        bytes.clone(),
    ));
    submit(session, mirror, root).await;
    check(session, mirror, 8, seed).await;
    let at_b = mirror
        .state
        .live()
        .find(|(_, record)| record.holder() == "b")
        .unwrap()
        .0;
    let mut through_b = ActivationProposal::package(at_b, Arc::from(b"result".as_slice()));
    through_b.emit(Emission::new(
        mirror.bc_edge.as_deref().unwrap(),
        OutputAuthority::Carry,
        bytes,
    ));
    submit(session, mirror, through_b).await;
    check(session, mirror, 9, seed).await;
    let at_c = mirror
        .state
        .live()
        .find(|(_, record)| record.holder() == "c")
        .unwrap()
        .0;
    let drop_bc = toggle_bc(EditBuilder::default(), mirror).request(TESTER);
    rewrite_both(session, mirror, &drop_bc).await.unwrap();
    assert_eq!(
        mirror
            .state
            .package(at_c)
            .unwrap()
            .retirement()
            .map(Retirement::reason),
        Some(RetirementReason::RouteRemoved)
    );
    check(session, mirror, 10, seed).await;

    // Every refusal, each leaving both sides unchanged.
    let mut index = 11;
    for (request, refusal) in refused_requests(mirror) {
        let error = rewrite_both(session, mirror, &request).await.unwrap_err();
        assert!(refusal(&error), "seed {seed}: unexpected refusal {error:?}");
        check(session, mirror, index, seed).await;
        index += 1;
    }
    index
}

#[tokio::test]
async fn sqlite_adapter_and_in_memory_state_agree_on_random_histories() {
    let mut saw = BTreeSet::new();
    for seed in 1..=12_u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
        let result = Contract::new("result", "Result", |_| Ok(())).unwrap();
        let item = Contract::new("item", "Item", |bytes| {
            if bytes == b"absent" {
                Err(ontography::ContractViolation::new("absent bytes"))
            } else {
                Ok(())
            }
        })
        .unwrap();
        let reject = Contract::new("reject", "Item", |_| {
            Err(ontography::ContractViolation::new("rejecting edge"))
        })
        .unwrap();
        let kernel = Arc::new(initial_kernel(&result, &item, &reject));
        let runtime = ProposalRuntime::with_policy(Arc::clone(&kernel), Arc::new(RefuseDenied));
        let session = runtime.open().unwrap();
        let mut mirror = Mirror {
            state: kernel.empty_state(),
            kernel,
            evidence: BTreeMap::new(),
            activations: Vec::new(),
            ab_edge: "ab".to_owned(),
            ac_edge: "ac".to_owned(),
            bc_edge: Some("bc0".to_owned()),
            cd: None,
            fresh: 0,
            saw: BTreeSet::new(),
        };
        let prefix = required_prefix(&session, &mut mirror, seed).await;
        for step_index in 0..120 {
            step(&mut rng, &session, &mut mirror).await;
            check(&session, &mirror, prefix + step_index, seed).await;
        }
        let final_state = session.snapshot().await;
        assert!(final_state.state().packages().values().all(
            |record| record.holder() != "" && matches!(record.phase(), Phase::In | Phase::Out)
        ));
        saw.extend(mirror.saw);
    }
    for scenario in Scenario::ALL {
        assert!(saw.contains(&scenario), "no seed exercised {scenario:?}");
    }
}
