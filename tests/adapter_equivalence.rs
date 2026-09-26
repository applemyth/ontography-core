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
//! `NoAcceptingEdge`, and rejected rewrites and extensions. The snapshot
//! itself runs the adapter's own projection check, so a drifted index fails
//! the step.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract,
    DefinitionId, Edge, EdgeDefinition, Emission, ExtensionError, Graph, IngressMode, Kernel, Node,
    NodeDefinition, OutputAuthority, PackageId, PackageRecord, Payload, PendingFrontier, Phase,
    ProposalDecision, ProposalRuntime, Retirement, RetirementReason, RewriteError, RewriteFragment,
    RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest, RootRule, Schema,
    SessionHandle, State,
};

/// Deterministic xorshift generator so every seed replays exactly.
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
/// current `ac*` edge; `b` → `c` on the current `bc*` edge; `c` is an `All`
/// receiver over its two incoming edges. A rewrite may add a node `d*` (Any)
/// fed by `c` on `cd*` and delete it again, or swap `a`'s two outgoing edges
/// for ones carrying the `reject` contract and back. Every edge carries the
/// `route` tag.
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

/// The `b`,`c` sub-definition with or without a `b → c` edge named `symbol`.
fn bc_fragment(symbol: Option<&str>) -> RewriteFragment {
    RewriteFragment::new(
        vec![Node::new("b").unwrap(), Node::new("c").unwrap()],
        symbol
            .map(|edge| Edge::new(edge, "b", "c").unwrap())
            .into_iter()
            .collect(),
        vec![
            NodeDefinition::new("b", ["Node"], "result").unwrap(),
            all_receiver("c"),
        ],
        symbol.map(edge_definition).into_iter().collect(),
        Vec::new(),
        Vec::new(),
    )
}

/// The `c` sub-definition alone, or with an `Any` node `d` fed on `cd`.
fn cd_fragment(with_d: bool) -> RewriteFragment {
    let mut nodes = vec![Node::new("c").unwrap()];
    let mut definitions = vec![all_receiver("c")];
    let mut edges = Vec::new();
    let mut edge_definitions = Vec::new();
    if with_d {
        nodes.push(Node::new("d").unwrap());
        definitions.push(NodeDefinition::new("d", ["Node"], "result").unwrap());
        edges.push(Edge::new("cd", "c", "d").unwrap());
        edge_definitions.push(edge_definition("cd"));
    }
    RewriteFragment::new(
        nodes,
        edges,
        definitions,
        edge_definitions,
        Vec::new(),
        Vec::new(),
    )
}

/// The `a`,`b`,`c` sub-definition with `a`'s two outgoing edges `x` and `y`,
/// accepting or rejecting.
fn a_fragment(rejecting: bool) -> RewriteFragment {
    let definition = if rejecting {
        rejecting_edge_definition
    } else {
        edge_definition
    };
    RewriteFragment::new(
        vec![
            Node::new("a").unwrap(),
            Node::new("b").unwrap(),
            Node::new("c").unwrap(),
        ],
        vec![
            Edge::new("x", "a", "b").unwrap(),
            Edge::new("y", "a", "c").unwrap(),
        ],
        vec![
            NodeDefinition::new("a", ["Node"], "result").unwrap(),
            NodeDefinition::new("b", ["Node"], "result").unwrap(),
            all_receiver("c"),
        ],
        vec![definition("x"), definition("y")],
        Vec::new(),
        vec![RootRule::new("a", Authority::new([tag("route")])).unwrap()],
    )
}

fn grammar() -> RewriteGrammar {
    let abc: BTreeSet<Arc<str>> = [Arc::from("a"), Arc::from("b"), Arc::from("c")].into();
    let bc: BTreeSet<Arc<str>> = [Arc::from("b"), Arc::from("c")].into();
    let c: BTreeSet<Arc<str>> = [Arc::from("c")].into();
    let production = |id: &str, left, interface: &BTreeSet<Arc<str>>, right| {
        RewriteProduction::new(id, left, interface.clone(), BTreeSet::new(), right).unwrap()
    };
    RewriteGrammar::new([
        production("drop", bc_fragment(Some("x")), &bc, bc_fragment(None)),
        production("add", bc_fragment(None), &bc, bc_fragment(Some("x"))),
        production("spawn", cd_fragment(false), &c, cd_fragment(true)),
        production("reap", cd_fragment(true), &c, cd_fragment(false)),
        production("poison", a_fragment(false), &abc, a_fragment(true)),
        production("cure", a_fragment(true), &abc, a_fragment(false)),
    ])
    .unwrap()
}

fn same(pairs: &[(&str, &str)]) -> BTreeMap<Arc<str>, Arc<str>> {
    pairs
        .iter()
        .map(|(symbol, actual)| (Arc::from(*symbol), Arc::from(*actual)))
        .collect()
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
    saw_stale: bool,
    saw_reap: bool,
    saw_no_accepting_edge: bool,
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

fn bc_request(mirror: &mut Mirror) -> RewriteRequest {
    if let Some(current) = &mirror.bc_edge {
        RewriteRequest::new(
            "drop",
            RewriteMatch::new(
                same(&[("b", "b"), ("c", "c")]),
                same(&[("x", current)]),
                BTreeMap::new(),
                BTreeMap::new(),
            ),
        )
    } else {
        let fresh = mirror.fresh_name("bc");
        RewriteRequest::new(
            "add",
            RewriteMatch::new(
                same(&[("b", "b"), ("c", "c")]),
                BTreeMap::new(),
                BTreeMap::new(),
                same(&[("x", &fresh)]),
            ),
        )
    }
}

/// Swaps `a`'s outgoing edges for rejecting ones, or back, under fresh names.
fn a_request(mirror: &mut Mirror) -> RewriteRequest {
    let rejecting = mirror
        .kernel
        .edge_definition(&mirror.ab_edge)
        .unwrap()
        .package_contract()
        == "reject";
    let (ab, ac) = (mirror.fresh_name("ab"), mirror.fresh_name("ac"));
    RewriteRequest::new(
        if rejecting { "cure" } else { "poison" },
        RewriteMatch::new(
            same(&[("a", "a"), ("b", "b"), ("c", "c")]),
            same(&[("x", &mirror.ab_edge), ("y", &mirror.ac_edge)]),
            BTreeMap::new(),
            same(&[("x", &ab), ("y", &ac)]),
        ),
    )
}

fn cd_request(mirror: &mut Mirror) -> RewriteRequest {
    if let Some((node, edge)) = &mirror.cd {
        RewriteRequest::new(
            "reap",
            RewriteMatch::new(
                same(&[("c", "c"), ("d", node)]),
                same(&[("cd", edge)]),
                BTreeMap::new(),
                BTreeMap::new(),
            ),
        )
    } else {
        let node = mirror.fresh_name("d");
        let edge = mirror.fresh_name("cd");
        RewriteRequest::new(
            "spawn",
            RewriteMatch::new(
                same(&[("c", "c")]),
                BTreeMap::new(),
                same(&[("d", &node)]),
                same(&[("cd", &edge)]),
            ),
        )
    }
}

/// Runs one rewrite on both sides and compares the outcome variant for variant.
async fn rewrite_both(
    session: &SessionHandle,
    mirror: &mut Mirror,
    grammar: &RewriteGrammar,
    request: &RewriteRequest,
) {
    let plan = session.prepare_rewrite(request).await.unwrap();
    let prepared = mirror
        .kernel
        .prepare_rewrite(&mirror.state, grammar, request, &mirror.evidence);
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
        }
        (Err(session_error), Err(mirror_error)) => assert_eq!(session_error, mirror_error),
        (plan, prepared) => panic!("rewrite decisions diverged: {plan:?} versus {prepared:?}"),
    }
}

async fn step(
    rng: &mut Rng,
    session: &SessionHandle,
    mirror: &mut Mirror,
    grammar: &RewriteGrammar,
) {
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
        // Rewrite: drop the current `b → c` edge or add a fresh one.
        8 => {
            let request = bc_request(mirror);
            rewrite_both(session, mirror, grammar, &request).await;
        }
        // Rewrite: spawn a fresh node `d` fed by `c`, or reap the current one,
        // retiring whatever it holds as `HolderRemoved`.
        9 => {
            let reaping = mirror.cd.is_some();
            let request = cd_request(mirror);
            rewrite_both(session, mirror, grammar, &request).await;
            mirror.saw_reap |= reaping;
        }
        // A plan prepared, then overtaken by an activation, is stale on both sides.
        10 => {
            let request = bc_request(mirror);
            let plan = session.prepare_rewrite(&request).await.unwrap().unwrap();
            let prepared = mirror
                .kernel
                .prepare_rewrite(&mirror.state, grammar, &request, &mirror.evidence)
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
            mirror.saw_stale = true;
        }
        // Rewrite: swap `a`'s outgoing edges for rejecting ones, retiring every
        // outbound package at `a` as `NoAcceptingEdge`, or swap them back.
        11 => {
            let request = a_request(mirror);
            rewrite_both(session, mirror, grammar, &request).await;
            mirror.saw_no_accepting_edge |= mirror.state.retired().any(|(_, record)| {
                record.retirement().map(Retirement::reason)
                    == Some(RetirementReason::NoAcceptingEdge)
            });
        }
        // Rewrites the kernel must reject, compared variant for variant.
        12 => {
            let request = if rng.below(2) == 0 {
                RewriteRequest::new(
                    "drop",
                    RewriteMatch::new(
                        same(&[("b", "b"), ("c", "c")]),
                        same(&[("x", "no-such-edge")]),
                        BTreeMap::new(),
                        BTreeMap::new(),
                    ),
                )
            } else {
                RewriteRequest::new("unregistered", RewriteMatch::default())
            };
            rewrite_both(session, mirror, grammar, &request).await;
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

#[tokio::test]
async fn sqlite_adapter_and_in_memory_state_agree_on_random_histories() {
    let mut saw_stale = false;
    let mut saw_holder_removed = false;
    let mut saw_no_accepting_edge = false;
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
        let grammar = grammar();
        let runtime = ProposalRuntime::with_grammar(Arc::clone(&kernel), grammar.clone());
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
            saw_stale: false,
            saw_reap: false,
            saw_no_accepting_edge: false,
        };
        for step_index in 0..120 {
            step(&mut rng, &session, &mut mirror, &grammar).await;
            check(&session, &mirror, step_index, seed).await;
        }
        let final_state = session.snapshot().await;
        assert!(final_state.state().packages().values().all(
            |record| record.holder() != "" && matches!(record.phase(), Phase::In | Phase::Out)
        ));
        saw_stale |= mirror.saw_stale;
        saw_no_accepting_edge |= mirror.saw_no_accepting_edge;
        saw_holder_removed |= mirror.saw_reap
            && mirror.state.retired().any(|(_, record)| {
                record.retirement().map(Retirement::reason) == Some(RetirementReason::HolderRemoved)
            });
    }
    assert!(saw_stale, "no seed exercised a stale rewrite plan");
    assert!(
        saw_holder_removed,
        "no seed reaped a node that held live packages"
    );
    assert!(
        saw_no_accepting_edge,
        "no seed poisoned a's edges while it held outbound packages"
    );
}
