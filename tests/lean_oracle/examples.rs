//! The six rewrite scenarios of `formal/Ontography/Examples.lean`, run on the
//! kernel with the same definitions, productions, and matches. Each run
//! requires the outcomes the model's `#guard`s state, so the kernel is pinned
//! to them too, and each is replayed in the oracle like any other run.

use std::collections::{BTreeMap, BTreeSet};

use ontography::{PackageId, RetirementReason};

use crate::format::{
    ContractSpec, DefinitionSpec, EdgeDefinitionSpec, EdgeSpec, FragmentSpec, Ingress, Match,
    MatchSpec, NodeSpec, ProductionSpec, RootSpec, SchemaSpec, Validator, hex,
};
use crate::run::{Run, activate, bind, carry, delivered, offer, orig, outbound, outputs, rewrite};

const PAYLOAD: &[u8] = &[1, 2, 3];

/// `result` and `other` accept everything, `payload` accepts exactly the
/// payload, and `deny` accepts nothing.
fn validators() -> BTreeMap<String, Validator> {
    [
        ("result", Validator::AcceptAll),
        ("payload", Validator::BytesEqual(hex(PAYLOAD))),
        ("deny", Validator::RejectAll),
        ("other", Validator::AcceptAll),
    ]
    .into_iter()
    .map(|(id, validator)| (id.to_owned(), validator))
    .collect()
}

/// `Examples.kernel`: every node has type `n`, result contract `result`, and a
/// root rule `{run}`; every edge is a `flow` over `run` with its contract.
fn kernel(nodes: &[&str], edges: &[(&str, &str, &str, &str)], all: &[&str]) -> DefinitionSpec {
    let owned = |items: &[&str]| items.iter().map(|item| (*item).to_owned()).collect();
    DefinitionSpec {
        schema: SchemaSpec {
            node_types: owned(&["n"]),
            object_types: owned(&["t", "other"]),
            tags: owned(&["run", "other"]),
        },
        contracts: [
            ("result", "t"),
            ("payload", "t"),
            ("deny", "t"),
            ("other", "other"),
        ]
        .map(|(id, object_type)| ContractSpec {
            id: id.to_owned(),
            object_type: object_type.to_owned(),
        })
        .to_vec(),
        nodes: owned(nodes),
        edges: edges
            .iter()
            .map(|(id, source, target, _)| EdgeSpec {
                id: (*id).to_owned(),
                source: (*source).to_owned(),
                target: (*target).to_owned(),
            })
            .collect(),
        node_definitions: nodes
            .iter()
            .map(|node| NodeSpec {
                node: (*node).to_owned(),
                types: owned(&["n"]),
                result_contract: "result".to_owned(),
                ingress: if all.contains(node) {
                    Ingress::All
                } else {
                    Ingress::Any
                },
            })
            .collect(),
        edge_definitions: edges
            .iter()
            .map(|(id, _, _, contract)| EdgeDefinitionSpec {
                edge: (*id).to_owned(),
                types: owned(&["flow"]),
                source_requirements: owned(&["n"]),
                target_requirements: owned(&["n"]),
                package_contract: (*contract).to_owned(),
                tags: owned(&["run"]),
                authority_match: Match::AnyOf,
            })
            .collect(),
        transitions: Vec::new(),
        roots: nodes
            .iter()
            .map(|node| RootSpec {
                node: (*node).to_owned(),
                ceiling: owned(&["run"]),
            })
            .collect(),
    }
}

/// `Examples.rule`: a production from `left` to `right` with interface `K`,
/// and the identity-symbol match of it.
fn rule(
    id: &str,
    left: &DefinitionSpec,
    right: &DefinitionSpec,
    interface_nodes: &[&str],
    interface_edges: &[&str],
) -> (ProductionSpec, MatchSpec) {
    let same = |ids: Vec<&String>| ids.into_iter().map(|id| (id.clone(), id.clone())).collect();
    let kept: BTreeSet<&str> = interface_nodes.iter().copied().collect();
    let kept_edges: BTreeSet<&str> = interface_edges.iter().copied().collect();
    let matching = MatchSpec {
        nodes: same(left.nodes.iter().collect()),
        edges: same(left.edges.iter().map(|edge| &edge.id).collect()),
        fresh_nodes: same(
            right
                .nodes
                .iter()
                .filter(|node| !kept.contains(node.as_str()))
                .collect(),
        ),
        fresh_edges: same(
            right
                .edges
                .iter()
                .map(|edge| &edge.id)
                .filter(|edge| !kept_edges.contains(edge.as_str()))
                .collect(),
        ),
    };
    let production = ProductionSpec {
        id: id.to_owned(),
        left: left.fragment(),
        interface_nodes: interface_nodes.iter().map(|id| (*id).to_owned()).collect(),
        interface_edges: interface_edges.iter().map(|id| (*id).to_owned()).collect(),
        right: right.fragment(),
    };
    (production, matching)
}

fn start(name: &str, definition: DefinitionSpec, grammar: Vec<ProductionSpec>) -> Run {
    Run::new(
        format!("examples-{name}"),
        None,
        definition,
        grammar,
        validators(),
    )
}

/// `Examples.delivered`: a root at the edge's source delivering the payload.
fn deliver(run: &mut Run, source: &str, edge: &str) -> PackageId {
    let born = vec![delivered(edge, carry(), PAYLOAD)];
    let id = run.accept_activation(
        "a delivered birth",
        activate(orig(source, &["run"]), PAYLOAD, born),
    );
    outputs::<1>(id)[0]
}

/// `Examples.outbound`: a root at `node` with the payload outbound.
fn wait(run: &mut Run, node: &str) -> PackageId {
    let born = vec![outbound("t", carry(), PAYLOAD)];
    let id = run.accept_activation(
        "an outbound birth",
        activate(orig(node, &["run"]), PAYLOAD, born),
    );
    outputs::<1>(id)[0]
}

/// A package's retirement, or `None` while it is live.
type Fate = Option<(RetirementReason, u64)>;

/// `Examples.outcome`: the nodes, the edges, the fates of `packages`, and the
/// revision.
fn assert_outcome(
    run: &Run,
    nodes: &[&str],
    edges: &[(&str, &str, &str)],
    packages: &[(PackageId, Fate)],
    revision: u64,
) {
    let graph = run.kernel.graph();
    let actual_nodes: BTreeSet<&str> = graph.nodes().iter().map(ontography::Node::id).collect();
    assert_eq!(
        actual_nodes,
        nodes.iter().copied().collect(),
        "{}: nodes",
        run.name
    );
    let actual_edges: BTreeSet<(&str, &str, &str)> = graph
        .edges()
        .iter()
        .map(|edge| (edge.id(), edge.source(), edge.target()))
        .collect();
    assert_eq!(
        actual_edges,
        edges.iter().copied().collect(),
        "{}: edges",
        run.name
    );
    for (package, fate) in packages {
        let record = run
            .state
            .package(*package)
            .expect("the package is recorded");
        let actual = record
            .retirement()
            .map(|retirement| (retirement.reason(), retirement.revision()));
        assert!(
            actual == *fate && (fate.is_some() || record.is_live()),
            "{}: package {package:?} is {:?}, expected {fate:?}",
            run.name,
            record.status()
        );
    }
    assert_eq!(run.state.revision(), revision, "{}: revision", run.name);
}

/// A receipt at an `All` join retires when its route is removed; at `Any` it
/// waits.
fn routes(all: bool) -> Run {
    let receivers: &[&str] = if all { &["B"] } else { &[] };
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], receivers);
    let bare = kernel(&["A", "B"], &[], receivers);
    let (production, matching) = rule("disconnect", &line, &bare, &["A", "B"], &[]);
    let name = if all { "route-all" } else { "route-any" };
    let mut run = start(name, line, vec![production]);
    let receipt = deliver(&mut run, "A", "ab");
    run.accept(
        "the route disconnected",
        rewrite("disconnect", matching, BTreeMap::new()),
    );
    let fate = all.then_some((RetirementReason::RouteRemoved, 2));
    assert_outcome(&run, &["A", "B"], &[], &[(receipt, fate)], 2);
    run
}

/// Deleting a node retires both phases, and its identity cannot be reused.
fn deletion() -> Run {
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let just_a = kernel(&["A"], &[], &[]);
    let (remove, removal) = rule("remove-b", &line, &just_a, &["A"], &[]);
    let (recreate, recreation) = rule("recreate-b", &just_a, &line, &["A"], &[]);
    let mut run = start("delete", line, vec![remove, recreate]);
    let received = deliver(&mut run, "A", "ab");
    let waiting = wait(&mut run, "B");
    run.accept(
        "B deleted with both phases",
        rewrite("remove-b", removal, BTreeMap::new()),
    );
    let removed = Some((RetirementReason::HolderRemoved, 3));
    assert_outcome(
        &run,
        &["A"],
        &[],
        &[(received, removed), (waiting, removed)],
        3,
    );
    run.reject(
        "B recreated under its used identity",
        rewrite("recreate-b", recreation, offer(&[PAYLOAD])),
    );
    run
}

/// A deleted node may not keep an unmatched incident edge.
fn dangling() -> Run {
    let host = kernel(
        &["A", "B", "U"],
        &[("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")],
        &[],
    );
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let just_a = kernel(&["A"], &[], &[]);
    let (production, matching) = rule("dangling", &line, &just_a, &["A"], &[]);
    let mut run = start("dangling", host, vec![production]);
    run.reject(
        "a deletion leaving ub dangling",
        rewrite("dangling", matching, offer(&[PAYLOAD])),
    );
    run
}

/// A preserved node keeps its local policy.
fn policy() -> Run {
    let just_a = kernel(&["A"], &[], &[]);
    let rootless = FragmentSpec {
        roots: Vec::new(),
        ..just_a.fragment()
    };
    let production = |id: &str, right: FragmentSpec| ProductionSpec {
        id: id.to_owned(),
        left: just_a.fragment(),
        interface_nodes: vec!["A".to_owned()],
        interface_edges: Vec::new(),
        right,
    };
    let grammar = vec![
        production("policy-drop-root", rootless),
        production("policy-keep", just_a.fragment()),
    ];
    let mut run = start("policy", just_a, grammar);
    let matching = MatchSpec {
        nodes: bind(&[("A", "A")]),
        ..MatchSpec::default()
    };
    run.reject(
        "a preserved node losing its root rule",
        rewrite("policy-drop-root", matching.clone(), offer(&[PAYLOAD])),
    );
    run.accept(
        "a preserved node keeping its policy",
        rewrite("policy-keep", matching, offer(&[PAYLOAD])),
    );
    assert_outcome(&run, &["A"], &[], &[], 1);
    run
}

/// Rule symbols bind exactly, injectively, and to fresh identities.
fn symbols() -> Run {
    let pattern = kernel(&["X", "Y"], &[("xy", "X", "Y", "payload")], &[]);
    let staged = kernel(
        &["X", "Y", "Z"],
        &[("xz", "X", "Z", "payload"), ("zy", "Z", "Y", "payload")],
        &[],
    );
    let (production, _) = rule("symbols", &pattern, &staged, &["X", "Y"], &[]);
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let mut run = start("symbols", line, vec![production]);
    let symbol_match = |nodes: &[(&str, &str)], fresh: &[(&str, &str)]| MatchSpec {
        nodes: bind(nodes),
        edges: bind(&[("xy", "ab")]),
        fresh_nodes: bind(fresh),
        fresh_edges: bind(&[("xz", "ac"), ("zy", "cb")]),
    };
    for (why, nodes, fresh) in [
        ("a match missing Y", &[("X", "A")][..], &[("Z", "C")][..]),
        (
            "a non-injective match",
            &[("X", "A"), ("Y", "A")],
            &[("Z", "C")],
        ),
        (
            "a fresh node reusing B",
            &[("X", "A"), ("Y", "B")],
            &[("Z", "B")],
        ),
    ] {
        run.reject(
            why,
            rewrite("symbols", symbol_match(nodes, fresh), BTreeMap::new()),
        );
    }
    run.accept(
        "an exact, injective, fresh match",
        rewrite(
            "symbols",
            symbol_match(&[("X", "A"), ("Y", "B")], &[("Z", "C")]),
            BTreeMap::new(),
        ),
    );
    assert_outcome(
        &run,
        &["A", "B", "C"],
        &[("ac", "A", "C"), ("cb", "C", "B")],
        &[],
        1,
    );
    run
}

/// Commutation needs disjoint affected holders. Two packages wait, at `A`
/// and at `C`; one rewrite adds an accepting edge from `A`, the other a
/// rejecting edge from `source`. From `C` the holders are disjoint and both
/// orders agree up to stamps; from `A` both rewrites affect `A`, and the order
/// decides whether `A`'s package retires.
fn commutation(source: &str, accept_first: bool) -> Run {
    let square = kernel(&["A", "B", "C", "D"], &[], &[]);
    let (accept, accepting) = rule(
        "accept",
        &square,
        &kernel(&["A", "B", "C", "D"], &[("ab", "A", "B", "payload")], &[]),
        &["A", "B", "C", "D"],
        &[],
    );
    let (reject, rejecting) = rule(
        "reject",
        &square,
        &kernel(
            &["A", "B", "C", "D"],
            &[("reject", source, "D", "deny")],
            &[],
        ),
        &["A", "B", "C", "D"],
        &[],
    );
    let name = format!(
        "commute-{}-{}-first",
        if source == "C" { "disjoint" } else { "overlap" },
        if accept_first { "accept" } else { "reject" }
    );
    let mut run = start(&name, square, vec![accept, reject]);
    let at_a = wait(&mut run, "A");
    let at_c = wait(&mut run, "C");
    let mut steps = vec![("accept", accepting), ("reject", rejecting)];
    if !accept_first {
        steps.reverse();
    }
    for (production, matching) in steps {
        run.accept(production, rewrite(production, matching, offer(&[PAYLOAD])));
    }
    let retired = |revision| Some((RetirementReason::NoAcceptingEdge, revision));
    let fates = match (source, accept_first) {
        ("C", true) => [None, retired(4)],
        ("C", false) => [None, retired(3)],
        (_, true) => [None, None],
        (_, false) => [retired(3), None],
    };
    assert_outcome(
        &run,
        &["A", "B", "C", "D"],
        &[("ab", "A", "B"), ("reject", source, "D")],
        &[(at_a, fates[0]), (at_c, fates[1])],
        4,
    );
    run
}

/// Every scenario of `Examples.lean`, with the commutation pair from both
/// sources and in both orders.
pub fn runs() -> Vec<Run> {
    let mut runs = vec![
        routes(true),
        routes(false),
        deletion(),
        dangling(),
        policy(),
        symbols(),
    ];
    for source in ["C", "A"] {
        for accept_first in [true, false] {
            runs.push(commutation(source, accept_first));
        }
    }
    runs
}
