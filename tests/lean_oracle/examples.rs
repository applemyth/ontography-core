//! The rewrite scenarios of `formal/Ontography/Examples.lean`, run on the
//! kernel with the same definitions and edits. Each run requires the outcomes
//! the model's `#guard`s state, so the kernel is pinned to them too, and each
//! is replayed in the oracle like any other run. A `#guard` evaluated from a
//! fresh state becomes a run of its own, or a later step of one when the
//! earlier steps were rejected and so left the state unchanged. Two guards
//! cannot be traces: removing one node twice, since a kernel edit removes a
//! set, and a policy other than the traces' fixed one.

use std::collections::{BTreeMap, BTreeSet};

use ontography::{PackageId, RetirementReason};

use crate::format::{
    ContractSpec, DefinitionSpec, EdgeDefinitionSpec, EdgeSpec, EditSpec, FragmentSpec, Ingress,
    Match, NodeSpec, RootSpec, SchemaSpec, TransitionSpec, Validator, hex,
};
use crate::run::{
    DENIED, Run, activate, carry, delivered, offer, orig, outbound, outputs, removing, rewrite,
    rewrite_by, sorted,
};

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

/// `Examples.diff`: the edit taking `before` to `after`, removing the nodes
/// and edges `after` lacks and adding the ones `before` lacks with their
/// annotations and policies in `after`.
fn diff(before: &DefinitionSpec, after: &DefinitionSpec) -> EditSpec {
    let node_ids = |definition: &DefinitionSpec| -> BTreeSet<String> {
        definition.nodes.iter().cloned().collect()
    };
    let edge_ids = |definition: &DefinitionSpec| -> BTreeSet<String> {
        definition
            .edges
            .iter()
            .map(|edge| edge.id.clone())
            .collect()
    };
    let (old_nodes, new_nodes) = (node_ids(before), node_ids(after));
    let (old_edges, new_edges) = (edge_ids(before), edge_ids(after));
    let added = |id: &String| !old_nodes.contains(id);
    EditSpec {
        remove_nodes: sorted(old_nodes.difference(&new_nodes).map(String::as_str)),
        remove_edges: sorted(old_edges.difference(&new_edges).map(String::as_str)),
        add: FragmentSpec {
            nodes: after.nodes.iter().filter(|id| added(id)).cloned().collect(),
            edges: after
                .edges
                .iter()
                .filter(|edge| !old_edges.contains(&edge.id))
                .cloned()
                .collect(),
            node_definitions: after
                .node_definitions
                .iter()
                .filter(|definition| added(&definition.node))
                .cloned()
                .collect(),
            edge_definitions: after
                .edge_definitions
                .iter()
                .filter(|definition| !old_edges.contains(&definition.edge))
                .cloned()
                .collect(),
            transitions: after
                .transitions
                .iter()
                .filter(|rule| added(&rule.node))
                .cloned()
                .collect(),
            roots: after
                .roots
                .iter()
                .filter(|root| added(&root.node))
                .cloned()
                .collect(),
        },
    }
}

fn start(name: &str, definition: DefinitionSpec) -> Run {
    Run::new(format!("examples-{name}"), None, definition, validators())
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
    let name = if all { "route-all" } else { "route-any" };
    let mut run = start(name, line.clone());
    let receipt = deliver(&mut run, "A", "ab");
    run.accept(
        "the route disconnected",
        rewrite(diff(&line, &bare), BTreeMap::new()),
    );
    let fate = all.then_some((RetirementReason::RouteRemoved, 2));
    assert_outcome(&run, &["A", "B"], &[], &[(receipt, fate)], 2);
    run
}

/// Deleting a node retires both phases, and its identity cannot be reused.
fn deletion() -> Run {
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let just_a = kernel(&["A"], &[], &[]);
    let mut run = start("delete", line.clone());
    let received = deliver(&mut run, "A", "ab");
    let waiting = wait(&mut run, "B");
    run.accept(
        "B deleted with both phases",
        rewrite(diff(&line, &just_a), BTreeMap::new()),
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
        rewrite(diff(&just_a, &line), offer(&[PAYLOAD])),
    );
    run
}

/// A removed node takes every edge at it with it.
fn dangling() -> Run {
    let fork = kernel(
        &["A", "B", "U"],
        &[("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")],
        &[],
    );
    let mut run = start("dangling", fork);
    run.reject(
        "B removed leaving ub dangling",
        rewrite(removing(&["B"], &["ab"]), BTreeMap::new()),
    );
    run.accept(
        "B removed with every edge at it",
        rewrite(removing(&["B"], &["ab", "ub"]), BTreeMap::new()),
    );
    assert_outcome(&run, &["A", "U"], &[], &[], 1);
    run
}

/// A surviving node keeps its definition and policies: an edit may give an
/// authority transition or a root rule only to a node it adds.
fn survivor() -> Vec<Run> {
    let just_a = kernel(&["A"], &[], &[]);
    let mut run = start("survivor", just_a.clone());
    let mut given_rule = EditSpec::default();
    given_rule.add.transitions.push(TransitionSpec {
        node: "A".to_owned(),
        source: vec!["run".to_owned()],
        target: vec!["other".to_owned()],
    });
    run.reject(
        "a surviving node given a transition",
        rewrite(given_rule, BTreeMap::new()),
    );
    run.accept(
        "the empty edit",
        rewrite(EditSpec::default(), BTreeMap::new()),
    );
    assert_outcome(&run, &["A"], &[], &[], 1);
    let rootless = DefinitionSpec {
        roots: Vec::new(),
        ..just_a
    };
    let mut unrooted = start("survivor-root", rootless);
    let mut given_root = EditSpec::default();
    given_root.add.roots.push(RootSpec {
        node: "A".to_owned(),
        ceiling: vec!["run".to_owned()],
    });
    unrooted.reject(
        "a surviving node given a root rule",
        rewrite(given_root, BTreeMap::new()),
    );
    vec![run, unrooted]
}

/// An edit removes current identities and allocates only unused ones.
fn identities() -> Vec<Run> {
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let inserted = kernel(
        &["A", "B", "C"],
        &[("ac", "A", "C", "payload"), ("cb", "C", "B", "payload")],
        &[],
    );
    let mut insert = start("insert", line.clone());
    insert.accept(
        "C inserted on the route",
        rewrite(diff(&line, &inserted), BTreeMap::new()),
    );
    assert_outcome(
        &insert,
        &["A", "B", "C"],
        &[("ac", "A", "C"), ("cb", "C", "B")],
        &[],
        1,
    );
    // Replace `ab` by a reversed edge named `id`.
    let reverse = |id: &str| {
        let reversed = kernel(&["A", "B"], &[(id, "B", "A", "payload")], &[]);
        let mut edit = removing(&[], &["ab"]);
        edit.add.edges = reversed.edges;
        edit.add.edge_definitions = reversed.edge_definitions;
        edit
    };
    let mut run = start("reverse", line);
    run.reject(
        "an edge identity reallocated by the edit removing it",
        rewrite(reverse("ab"), BTreeMap::new()),
    );
    run.reject(
        "removing a node the graph lacks",
        rewrite(removing(&["C"], &[]), BTreeMap::new()),
    );
    run.accept(
        "ab replaced by a reversed edge",
        rewrite(reverse("ba"), BTreeMap::new()),
    );
    assert_outcome(&run, &["A", "B"], &[("ba", "B", "A")], &[], 1);
    vec![insert, run]
}

/// The policy sees the principal: the one the traces' policy refuses may not
/// make an edit the manager may.
fn policy() -> Run {
    let pair = kernel(&["A", "B"], &[], &[]);
    let line = kernel(&["A", "B"], &[("ab", "A", "B", "payload")], &[]);
    let mut run = start("policy", pair.clone());
    run.reject(
        "an edit asked by the refused principal",
        rewrite_by(DENIED, diff(&pair, &line), BTreeMap::new()),
    );
    run.accept(
        "the same edit asked by the manager",
        rewrite(diff(&pair, &line), BTreeMap::new()),
    );
    assert_outcome(&run, &["A", "B"], &[("ab", "A", "B")], &[], 1);
    run
}

/// Commutation needs disjoint affected holders. Two packages wait, at `A`
/// and at `C`; one rewrite adds an accepting edge from `A`, the other a
/// rejecting edge from `source`. From `C` the holders are disjoint and both
/// orders agree up to stamps; from `A` both rewrites affect `A`, and the order
/// decides whether `A`'s package retires.
fn commutation(source: &str, accept_first: bool) -> Run {
    let square = kernel(&["A", "B", "C", "D"], &[], &[]);
    let accepting = diff(
        &square,
        &kernel(&["A", "B", "C", "D"], &[("ab", "A", "B", "payload")], &[]),
    );
    let rejecting = diff(
        &square,
        &kernel(
            &["A", "B", "C", "D"],
            &[("reject", source, "D", "deny")],
            &[],
        ),
    );
    let name = format!(
        "commute-{}-{}-first",
        if source == "C" { "disjoint" } else { "overlap" },
        if accept_first { "accept" } else { "reject" }
    );
    let mut run = start(&name, square);
    let at_a = wait(&mut run, "A");
    let at_c = wait(&mut run, "C");
    let mut steps = vec![("accept", accepting), ("reject", rejecting)];
    if !accept_first {
        steps.reverse();
    }
    for (why, edit) in steps {
        run.accept(why, rewrite(edit, offer(&[PAYLOAD])));
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

/// Every scenario of `Examples.lean` a trace can express, with the
/// commutation pair from both sources and in both orders.
pub fn runs() -> Vec<Run> {
    let mut runs = vec![
        routes(true),
        routes(false),
        deletion(),
        dangling(),
        policy(),
    ];
    runs.extend(survivor());
    runs.extend(identities());
    for source in ["C", "A"] {
        for accept_first in [true, false] {
            runs.push(commutation(source, accept_first));
        }
    }
    runs
}
