//! The fixed definitions random runs explore, the node and edge kinds edits
//! copy, and the required prefixes that pin every rare case.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{AuthorityTag, IngressMode, Kernel, Retirement, RetirementReason};

use crate::format::{
    ContractSpec, DefinitionSpec, EdgeDefinitionSpec, EdgeSpec, EditSpec, FragmentSpec, Ingress,
    Match, NodeSpec, RootSpec, SchemaSpec, TransitionSpec, Validator, hex,
};
use crate::run::{
    DENIED, Run, carry, delivered, extend, joined, names, offer_instead, outbound, outputs,
    removing, retire, rewrite, rewrite_by, rooted, to, transfer, unknown_activation,
    unknown_package,
};

/// A definition with the validator each of its contracts names.
pub struct Setup {
    pub definition: DefinitionSpec,
    pub validators: BTreeMap<String, Validator>,
}

pub struct Fixture {
    pub name: &'static str,
    pub setup: fn() -> Setup,
    pub prefix: fn(&mut Run),
}

pub const FIXTURES: [Fixture; 3] = [
    Fixture {
        name: "coverage",
        setup: coverage_setup,
        prefix: coverage_prefix,
    },
    Fixture {
        name: "cyclic",
        setup: cyclic_setup,
        prefix: cyclic_prefix,
    },
    Fixture {
        name: "sparse",
        setup: sparse_setup,
        prefix: sparse_prefix,
    },
];

/// Contracts no fixture registers at first, which extensions add: `late`
/// accepts everything, `late_deny` nothing, and `late_t2` carries an object
/// type only an extension adds.
pub const LATE_CONTRACTS: [(&str, &str, Validator); 3] = [
    ("late", "t", Validator::AcceptAll),
    ("late_deny", "t", Validator::RejectAll),
    ("late_t2", "t2", Validator::AcceptAll),
];

/// Vocabulary no fixture has at first, which extensions add.
pub const LATE_NODE_TYPE: &str = "n2";
pub const LATE_OBJECT_TYPE: &str = "t2";
pub const LATE_TAG: &str = "extra";

impl Setup {
    /// The validators of the definition and of every late contract.
    pub fn all_validators(&self) -> BTreeMap<String, Validator> {
        let mut validators = self.validators.clone();
        for (id, _, validator) in LATE_CONTRACTS {
            validators.entry(id.to_owned()).or_insert(validator);
        }
        validators
    }
}

// Builders.

fn contracts(list: &[(&str, &str, Validator)]) -> (Vec<ContractSpec>, BTreeMap<String, Validator>) {
    let specs = list
        .iter()
        .map(|(id, object_type, _)| ContractSpec {
            id: (*id).to_owned(),
            object_type: (*object_type).to_owned(),
        })
        .collect();
    let validators = list
        .iter()
        .map(|(id, _, validator)| ((*id).to_owned(), validator.clone()))
        .collect();
    (specs, validators)
}

fn node(id: &str, types: &[&str], result_contract: &str, ingress: Ingress) -> NodeSpec {
    NodeSpec {
        node: id.to_owned(),
        types: names(types),
        result_contract: result_contract.to_owned(),
        ingress,
    }
}

fn edge(
    id: &str,
    (source, target): (&str, &str),
    package_contract: &str,
    tags: &[&str],
    authority_match: Match,
) -> (EdgeSpec, EdgeDefinitionSpec) {
    (
        EdgeSpec {
            id: id.to_owned(),
            source: source.to_owned(),
            target: target.to_owned(),
        },
        EdgeDefinitionSpec {
            edge: id.to_owned(),
            types: names(&["flow"]),
            source_requirements: names(&["n"]),
            target_requirements: Vec::new(),
            package_contract: package_contract.to_owned(),
            tags: names(tags),
            authority_match,
        },
    )
}

fn rule(node: &str, source: &[&str], target: &[&str]) -> TransitionSpec {
    TransitionSpec {
        node: node.to_owned(),
        source: names(source),
        target: names(target),
    }
}

fn root(node: &str, ceiling: &[&str]) -> RootSpec {
    RootSpec {
        node: node.to_owned(),
        ceiling: names(ceiling),
    }
}

fn schema(node_types: &[&str], object_types: &[&str], tags: &[&str]) -> SchemaSpec {
    SchemaSpec {
        node_types: names(node_types),
        object_types: names(object_types),
        tags: names(tags),
    }
}

// The fixed definitions.

/// `a` roots under `{run, audit}` and fans out to `b` over four parallel
/// edges (`AnyOf`, `AllOf`, a rejecting contract, and a `bytes_equal`
/// contract of another object type) and to the `All` node `j` over the
/// parallel edges `aj1` and `aj2`. `j` feeds `x`, which roots under `{run}`,
/// loops on itself, and closes a cycle back to `a`.
fn coverage_setup() -> Setup {
    let (edges, edge_definitions) = [
        edge("ab", ("a", "b"), "c_any", &["run", "audit"], Match::AnyOf),
        edge(
            "ab_all",
            ("a", "b"),
            "c_any",
            &["run", "audit"],
            Match::AllOf,
        ),
        edge("ab_none", ("a", "b"), "c_none", &["run"], Match::AnyOf),
        edge("ab_ok", ("a", "b"), "c_ok", &["run"], Match::AnyOf),
        edge("aj1", ("a", "j"), "c_any", &["run"], Match::AnyOf),
        edge("aj2", ("a", "j"), "c_any", &["run"], Match::AnyOf),
        edge("jx", ("j", "x"), "c_any", &["run", "audit"], Match::AnyOf),
        edge("xx", ("x", "x"), "c_any", &["run"], Match::AnyOf),
        edge("xa", ("x", "a"), "c_even", &["audit"], Match::AnyOf),
    ]
    .into_iter()
    .unzip();
    let (contracts, validators) = contracts(&[
        ("c_any", "t", Validator::AcceptAll),
        ("c_none", "t", Validator::RejectAll),
        ("c_even", "t", Validator::FirstByteEven),
        ("c_ok", "u", Validator::BytesEqual(hex(b"ok"))),
    ]);
    let definition = DefinitionSpec {
        schema: schema(&["n"], &["t", "u"], &["run", "audit", "admin"]),
        contracts,
        nodes: names(&["a", "b", "j", "x"]),
        edges,
        node_definitions: vec![
            node("a", &["n"], "c_any", Ingress::Any),
            node("b", &["n"], "c_even", Ingress::Any),
            node("j", &["n"], "c_any", Ingress::All),
            node("x", &["n"], "c_any", Ingress::Any),
        ],
        edge_definitions,
        transitions: vec![
            rule("a", &["run"], &["audit"]),
            rule("a", &["run", "audit"], &["run", "audit"]),
            rule("a", &["run"], &["run", "admin"]),
            rule("x", &["run"], &[]),
            rule("x", &["run"], &["audit"]),
        ],
        roots: vec![root("a", &["run", "audit"]), root("x", &["run"])],
    };
    Setup {
        definition,
        validators,
    }
}

/// `s` feeds the `All` node `m` over two parallel edges, and `m` also receives
/// on its own self-loop, so a join at `m` needs a delivery `m` made; `m` feeds
/// `k`, which loops on itself through a rejecting contract and closes the
/// cycle back to `s`.
fn cyclic_setup() -> Setup {
    let (edges, edge_definitions) = [
        edge("sm1", ("s", "m"), "acc", &["p"], Match::AnyOf),
        edge("sm2", ("s", "m"), "acc", &["p", "q"], Match::AllOf),
        edge("mm", ("m", "m"), "even", &["p", "q"], Match::AnyOf),
        edge("mk", ("m", "k"), "acc", &["q"], Match::AnyOf),
        edge("ks", ("k", "s"), "acc", &["p"], Match::AnyOf),
        edge("kk", ("k", "k"), "rej", &["p"], Match::AnyOf),
    ]
    .into_iter()
    .unzip();
    let (contracts, validators) = contracts(&[
        ("acc", "t", Validator::AcceptAll),
        ("even", "t", Validator::FirstByteEven),
        ("rej", "t", Validator::RejectAll),
    ]);
    let definition = DefinitionSpec {
        schema: schema(&["n"], &["t"], &["p", "q"]),
        contracts,
        nodes: names(&["s", "m", "k"]),
        edges,
        node_definitions: vec![
            node("s", &["n"], "acc", Ingress::Any),
            node("m", &["n"], "acc", Ingress::All),
            node("k", &["n"], "even", Ingress::Any),
        ],
        edge_definitions,
        transitions: vec![
            rule("m", &["p"], &["p", "q"]),
            rule("k", &["p", "q"], &["p"]),
            rule("k", &["q"], &["p"]),
            rule("s", &["p", "q"], &["p"]),
        ],
        roots: vec![root("s", &["p", "q"]), root("m", &["p"])],
    };
    Setup {
        definition,
        validators,
    }
}

/// `root` reaches the `leaf` node `sink` over an exact-bytes `AllOf` edge and a
/// parallel edge of another object type; `lonely` is an `All` node without
/// incoming edges whose root ceiling is empty. Nodes and edges are declared
/// out of order, since neither side may depend on declaration order.
fn sparse_setup() -> Setup {
    let (mut edges, mut edge_definitions): (Vec<_>, Vec<_>) = [
        edge("rs", ("root", "sink"), "exact", &["r"], Match::AllOf),
        edge("ru", ("root", "sink"), "u_acc", &["r"], Match::AnyOf),
    ]
    .into_iter()
    .unzip();
    edge_definitions[0].target_requirements = names(&["leaf"]);
    edges.sort_by(|left, right| right.id.cmp(&left.id));
    let (contracts, validators) = contracts(&[
        ("acc", "t", Validator::AcceptAll),
        ("u_acc", "u", Validator::AcceptAll),
        ("exact", "t", Validator::BytesEqual(hex(b"\x00\x01"))),
    ]);
    let definition = DefinitionSpec {
        schema: schema(&["n", "leaf"], &["t", "u"], &["r"]),
        contracts,
        nodes: names(&["sink", "lonely", "root"]),
        edges,
        node_definitions: vec![
            node("root", &["n"], "acc", Ingress::Any),
            node("lonely", &["n"], "acc", Ingress::All),
            node("sink", &["n", "leaf"], "exact", Ingress::Any),
        ],
        edge_definitions,
        transitions: vec![rule("root", &["r"], &[]), rule("lonely", &[], &["r"])],
        roots: vec![root("root", &["r"]), root("lonely", &[])],
    };
    Setup {
        definition,
        validators,
    }
}

// Node and edge kinds, which added elements copy.

fn tag_set<'a>(tags: impl Iterator<Item = &'a AuthorityTag>) -> BTreeSet<String> {
    tags.map(|tag| tag.id().to_owned()).collect()
}

/// A node's local definition: its types, result contract, ingress, root
/// ceiling, and authority transitions.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Profile {
    types: BTreeSet<String>,
    result_contract: String,
    ingress: Ingress,
    ceiling: Option<BTreeSet<String>>,
    transitions: BTreeSet<(BTreeSet<String>, BTreeSet<String>)>,
}

/// An edge's annotation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Annotation {
    types: BTreeSet<String>,
    source_requirements: BTreeSet<String>,
    target_requirements: BTreeSet<String>,
    package_contract: String,
    tags: BTreeSet<String>,
    authority_match: Match,
}

pub fn profile_of(kernel: &Kernel, node: &str) -> Option<Profile> {
    let definition = kernel.node_definition(node)?;
    Some(Profile {
        types: definition.types().iter().map(ToString::to_string).collect(),
        result_contract: definition.result_contract().to_owned(),
        ingress: match definition.ingress_mode() {
            IngressMode::Any => Ingress::Any,
            IngressMode::All => Ingress::All,
        },
        ceiling: kernel
            .root_ceiling(node)
            .map(|ceiling| tag_set(ceiling.tags())),
        transitions: kernel
            .authority_transitions()
            .iter()
            .filter(|rule| rule.node_id() == node)
            .map(|rule| (tag_set(rule.from().tags()), tag_set(rule.to().tags())))
            .collect(),
    })
}

pub fn annotation_of(kernel: &Kernel, edge: &str) -> Option<Annotation> {
    let definition = kernel.edge_definition(edge)?;
    let strings = |items: &BTreeSet<Arc<str>>| -> BTreeSet<String> {
        items.iter().map(ToString::to_string).collect()
    };
    Some(Annotation {
        types: strings(definition.types()),
        source_requirements: strings(definition.source_requirements()),
        target_requirements: strings(definition.target_requirements()),
        package_contract: definition.package_contract().to_owned(),
        tags: tag_set(definition.authority_tags().iter()),
        authority_match: match definition.authority_match() {
            ontography::AuthorityMatch::AnyOf => Match::AnyOf,
            ontography::AuthorityMatch::AllOf => Match::AllOf,
        },
    })
}

fn list(items: &BTreeSet<String>) -> Vec<String> {
    items.iter().cloned().collect()
}

impl Profile {
    pub fn types(&self) -> &BTreeSet<String> {
        &self.types
    }

    pub fn with_type(&self, node_type: &str) -> Self {
        let mut types = self.types.clone();
        types.insert(node_type.to_owned());
        Self {
            types,
            ..self.clone()
        }
    }

    /// Adds a node of this kind as `id`, with its definition, root rule, and
    /// authority transitions.
    pub fn place(&self, fragment: &mut FragmentSpec, id: &str) {
        fragment.nodes.push(id.to_owned());
        fragment.node_definitions.push(NodeSpec {
            node: id.to_owned(),
            types: list(&self.types),
            result_contract: self.result_contract.clone(),
            ingress: self.ingress,
        });
        if let Some(ceiling) = &self.ceiling {
            fragment.roots.push(RootSpec {
                node: id.to_owned(),
                ceiling: list(ceiling),
            });
        }
        for (source, target) in &self.transitions {
            fragment.transitions.push(TransitionSpec {
                node: id.to_owned(),
                source: list(source),
                target: list(target),
            });
        }
    }
}

impl Annotation {
    /// Whether nodes of these types may be its source and target.
    pub fn fits(&self, source: &BTreeSet<String>, target: &BTreeSet<String>) -> bool {
        self.source_requirements.is_subset(source) && self.target_requirements.is_subset(target)
    }

    /// Adds an edge of this kind as `id`, from `source` to `target`.
    pub fn connect(&self, fragment: &mut FragmentSpec, id: &str, source: &str, target: &str) {
        fragment.edges.push(EdgeSpec {
            id: id.to_owned(),
            source: source.to_owned(),
            target: target.to_owned(),
        });
        fragment.edge_definitions.push(self.definition(id));
    }

    /// Its definition at `id`.
    pub fn definition(&self, id: &str) -> EdgeDefinitionSpec {
        EdgeDefinitionSpec {
            edge: id.to_owned(),
            types: list(&self.types),
            source_requirements: list(&self.source_requirements),
            target_requirements: list(&self.target_requirements),
            package_contract: self.package_contract.clone(),
            tags: list(&self.tags),
            authority_match: self.authority_match,
        }
    }

    pub fn with_contract(&self, contract: &str) -> Self {
        Self {
            package_contract: contract.to_owned(),
            ..self.clone()
        }
    }

    pub fn with_tag(&self, tag: &str) -> Self {
        let mut tags = self.tags.clone();
        tags.insert(tag.to_owned());
        Self {
            tags,
            ..self.clone()
        }
    }
}

// The required prefixes. Each step states the kernel's intended outcome, so
// the prefix provably reaches every case it names before random exploration.

/// The fixed-graph cases of the coverage fixture.
fn fixed_graph_prefix(run: &mut Run) {
    // Roots, and delivered and outbound births under `Carry`.
    let first = run.accept_activation(
        "a root within its ceiling births delivered and outbound packages",
        rooted(
            "a",
            &["run"],
            vec![
                delivered("ab", carry(), b"\x02A"),
                delivered("aj1", carry(), b"j1"),
                delivered("aj2", carry(), b"j2"),
                outbound("t", carry(), b"out"),
                outbound("u", carry(), b"ok"),
                delivered("ab_ok", carry(), b"ok"),
                outbound("t", carry(), b"\x03A"),
            ],
        ),
    );
    let [at_b, at_j1, at_j2, out_t, out_u, at_b_u, out_odd] = outputs(first);
    run.reject("root outside the schema", rooted("a", &["ghost"], vec![]));
    run.reject("root above the ceiling", rooted("a", &["admin"], vec![]));
    run.reject("root without a root rule", rooted("b", &["run"], vec![]));
    run.reject("root at an unknown node", rooted("nowhere", &[], vec![]));
    let born = vec![outbound("t", carry(), b"no")];
    let [out_empty] = outputs(run.accept_activation("empty root", rooted("a", &[], born)));
    run.reject("result contract", joined(&[at_b], b"\x01", vec![]));

    // Output authority and edge matching.
    let born = vec![delivered("ab", to(&["audit"]), b"\x02A")];
    let audit = run.accept_activation("permitted transition", rooted("a", &["run"], born));
    let [at_b_audit] = outputs(audit);
    let born = vec![outbound("t", to(&["admin"]), b"no")];
    run.reject("forbidden transition", rooted("a", &["run"], born));
    let born = vec![outbound("t", to(&["run"]), b"no")];
    run.reject(
        "explicit preservation without a rule",
        rooted("a", &["run"], born),
    );
    let born = vec![delivered("ab_all", to(&["run", "audit"]), b"\x02A")];
    let both = run.accept_activation(
        "explicit preservation with a rule, over a matched AllOf edge",
        rooted("a", &["run", "audit"], born),
    );
    let [at_b_both] = outputs(both);
    let born = vec![outbound("t", to(&["run", "admin"]), b"no")];
    let amplified = run.accept_activation("amplifying transition", rooted("a", &["run"], born));
    let [out_amplified] = outputs(amplified);
    let born = vec![outbound("t", to(&["ghost"]), b"no")];
    run.reject("transition outside the schema", rooted("a", &["run"], born));
    let born = vec![delivered("ab_all", carry(), b"\x02A")];
    run.reject("AllOf edge missing a tag", rooted("a", &["run"], born));
    let born = vec![delivered("aj1", carry(), b"j1")];
    run.reject("AnyOf edge sharing no tag", rooted("a", &["audit"], born));
    let born = vec![delivered("ab", carry(), b"\x02A")];
    run.accept("AnyOf edge sharing one tag", rooted("a", &["audit"], born));
    let born = vec![delivered("ab_none", carry(), b"\x02A")];
    run.reject(
        "birth the edge contract rejects",
        rooted("a", &["run"], born),
    );
    let born = vec![delivered("ab_ok", carry(), b"no")];
    run.reject("birth unequal to exact bytes", rooted("a", &["run"], born));
    let born = vec![outbound("nope", carry(), b"no")];
    run.reject(
        "outbound birth of an unknown type",
        rooted("a", &["run"], born),
    );
    let born = vec![delivered("zz", carry(), b"no")];
    run.reject("birth on an unknown edge", rooted("a", &["run"], born));
    let born = vec![delivered("xx", carry(), b"no")];
    run.reject("birth on another node's edge", rooted("a", &["run"], born));
    let born = vec![
        delivered("ab", carry(), b"\x02A"),
        delivered("ab_none", carry(), b"\x02A"),
    ];
    run.reject(
        "one inadmissible birth among others",
        rooted("a", &["run"], born),
    );

    // The `All` join at `j` over the parallel edges `aj1` and `aj2`.
    run.reject("incomplete All join", joined(&[at_j1], b"r", vec![]));
    let born = vec![delivered("aj1", carry(), b"j1")];
    let [at_j1_again] =
        outputs(run.accept_activation("second on aj1", rooted("a", &["run"], born)));
    let inputs = [at_j1, at_j1_again];
    run.reject("All join, two on one edge", joined(&inputs, b"r", vec![]));
    let inputs = [at_j1, at_j1_again, at_j2];
    run.reject("All join repeating an edge", joined(&inputs, b"r", vec![]));
    let born = vec![delivered("aj1", carry(), b"j1")];
    let wide = run.accept_activation("wider on aj1", rooted("a", &["run", "audit"], born));
    let [at_j1_wide] = outputs(wide);
    let inputs = [at_j1_wide, at_j2];
    run.reject(
        "All join, mismatched authorities",
        joined(&inputs, b"r", vec![]),
    );
    run.reject(
        "All join, outbound input",
        joined(&[out_t, at_j2], b"r", vec![]),
    );
    let born = vec![delivered("jx", carry(), b"\x02A")];
    let join = run.accept_activation("complete All join", joined(&[at_j1, at_j2], b"r", born));
    let [at_x] = outputs(join);
    run.reject(
        "All join, consumed inputs",
        joined(&[at_j1, at_j2], b"r", vec![]),
    );

    // `Any` activations at `b`.
    run.accept("Any activation", joined(&[at_b], b"\x02", vec![]));
    let born = vec![
        delivered("ab", carry(), b"\x02A"),
        delivered("ab", carry(), b"payload"),
    ];
    let pair = run.accept_activation("two on ab", rooted("a", &["run"], born));
    let [at_b_first, at_b_second] = outputs(pair);
    let inputs = [at_b_first, at_b_second];
    run.reject(
        "Any join, two on one edge",
        joined(&inputs, b"\x02", vec![]),
    );
    let inputs = [at_b_first, at_b_u];
    run.reject(
        "Any join, two on parallel edges",
        joined(&inputs, b"\x02", vec![]),
    );
    let inputs = [at_b_first, at_b_audit];
    run.reject(
        "Any join, mismatched authorities",
        joined(&inputs, b"\x02", vec![]),
    );
    run.reject(
        "Any join, outbound input",
        joined(&[out_t], b"\x02", vec![]),
    );
    run.reject("no inputs", joined(&[], b"\x02", vec![]));
    run.reject(
        "unknown input",
        joined(&[unknown_package()], b"\x02", vec![]),
    );
    run.reject("consumed input", joined(&[at_b], b"\x02", vec![]));

    // Self-loops.
    let born = vec![delivered("xx", carry(), b"loop")];
    let [at_x_loop] =
        outputs(run.accept_activation("self-loop birth", rooted("x", &["run"], born)));
    let born = vec![
        delivered("xx", carry(), b"loop"),
        outbound("t", to(&[]), b"no"),
        delivered("xa", to(&["audit"]), b"\x02A"),
        outbound("t", carry(), b"loop"),
    ];
    let relooped = run.accept_activation(
        "consume a self-loop delivery and deliver on the loop again",
        joined(&[at_x_loop], b"r", born),
    );
    let [_, out_x_empty, _, out_x] = outputs(relooped);
    run.accept("consume the join's output", joined(&[at_x], b"r", vec![]));

    // Transfers.
    run.accept("transfer", transfer(out_t, "ab", b"out"));
    run.reject("transfer, delivered", transfer(out_t, "ab", b"out"));
    run.reject("transfer, wrong source", transfer(out_odd, "xx", b"\x03A"));
    run.reject("transfer, unknown edge", transfer(out_odd, "zz", b"\x03A"));
    run.reject(
        "transfer, type mismatch",
        transfer(out_odd, "ab_ok", b"\x03A"),
    );
    run.reject("transfer, AnyOf mismatch", transfer(out_empty, "ab", b"no"));
    run.reject(
        "transfer, AllOf mismatch",
        transfer(out_odd, "ab_all", b"\x03A"),
    );
    run.reject("transfer, contract", transfer(out_odd, "ab_none", b"\x03A"));
    run.reject("transfer, digest mismatch", transfer(out_odd, "aj1", b"j1"));
    run.accept(
        "transfer, committed bytes",
        transfer(out_odd, "aj1", b"\x03A"),
    );
    run.accept("transfer, exact bytes", transfer(out_u, "ab_ok", b"ok"));
    run.reject("transfer, consumed", transfer(at_j1, "aj1", b"j1"));
    run.reject(
        "transfer, unknown",
        transfer(unknown_package(), "ab", b"no"),
    );
    run.reject(
        "self-loop, AnyOf mismatch",
        transfer(out_x_empty, "xx", b"no"),
    );
    run.accept("transfer on a self-loop", transfer(out_x, "xx", b"loop"));
    run.reject("amplified, AllOf", transfer(out_amplified, "ab_all", b"no"));
    run.accept("amplified, AnyOf", transfer(out_amplified, "ab", b"no"));

    // Retirements.
    run.accept("retire live", retire(at_b_audit, None));
    run.reject("retire retired", retire(at_b_audit, None));
    run.reject("retire consumed", retire(at_b, None));
    run.accept("retire with evidence", retire(at_b_both, Some(first)));
    let evidence = Some(unknown_activation());
    run.reject(
        "retire with unknown evidence",
        retire(at_b_second, evidence),
    );
    run.accept("retire outbound", retire(out_empty, Some(join)));
    run.reject("retire unknown", retire(unknown_package(), None));
    run.reject("consume retired", joined(&[at_b_audit], b"\x02", vec![]));
    run.reject("transfer retired", transfer(out_empty, "ab", b"no"));
}

fn cyclic_prefix(run: &mut Run) {
    let born = vec![
        delivered("sm1", carry(), b"\x00"),
        delivered("sm2", carry(), b"\x02A"),
    ];
    let first = run.accept_activation("both parallel edges into m", rooted("s", &["p", "q"], born));
    let [via_sm1, via_sm2] = outputs(first);
    let born = vec![delivered("mm", to(&["p", "q"]), b"\x00")];
    let [via_mm] =
        outputs(run.accept_activation("m feeds its own loop", rooted("m", &["p"], born)));
    let inputs = [via_sm1, via_sm2];
    run.reject(
        "join at m without its self-loop",
        joined(&inputs, b"r", vec![]),
    );
    let born = vec![
        delivered("mm", carry(), b"\x02A"),
        delivered("mk", carry(), b"\x00"),
    ];
    let join = run.accept_activation(
        "complete All join over parallel edges and a self-loop",
        joined(&[via_sm1, via_sm2, via_mm], b"r", born),
    );
    let [_, at_k] = outputs(join);
    let born = vec![delivered("mm", to(&["p", "q"]), b"\x01")];
    run.reject("self-loop contract", rooted("m", &["p"], born));
    let born = vec![delivered("ks", to(&["p"]), b"\x00")];
    run.accept("cycle back to s", joined(&[at_k], b"\x02", born));
}

fn sparse_prefix(run: &mut Run) {
    let born = vec![outbound("t", to(&["r"]), b"\x00\x01")];
    let lonely = run.accept_activation("root under an empty ceiling", rooted("lonely", &[], born));
    let [out_lonely] = outputs(lonely);
    run.reject(
        "root above an empty ceiling",
        rooted("lonely", &["r"], vec![]),
    );
    run.reject(
        "All node without incoming edges",
        joined(&[out_lonely], b"r", vec![]),
    );
    let born = vec![
        delivered("rs", carry(), b"\x00\x01"),
        outbound("u", carry(), b"no"),
        outbound("t", to(&[]), b"no"),
    ];
    let [at_sink, out_u, out_t] =
        outputs(run.accept_activation("exact bytes", rooted("root", &["r"], born)));
    run.reject(
        "result unequal to exact bytes",
        joined(&[at_sink], b"no", vec![]),
    );
    run.accept(
        "result equal to exact bytes",
        joined(&[at_sink], b"\x00\x01", vec![]),
    );
    run.accept("transfer on a parallel edge", transfer(out_u, "ru", b"no"));
    run.reject("transfer, empty authority", transfer(out_t, "rs", b"no"));
}

fn coverage_prefix(run: &mut Run) {
    fixed_graph_prefix(run);
    rewrite_prefix(run);
}

/// Rewrites and extensions on the coverage fixture, after its fixed-graph
/// prefix: every way an edit can fail, evidence missing, mismatched, and
/// complete, the policy refusing its principal, a stage inserted and removed
/// with both phases of its node, a route removed at an `All` receiver, an
/// added node with its own root rule and transitions, extensions that enable
/// an edit, and stale and current plans.
fn rewrite_prefix(run: &mut Run) {
    let waiting = run.accept_activation(
        "outbound work at a",
        rooted(
            "a",
            &["run"],
            vec![
                outbound("t", carry(), b"\x02A"),
                outbound("u", carry(), b"no"),
            ],
        ),
    );
    let [waiting_t, waiting_u] = outputs(waiting);
    let kernel = Arc::clone(&run.kernel);
    let kind = |edge: &str| annotation_of(&kernel, edge).expect("a fixture edge");
    let like = |node: &str| profile_of(&kernel, node).expect("a fixture node");
    let (ab, aj1) = (kind("ab"), kind("aj1"));
    let mend = |id: &str| {
        let mut edit = EditSpec::default();
        ab.connect(&mut edit.add, id, "a", "b");
        edit
    };
    let swapped = offer_instead(&[(b"\x02A", b"no"), (b"no", b"\x02A")]);

    // Evidence: a changed holder's waiting work is rechecked against its bytes.
    run.reject("missing evidence", rewrite(mend("ab~1"), BTreeMap::new()));
    run.reject("mismatched evidence", rewrite(mend("ab~1"), swapped));
    run.reject(
        "an admissible edit its principal may not make",
        rewrite_by(DENIED, mend("ab~1"), run.known_evidence()),
    );
    run.accept(
        "an accepting edge added from a holder with waiting work",
        rewrite(mend("ab~1"), run.known_evidence()),
    );
    assert!(
        run.state.package(waiting_t).unwrap().is_live(),
        "the new edge carries the waiting t package"
    );
    assert_eq!(
        run.state
            .package(waiting_u)
            .and_then(|record| record.retirement())
            .map(Retirement::reason),
        Some(RetirementReason::NoAcceptingEdge),
        "no edge from a carries the waiting u package's bytes"
    );

    // Edits that fail.
    let evidence = run.known_evidence();
    let refuse = |run: &mut Run, why: &str, edit: EditSpec| {
        run.reject(why, rewrite(edit, evidence.clone()));
    };
    refuse(run, "an added edge reusing a current identity", mend("ab"));
    refuse(
        run,
        "removing a node the graph lacks",
        removing(&["ghost"], &[]),
    );
    refuse(
        run,
        "removing an edge the graph lacks",
        removing(&[], &["zz"]),
    );
    refuse(
        run,
        "a removed node leaving an edge dangling",
        removing(&["b"], &["ab", "ab_all", "ab_none", "ab_ok"]),
    );
    let mut redefined = EditSpec::default();
    redefined
        .add
        .node_definitions
        .push(node("a", &["n"], "c_any", Ingress::Any));
    refuse(run, "a surviving node redefined", redefined);
    let mut given_rule = EditSpec::default();
    given_rule
        .add
        .transitions
        .push(rule("b", &["run"], &["audit"]));
    refuse(run, "a surviving node given a transition", given_rule);
    let mut given_root = EditSpec::default();
    given_root.add.roots.push(root("b", &["run"]));
    refuse(run, "a surviving node given a root rule", given_root);
    let mut relabelled = EditSpec::default();
    relabelled
        .add
        .edge_definitions
        .push(ab.with_contract("c_none").definition("ab"));
    refuse(run, "a surviving edge redefined", relabelled);
    let mut undefined = EditSpec::default();
    undefined.add.nodes.push("n~1".to_owned());
    refuse(run, "an added node without a definition", undefined);
    let mut twice = EditSpec::default();
    like("b").place(&mut twice.add, "n~1");
    like("b").place(&mut twice.add, "n~1");
    refuse(run, "one node added twice", twice);
    let mut stranded = removing(&["x"], &["jx", "xx", "xa"]);
    ab.connect(&mut stranded.add, "ax~1", "a", "x");
    refuse(run, "an added edge ending at a removed node", stranded);
    let mut nameless = EditSpec::default();
    like("b").place(&mut nameless.add, "");
    refuse(run, "an added node with an empty identity", nameless);

    // Identity rewrites.
    run.accept(
        "the empty edit",
        rewrite(EditSpec::default(), evidence.clone()),
    );
    run.reject(
        "the empty edit, asked by a principal the policy refuses",
        rewrite_by(DENIED, EditSpec::default(), evidence.clone()),
    );

    // A stage inserted on the `All` receiver's route, then removed with its node.
    let stage = |route: &str, node: &str, into: &str, onward: &str| {
        let mut edit = removing(&[], &[route]);
        like("j").place(&mut edit.add, node);
        aj1.connect(&mut edit.add, into, "a", node);
        aj1.connect(&mut edit.add, onward, node, "j");
        edit
    };
    refuse(
        run,
        "one edge added twice",
        stage("aj1", "z~1", "f~1", "f~1"),
    );
    run.accept(
        "a stage inserted on a route into an All receiver",
        rewrite(stage("aj1", "z~1", "f~1", "g~1"), evidence.clone()),
    );
    assert!(
        run.state.retired().any(|(_, record)| record
            .retirement()
            .is_some_and(|retirement| retirement.reason() == RetirementReason::RouteRemoved)),
        "removing aj1 retires the receipts it delivered to the All receiver j"
    );
    let staged = run.accept_activation(
        "deliveries into the staged node",
        rooted(
            "a",
            &["run"],
            vec![
                delivered("f~1", carry(), b"\x02A"),
                delivered("f~1", carry(), b"\x02A"),
            ],
        ),
    );
    let [received, held] = outputs(staged);
    let consumed = run.accept_activation(
        "a join at the staged node births outbound work there",
        joined(&[received], b"r", vec![outbound("t", carry(), b"\x02A")]),
    );
    let [waiting_z] = outputs(consumed);
    let mut unstage = removing(&["z~1"], &["f~1", "g~1"]);
    aj1.connect(&mut unstage.add, "aj1~1", "a", "j");
    run.accept(
        "the staged node removed with both of its phases",
        rewrite(unstage, run.known_evidence()),
    );
    for package in [held, waiting_z] {
        assert_eq!(
            run.state
                .package(package)
                .and_then(|record| record.retirement())
                .map(Retirement::reason),
            Some(RetirementReason::HolderRemoved),
            "unstaging retires what the staged node held"
        );
    }
    run.reject(
        "an added node reusing a removed identity",
        rewrite(stage("aj1~1", "z~1", "f~2", "g~2"), run.known_evidence()),
    );
    run.reject(
        "an added edge reusing a removed identity",
        rewrite(mend("f~1"), run.known_evidence()),
    );

    // An added node with its own root rule and authority transitions.
    let mut spawned = EditSpec::default();
    like("a").place(&mut spawned.add, "a~1");
    run.accept(
        "a node added with a root rule and authority transitions",
        rewrite(spawned, run.known_evidence()),
    );
    let born = vec![outbound("t", to(&["audit"]), b"\x02A")];
    run.accept(
        "a root and a transition at the added node",
        rooted("a~1", &["run"], born),
    );

    // Extensions, and an edit they enable.
    let late = || {
        let mut edit = EditSpec::default();
        ab.with_contract("late")
            .connect(&mut edit.add, "late~1", "a", "b");
        edit
    };
    run.reject(
        "an edit naming an unregistered contract",
        rewrite(late(), run.known_evidence()),
    );
    let mut wider = run.definition.schema.clone();
    wider.tags.push("extra".to_owned());
    let mut contracts = run.definition.contracts.clone();
    for (id, object_type) in [("late", "t"), ("late_deny", "t")] {
        contracts.push(ContractSpec {
            id: id.to_owned(),
            object_type: object_type.to_owned(),
        });
    }
    run.accept(
        "an extension adding a tag and contracts",
        extend(wider.clone(), contracts.clone()),
    );
    run.accept(
        "an edit the extension enabled",
        rewrite(late(), run.known_evidence()),
    );
    run.reject(
        "an extension adding nothing",
        extend(wider.clone(), contracts.clone()),
    );
    run.reject(
        "an extension dropping a tag",
        extend(run.definition.schema.clone(), contracts.clone()),
    );
    run.reject(
        "an extension dropping a contract",
        extend(wider.clone(), contracts[..contracts.len() - 1].to_vec()),
    );
    let mut typed = contracts.clone();
    typed.push(ContractSpec {
        id: "late_t2".to_owned(),
        object_type: "t2".to_owned(),
    });
    run.reject(
        "a contract of an object type outside the schema",
        extend(wider.clone(), typed.clone()),
    );
    let mut widest = wider.clone();
    widest.object_types.push("t2".to_owned());
    run.accept(
        "a contract of an object type the extension adds",
        extend(widest.clone(), typed),
    );

    // Plans: stale after an accepted change, current after a rejected op.
    let mend_plan = |run: &mut Run| {
        let mut edit = EditSpec::default();
        aj1.connect(&mut edit.add, "aj~2", "a", "j");
        rewrite(edit, run.known_evidence())
    };
    let op = mend_plan(run);
    let plan = run.plan(op).expect("the rewrite prepares");
    run.accept("a change after preparation", rooted("a", &["run"], vec![]));
    assert!(
        !run.commit_plan(plan),
        "a plan prepared before a change is stale"
    );
    let op = mend_plan(run);
    let plan = run.plan(op).expect("the rewrite prepares");
    run.reject(
        "a rejected op changes nothing",
        retire(unknown_package(), Some(unknown_activation())),
    );
    assert!(
        run.commit_plan(plan),
        "a plan with no change since is current"
    );
    let mut grown = widest.clone();
    grown.node_types.push("n2".to_owned());
    let current_contracts = run
        .kernel
        .contracts()
        .iter()
        .map(|contract| ContractSpec {
            id: contract.id().to_owned(),
            object_type: contract.object_type().to_owned(),
        })
        .collect::<Vec<_>>();
    let plan = run
        .plan(extend(grown.clone(), current_contracts.clone()))
        .expect("the extension prepares");
    run.accept("a change after preparation", rooted("a", &["run"], vec![]));
    assert!(
        !run.commit_plan(plan),
        "an extension prepared before a change is stale"
    );
    let plan = run
        .plan(extend(grown, current_contracts))
        .expect("the extension prepares");
    assert!(
        run.commit_plan(plan),
        "an extension with no change since is current"
    );
    assert_eq!(run.stale, 2);
}
