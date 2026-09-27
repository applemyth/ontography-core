//! The fixed definitions random runs explore, the rewrite grammar derived
//! from each, and the required prefixes that pin every rare case.

use std::collections::{BTreeMap, BTreeSet};

use ontography::{AuthorityTag, IngressMode, Kernel, Retirement, RetirementReason};

use crate::format::{
    ContractSpec, DefinitionSpec, EdgeDefinitionSpec, EdgeSpec, FragmentSpec, Ingress, Match,
    MatchSpec, NodeSpec, ProductionSpec, RootSpec, SchemaSpec, TransitionSpec, Validator, hex,
};
use crate::run::{
    Run, bind, carry, delivered, extend, joined, names, offer_instead, outbound, outputs, retire,
    rewrite, rooted, to, transfer, unknown_activation, unknown_package,
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

// Node and edge kinds, as rewrites compare them.

fn set(items: &[String]) -> BTreeSet<String> {
    items.iter().cloned().collect()
}

fn tag_set<'a>(tags: impl Iterator<Item = &'a AuthorityTag>) -> BTreeSet<String> {
    tags.map(|tag| tag.id().to_owned()).collect()
}

/// What a rewrite requires a matched or preserved node to keep: its types,
/// result contract, ingress, root ceiling, and authority transitions.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Profile {
    types: BTreeSet<String>,
    result_contract: String,
    ingress: Ingress,
    ceiling: Option<BTreeSet<String>>,
    transitions: BTreeSet<(BTreeSet<String>, BTreeSet<String>)>,
}

/// What a rewrite requires a matched or preserved edge to keep.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Annotation {
    types: BTreeSet<String>,
    source_requirements: BTreeSet<String>,
    target_requirements: BTreeSet<String>,
    package_contract: String,
    tags: BTreeSet<String>,
    authority_match: Match,
}

pub fn profile_in(fragment: &FragmentSpec, node: &str) -> Profile {
    let definition = fragment
        .node_definitions
        .iter()
        .find(|definition| definition.node == node)
        .unwrap_or_else(|| panic!("node {node} has a definition"));
    Profile {
        types: set(&definition.types),
        result_contract: definition.result_contract.clone(),
        ingress: definition.ingress,
        ceiling: fragment
            .roots
            .iter()
            .find(|root| root.node == node)
            .map(|root| set(&root.ceiling)),
        transitions: fragment
            .transitions
            .iter()
            .filter(|rule| rule.node == node)
            .map(|rule| (set(&rule.source), set(&rule.target)))
            .collect(),
    }
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

pub fn annotation_in(fragment: &FragmentSpec, edge: &str) -> Annotation {
    let definition = fragment
        .edge_definitions
        .iter()
        .find(|definition| definition.edge == edge)
        .unwrap_or_else(|| panic!("edge {edge} has a definition"));
    Annotation {
        types: set(&definition.types),
        source_requirements: set(&definition.source_requirements),
        target_requirements: set(&definition.target_requirements),
        package_contract: definition.package_contract.clone(),
        tags: set(&definition.tags),
        authority_match: definition.authority_match,
    }
}

pub fn annotation_of(kernel: &Kernel, edge: &str) -> Option<Annotation> {
    let definition = kernel.edge_definition(edge)?;
    let strings = |items: &BTreeSet<std::sync::Arc<str>>| -> BTreeSet<String> {
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

impl Profile {
    fn with_type(&self, node_type: &str) -> Self {
        let mut types = self.types.clone();
        types.insert(node_type.to_owned());
        Self {
            types,
            ..self.clone()
        }
    }

    /// Places a node of this kind at `symbol`.
    fn place(&self, fragment: &mut FragmentSpec, symbol: &str) {
        let list = |items: &BTreeSet<String>| items.iter().cloned().collect::<Vec<_>>();
        fragment.nodes.push(symbol.to_owned());
        fragment.node_definitions.push(NodeSpec {
            node: symbol.to_owned(),
            types: list(&self.types),
            result_contract: self.result_contract.clone(),
            ingress: self.ingress,
        });
        if let Some(ceiling) = &self.ceiling {
            fragment.roots.push(RootSpec {
                node: symbol.to_owned(),
                ceiling: list(ceiling),
            });
        }
        for (source, target) in &self.transitions {
            fragment.transitions.push(TransitionSpec {
                node: symbol.to_owned(),
                source: list(source),
                target: list(target),
            });
        }
    }
}

impl Annotation {
    /// Places an edge of this kind at `symbol`, from `source` to `target`.
    fn connect(&self, fragment: &mut FragmentSpec, symbol: &str, source: &str, target: &str) {
        let list = |items: &BTreeSet<String>| items.iter().cloned().collect::<Vec<_>>();
        fragment.edges.push(EdgeSpec {
            id: symbol.to_owned(),
            source: source.to_owned(),
            target: target.to_owned(),
        });
        fragment.edge_definitions.push(EdgeDefinitionSpec {
            edge: symbol.to_owned(),
            types: list(&self.types),
            source_requirements: list(&self.source_requirements),
            target_requirements: list(&self.target_requirements),
            package_contract: self.package_contract.clone(),
            tags: list(&self.tags),
            authority_match: self.authority_match,
        });
    }

    fn with_contract(&self, contract: &str) -> Self {
        Self {
            package_contract: contract.to_owned(),
            ..self.clone()
        }
    }

    fn with_tag(&self, tag: &str) -> Self {
        let mut tags = self.tags.clone();
        tags.insert(tag.to_owned());
        Self {
            tags,
            ..self.clone()
        }
    }
}

fn fragment_with(
    nodes: &[(&str, &Profile)],
    edges: &[(&str, &str, &str, &Annotation)],
) -> FragmentSpec {
    let mut fragment = FragmentSpec::default();
    for (symbol, profile) in nodes {
        profile.place(&mut fragment, symbol);
    }
    for (symbol, source, target, annotation) in edges {
        annotation.connect(&mut fragment, symbol, source, target);
    }
    fragment
}

fn production(
    id: &str,
    left: FragmentSpec,
    interface_nodes: &[&str],
    interface_edges: &[&str],
    right: FragmentSpec,
) -> ProductionSpec {
    ProductionSpec {
        id: id.to_owned(),
        left,
        interface_nodes: names(interface_nodes),
        interface_edges: names(interface_edges),
        right,
    }
}

/// The rewrite grammar of a fixture, derived from its own node and edge
/// kinds. For each kind of node: an identity (`keep`), a fresh node (`spawn`),
/// and a deletion (`drop`, which dangles unless the node is isolated). For
/// each kind of edge: removal (`cut`), an accepting edge added between nodes of
/// its end kinds (`mend`), a rejecting one (`block`), an identity preserving
/// the edge (`hold`), a fresh node and edge added beside the preserved edge
/// (`branch`), and, off self-loops, a stage inserted on it (`stage`), a staged
/// node removed with both its phases (`unstage`), and the target deleted with
/// the edge (`drop-target`); on a self-loop, the node deleted with its loop
/// (`drop-loop`). Plus the empty identity (`nothing`), and productions that
/// only an extension makes admissible: an edge whose contract it registers
/// (`mend-late`), an edge carrying a tag it adds (`mend-extra`), and a node of
/// a type it adds (`spawn-late`).
pub fn derived_grammar(
    definition: &DefinitionSpec,
    validators: &BTreeMap<String, Validator>,
) -> Vec<ProductionSpec> {
    let whole = definition.fragment();
    let reject = definition
        .contracts
        .iter()
        .find(|contract| validators.get(&contract.id) == Some(&Validator::RejectAll))
        .map_or("late_deny", |contract| contract.id.as_str());
    let empty = FragmentSpec::default;
    let mut grammar = vec![production("nothing", empty(), &[], &[], empty())];
    let mut kinds = BTreeSet::new();
    for id in &definition.nodes {
        let profile = profile_in(&whole, id);
        if !kinds.insert(profile.clone()) {
            continue;
        }
        let one = fragment_with(&[("X", &profile)], &[]);
        grammar.push(production(
            &format!("keep:{id}"),
            one.clone(),
            &["X"],
            &[],
            one.clone(),
        ));
        grammar.push(production(
            &format!("spawn:{id}"),
            empty(),
            &[],
            &[],
            one.clone(),
        ));
        grammar.push(production(&format!("drop:{id}"), one, &[], &[], empty()));
        if grammar.iter().all(|p| p.id != "spawn-late") {
            let late = fragment_with(&[("Z", &profile.with_type(LATE_NODE_TYPE))], &[]);
            grammar.push(production("spawn-late", empty(), &[], &[], late));
        }
    }
    let mut kinds = BTreeSet::new();
    for edge in &definition.edges {
        let source = profile_in(&whole, &edge.source);
        let target = profile_in(&whole, &edge.target);
        let annotation = annotation_in(&whole, &edge.id);
        let looped = edge.source == edge.target;
        if !kinds.insert((source.clone(), target.clone(), annotation.clone(), looped)) {
            continue;
        }
        let id = &edge.id;
        let (ends, y): (Vec<(&str, &Profile)>, &str) = if looped {
            (vec![("X", &source)], "X")
        } else {
            (vec![("X", &source), ("Y", &target)], "Y")
        };
        let interface: Vec<&str> = ends.iter().map(|(symbol, _)| *symbol).collect();
        let bare = fragment_with(&ends, &[]);
        let joined = fragment_with(&ends, &[("E", "X", y, &annotation)]);
        let blocked = fragment_with(&ends, &[("B", "X", y, &annotation.with_contract(reject))]);
        grammar.push(production(
            &format!("cut:{id}"),
            joined.clone(),
            &interface,
            &[],
            bare.clone(),
        ));
        grammar.push(production(
            &format!("mend:{id}"),
            bare.clone(),
            &interface,
            &[],
            joined.clone(),
        ));
        grammar.push(production(
            &format!("block:{id}"),
            bare.clone(),
            &interface,
            &[],
            blocked,
        ));
        let held: Vec<&str> = vec!["E"];
        grammar.push(production(
            &format!("hold:{id}"),
            joined.clone(),
            &interface,
            &held,
            joined.clone(),
        ));
        let branched = fragment_with(
            &[("X", &source), ("Y", &target), ("Z", &target)],
            &[("E", "X", y, &annotation), ("F", "X", "Z", &annotation)],
        );
        let branched = if looped {
            fragment_with(
                &[("X", &source), ("Z", &target)],
                &[("E", "X", "X", &annotation), ("F", "X", "Z", &annotation)],
            )
        } else {
            branched
        };
        grammar.push(production(
            &format!("branch:{id}"),
            joined.clone(),
            &interface,
            &held,
            branched,
        ));
        if grammar.iter().all(|p| p.id != "mend-late") {
            let late = fragment_with(&ends, &[("L", "X", y, &annotation.with_contract("late"))]);
            grammar.push(production("mend-late", bare.clone(), &interface, &[], late));
            let extra = fragment_with(&ends, &[("T", "X", y, &annotation.with_tag(LATE_TAG))]);
            grammar.push(production("mend-extra", bare, &interface, &[], extra));
        }
        if looped {
            grammar.push(production(
                &format!("drop-loop:{id}"),
                joined,
                &[],
                &[],
                empty(),
            ));
        } else {
            let staged = fragment_with(
                &[("X", &source), ("Y", &target), ("Z", &target)],
                &[("F", "X", "Z", &annotation), ("G", "Z", "Y", &annotation)],
            );
            grammar.push(production(
                &format!("stage:{id}"),
                joined.clone(),
                &["X", "Y"],
                &[],
                staged.clone(),
            ));
            grammar.push(production(
                &format!("unstage:{id}"),
                staged,
                &["X", "Y"],
                &[],
                joined.clone(),
            ));
            grammar.push(production(
                &format!("drop-target:{id}"),
                joined,
                &["X"],
                &[],
                fragment_with(&[("X", &source)], &[]),
            ));
        }
    }
    grammar
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
/// prefix: every way a request can fail, evidence missing, mismatched, and
/// complete, a stage inserted and removed with both phases of its node,
/// a route removed at an `All` receiver, extensions that enable a production,
/// and stale and current plans.
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
    let mend = |edge: &str| MatchSpec {
        nodes: bind(&[("X", "a"), ("Y", "b")]),
        fresh_edges: bind(&[("E", edge)]),
        ..MatchSpec::default()
    };
    let swapped = offer_instead(&[(b"\x02A", b"no"), (b"no", b"\x02A")]);

    // Evidence: a changed holder's waiting work is rechecked against its bytes.
    run.reject(
        "missing evidence",
        rewrite("mend:ab", mend("ab~1"), BTreeMap::new()),
    );
    run.reject(
        "mismatched evidence",
        rewrite("mend:ab", mend("ab~1"), swapped),
    );
    run.accept(
        "an accepting edge added from a holder with waiting work",
        rewrite("mend:ab", mend("ab~1"), run.known_evidence()),
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

    // Requests that fail.
    let evidence = run.known_evidence();
    run.reject(
        "a fresh edge reusing a current identity",
        rewrite("mend:ab", mend("ab"), evidence.clone()),
    );
    let cut = |nodes: &[(&str, &str)], edges: &[(&str, &str)]| MatchSpec {
        nodes: bind(nodes),
        edges: bind(edges),
        ..MatchSpec::default()
    };
    run.reject(
        "a match missing a symbol",
        rewrite(
            "cut:ab",
            cut(&[("X", "a"), ("Y", "b")], &[]),
            evidence.clone(),
        ),
    );
    run.reject(
        "a match binding a symbol the production lacks",
        rewrite(
            "cut:ab",
            cut(&[("X", "a"), ("Y", "b"), ("W", "x")], &[("E", "ab")]),
            evidence.clone(),
        ),
    );
    let stage = |fresh: &[(&str, &str)]| MatchSpec {
        nodes: bind(&[("X", "a"), ("Y", "j")]),
        edges: bind(&[("E", "aj1")]),
        fresh_nodes: bind(&[("Z", "z~1")]),
        fresh_edges: bind(fresh),
    };
    run.reject(
        "a non-injective allocation",
        rewrite(
            "stage:aj1",
            stage(&[("F", "f~1"), ("G", "f~1")]),
            evidence.clone(),
        ),
    );
    run.reject(
        "an edge matched to one of another kind",
        rewrite(
            "cut:ab",
            cut(&[("X", "a"), ("Y", "b")], &[("E", "ab_all")]),
            evidence.clone(),
        ),
    );
    run.reject(
        "a node matched to one of another kind",
        rewrite("keep:a", cut(&[("X", "b")], &[]), evidence.clone()),
    );
    run.reject(
        "a deletion leaving dangling edges",
        rewrite("drop:b", cut(&[("X", "b")], &[]), evidence.clone()),
    );
    run.reject(
        "a production outside the grammar",
        rewrite("nope", MatchSpec::default(), evidence.clone()),
    );

    // Identity rewrites.
    run.accept(
        "the empty identity rewrite",
        rewrite("nothing", MatchSpec::default(), evidence.clone()),
    );
    run.accept(
        "an identity rewrite of a matched node",
        rewrite("keep:a", cut(&[("X", "a")], &[]), evidence.clone()),
    );

    // A stage inserted on the `All` receiver's route, then removed with its node.
    run.accept(
        "a stage inserted on a route into an All receiver",
        rewrite(
            "stage:aj1",
            stage(&[("F", "f~1"), ("G", "g~1")]),
            evidence.clone(),
        ),
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
    run.accept(
        "the staged node removed with both of its phases",
        rewrite(
            "unstage:aj1",
            MatchSpec {
                nodes: bind(&[("X", "a"), ("Y", "j"), ("Z", "z~1")]),
                edges: bind(&[("F", "f~1"), ("G", "g~1")]),
                fresh_nodes: Vec::new(),
                fresh_edges: bind(&[("E", "aj1~1")]),
            },
            run.known_evidence(),
        ),
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
        "a fresh node reusing a removed identity",
        rewrite(
            "stage:aj1",
            MatchSpec {
                nodes: bind(&[("X", "a"), ("Y", "j")]),
                edges: bind(&[("E", "aj1~1")]),
                fresh_nodes: bind(&[("Z", "z~1")]),
                fresh_edges: bind(&[("F", "f~2"), ("G", "g~2")]),
            },
            run.known_evidence(),
        ),
    );
    run.reject(
        "a fresh edge reusing a removed identity",
        rewrite("mend:ab", mend("f~1"), run.known_evidence()),
    );

    // Extensions, and a production they enable.
    let late = MatchSpec {
        nodes: bind(&[("X", "a"), ("Y", "b")]),
        fresh_edges: bind(&[("L", "late~1")]),
        ..MatchSpec::default()
    };
    run.reject(
        "a production naming an unregistered contract",
        rewrite("mend-late", late.clone(), run.known_evidence()),
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
        "a production the extension enabled",
        rewrite("mend-late", late, run.known_evidence()),
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
        let evidence = run.known_evidence();
        rewrite(
            "mend:aj1",
            MatchSpec {
                nodes: bind(&[("X", "a"), ("Y", "j")]),
                fresh_edges: bind(&[("E", "aj~2")]),
                ..MatchSpec::default()
            },
            evidence,
        )
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
