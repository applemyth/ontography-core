//! The trace format of `formal/TRACE_FORMAT.md`, the kernel values a trace
//! denotes, and the canonical encoding of the kernel's definition and state.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::Arc;

use ontography::{
    Activation, ActivationId, Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule,
    Checkpoint, ContentDigest, Contract, ContractViolation, DefinitionError, DefinitionFingerprint,
    DefinitionId, Edge, EdgeDefinition, Graph, IngressMode, Kernel, Node, NodeDefinition,
    PackageId, PackageRecord, PackageStatus, RetirementReason, RewriteFragment, RewriteGrammar,
    RewriteMatch, RewriteProduction, RewriteRequest, RootRule, Schema, Trigger,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

pub const FORMAT: &str = "ontography-lean-trace/2";

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Trace {
    pub format: String,
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub known_disagreement: Option<KnownDisagreement>,
    /// The validator each contract identity names, for the whole run.
    pub validators: BTreeMap<String, Validator>,
    /// Payload hex to `ContentDigest::compute` of those bytes, in hex.
    pub digests: BTreeMap<String, String>,
    pub grammar: Vec<ProductionSpec>,
    pub definition: DefinitionSpec,
    pub ops: Vec<TraceOp>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct KnownDisagreement {
    /// The first step at which the kernel and the model disagree.
    pub step: usize,
    pub summary: String,
}

/// The fixed validator menu both implementations provide.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Validator {
    AcceptAll,
    RejectAll,
    /// Accepts exactly the bytes given in hex.
    BytesEqual(String),
    /// Accepts a nonempty payload whose first byte is even.
    FirstByteEven,
}

impl Validator {
    pub fn accepts(&self, payload: &[u8]) -> bool {
        match self {
            Self::AcceptAll => true,
            Self::RejectAll => false,
            Self::BytesEqual(expected) => payload == unhex(expected).as_slice(),
            Self::FirstByteEven => payload.first().is_some_and(|byte| byte % 2 == 0),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SchemaSpec {
    pub node_types: Vec<String>,
    pub object_types: Vec<String>,
    pub tags: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ContractSpec {
    pub id: String,
    pub object_type: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionSpec {
    pub schema: SchemaSpec,
    pub contracts: Vec<ContractSpec>,
    pub nodes: Vec<String>,
    pub edges: Vec<EdgeSpec>,
    pub node_definitions: Vec<NodeSpec>,
    pub edge_definitions: Vec<EdgeDefinitionSpec>,
    pub transitions: Vec<TransitionSpec>,
    pub roots: Vec<RootSpec>,
}

/// The graph and annotations of a definition or a production side.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FragmentSpec {
    pub nodes: Vec<String>,
    pub edges: Vec<EdgeSpec>,
    pub node_definitions: Vec<NodeSpec>,
    pub edge_definitions: Vec<EdgeDefinitionSpec>,
    pub transitions: Vec<TransitionSpec>,
    pub roots: Vec<RootSpec>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EdgeSpec {
    pub id: String,
    pub source: String,
    pub target: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NodeSpec {
    pub node: String,
    pub types: Vec<String>,
    pub result_contract: String,
    pub ingress: Ingress,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Ingress {
    Any,
    All,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EdgeDefinitionSpec {
    pub edge: String,
    pub types: Vec<String>,
    pub source_requirements: Vec<String>,
    pub target_requirements: Vec<String>,
    pub package_contract: String,
    pub tags: Vec<String>,
    pub authority_match: Match,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Match {
    AnyOf,
    AllOf,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TransitionSpec {
    pub node: String,
    pub source: Vec<String>,
    pub target: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RootSpec {
    pub node: String,
    pub ceiling: Vec<String>,
}

/// A production `L ← K → R`, with `K` given by its node and edge symbols.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionSpec {
    pub id: String,
    pub left: FragmentSpec,
    pub interface_nodes: Vec<String>,
    pub interface_edges: Vec<String>,
    pub right: FragmentSpec,
}

/// Symbol bindings: `L`'s symbols to current identities, `R ∖ K`'s to fresh ones.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MatchSpec {
    pub nodes: Vec<(String, String)>,
    pub edges: Vec<(String, String)>,
    pub fresh_nodes: Vec<(String, String)>,
    pub fresh_edges: Vec<(String, String)>,
}

/// A package identity `[producer, output]`: the producer's `u128` in decimal
/// and the output ordinal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct PackageRef(pub String, pub u64);

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum TraceOp {
    Activate {
        id: String,
        trigger: TriggerSpec,
        result: String,
        emissions: Vec<EmissionSpec>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expect: Option<Expectation>,
    },
    Transfer {
        package: PackageRef,
        edge: String,
        payload: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expect: Option<Expectation>,
    },
    Retire {
        package: PackageRef,
        /// Required, and `null` for none.
        #[serde(deserialize_with = "Option::deserialize")]
        evidence: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expect: Option<Expectation>,
    },
    Rewrite {
        production: String,
        #[serde(rename = "match")]
        matching: MatchSpec,
        /// Digest hex to the payload hex offered for that commitment.
        evidence: BTreeMap<String, String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expect: Option<Expectation>,
    },
    Extend {
        schema: SchemaSpec,
        contracts: Vec<ContractSpec>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expect: Option<Expectation>,
    },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TriggerSpec {
    Orig {
        node: String,
        authority: Vec<String>,
    },
    Pkgs(Vec<PackageRef>),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EmissionSpec {
    pub destination: Destination,
    pub authority: AuthoritySpec,
    pub payload: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Destination {
    Delivered(String),
    Outbound(String),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthoritySpec {
    Carry,
    Transition(Vec<String>),
}

/// The kernel's outcome of one operation, and the canonical state after it.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Expectation {
    pub accepted: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub state: Option<Value>,
}

impl TraceOp {
    pub fn expect(&self) -> Option<&Expectation> {
        match self {
            Self::Activate { expect, .. }
            | Self::Transfer { expect, .. }
            | Self::Retire { expect, .. }
            | Self::Rewrite { expect, .. }
            | Self::Extend { expect, .. } => expect.as_ref(),
        }
    }

    pub fn expect_mut(&mut self) -> &mut Option<Expectation> {
        match self {
            Self::Activate { expect, .. }
            | Self::Transfer { expect, .. }
            | Self::Retire { expect, .. }
            | Self::Rewrite { expect, .. }
            | Self::Extend { expect, .. } => expect,
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Self::Activate { .. } => "activate",
            Self::Transfer { .. } => "transfer",
            Self::Retire { .. } => "retire",
            Self::Rewrite { .. } => "rewrite",
            Self::Extend { .. } => "extend",
        }
    }

    /// The payloads the operation commits to, checks against a commitment, or
    /// offers as evidence.
    pub fn payloads(&self) -> Vec<&str> {
        match self {
            Self::Activate { emissions, .. } => emissions
                .iter()
                .map(|emission| emission.payload.as_str())
                .collect(),
            Self::Transfer { payload, .. } => vec![payload.as_str()],
            Self::Rewrite { evidence, .. } => evidence.values().map(String::as_str).collect(),
            Self::Retire { .. } | Self::Extend { .. } => Vec::new(),
        }
    }
}

impl DefinitionSpec {
    pub fn fragment(&self) -> FragmentSpec {
        FragmentSpec {
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            node_definitions: self.node_definitions.clone(),
            edge_definitions: self.edge_definitions.clone(),
            transitions: self.transitions.clone(),
            roots: self.roots.clone(),
        }
    }
}

// Identities and bytes.

pub fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing to a string cannot fail");
    }
    text
}

pub fn unhex(text: &str) -> Vec<u8> {
    assert!(
        text.len().is_multiple_of(2) && text.is_ascii(),
        "{text:?} is not a hex byte string"
    );
    (0..text.len())
        .step_by(2)
        .map(|at| {
            u8::from_str_radix(&text[at..at + 2], 16)
                .unwrap_or_else(|_| panic!("{text:?} is not a hex byte string"))
        })
        .collect()
}

pub fn parse_digest(text: &str) -> ContentDigest {
    let bytes: [u8; 32] = unhex(text)
        .try_into()
        .unwrap_or_else(|_| panic!("{text:?} is not a 32-byte digest"));
    ContentDigest::from_bytes(bytes)
}

pub fn activation_text(id: ActivationId) -> String {
    id.as_u128().to_string()
}

pub fn parse_activation(text: &str) -> ActivationId {
    ActivationId::from_u128(
        text.parse()
            .unwrap_or_else(|_| panic!("activation id {text:?} is not a decimal u128")),
    )
}

pub fn package_ref(id: PackageId) -> PackageRef {
    PackageRef(
        activation_text(id.producer()),
        u64::try_from(id.output()).expect("output ordinals fit in u64"),
    )
}

pub fn parse_package(reference: &PackageRef) -> PackageId {
    PackageId::from_parts(parse_activation(&reference.0), u128::from(reference.1))
}

// The kernel values a trace denotes.

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).expect("authority tags are nonempty")
}

pub fn authority(tags: &[String]) -> Authority {
    Authority::new(tags.iter().map(|id| tag(id)))
}

/// One kernel contract per identity and object type for the whole run, so an
/// identity keeps its validator, which extensions and rewrites require.
pub struct Registry {
    validators: BTreeMap<String, Validator>,
    contracts: BTreeMap<(String, String), Contract>,
}

impl Registry {
    pub fn new(validators: BTreeMap<String, Validator>) -> Self {
        Self {
            validators,
            contracts: BTreeMap::new(),
        }
    }

    pub fn validators(&self) -> &BTreeMap<String, Validator> {
        &self.validators
    }

    pub fn contract(&mut self, spec: &ContractSpec) -> Contract {
        let validator = self
            .validators
            .get(&spec.id)
            .unwrap_or_else(|| panic!("contract {} has no validator", spec.id))
            .clone();
        self.contracts
            .entry((spec.id.clone(), spec.object_type.clone()))
            .or_insert_with(|| {
                Contract::new(
                    spec.id.as_str(),
                    spec.object_type.as_str(),
                    move |payload| {
                        if validator.accepts(payload) {
                            Ok(())
                        } else {
                            Err(ContractViolation::new("the trace validator rejects it"))
                        }
                    },
                )
                .expect("contract identities are nonempty")
            })
            .clone()
    }
}

fn schema(spec: &SchemaSpec) -> Result<Schema, DefinitionError> {
    Schema::new(
        spec.node_types.iter().map(String::as_str),
        spec.object_types.iter().map(String::as_str),
        spec.tags.iter().map(|id| tag(id)),
    )
}

fn node_definition(spec: &NodeSpec) -> Result<NodeDefinition, DefinitionError> {
    Ok(NodeDefinition::new(
        spec.node.as_str(),
        spec.types.iter().map(String::as_str),
        spec.result_contract.as_str(),
    )?
    .with_ingress_mode(match spec.ingress {
        Ingress::Any => IngressMode::Any,
        Ingress::All => IngressMode::All,
    }))
}

fn edge_definition(spec: &EdgeDefinitionSpec) -> Result<EdgeDefinition, DefinitionError> {
    Ok(EdgeDefinition::new(
        spec.edge.as_str(),
        spec.types.iter().map(String::as_str),
        spec.source_requirements.iter().map(String::as_str),
        spec.target_requirements.iter().map(String::as_str),
        spec.package_contract.as_str(),
        spec.tags.iter().map(|id| tag(id)),
    )?
    .with_authority_match(match spec.authority_match {
        Match::AnyOf => AuthorityMatch::AnyOf,
        Match::AllOf => AuthorityMatch::AllOf,
    }))
}

/// A fragment's topology and annotations as kernel values.
#[allow(clippy::type_complexity)]
fn parts(
    spec: &FragmentSpec,
) -> Result<
    (
        Vec<Node>,
        Vec<Edge>,
        Vec<NodeDefinition>,
        Vec<EdgeDefinition>,
        Vec<AuthorityTransitionRule>,
        Vec<RootRule>,
    ),
    DefinitionError,
> {
    Ok((
        spec.nodes
            .iter()
            .map(|id| Node::new(id.as_str()))
            .collect::<Result<_, _>>()?,
        spec.edges
            .iter()
            .map(|edge| Edge::new(edge.id.as_str(), edge.source.as_str(), edge.target.as_str()))
            .collect::<Result<_, _>>()?,
        spec.node_definitions
            .iter()
            .map(node_definition)
            .collect::<Result<_, _>>()?,
        spec.edge_definitions
            .iter()
            .map(edge_definition)
            .collect::<Result<_, _>>()?,
        spec.transitions
            .iter()
            .map(|rule| {
                AuthorityTransitionRule::new(
                    rule.node.as_str(),
                    authority(&rule.source),
                    authority(&rule.target),
                )
            })
            .collect::<Result<_, _>>()?,
        spec.roots
            .iter()
            .map(|root| RootRule::new(root.node.as_str(), authority(&root.ceiling)))
            .collect::<Result<_, _>>()?,
    ))
}

/// Admits a trace definition, with each contract drawn from the registry.
pub fn admit(
    definition: &DefinitionSpec,
    registry: &mut Registry,
) -> Result<Kernel, DefinitionError> {
    let (nodes, edges, node_definitions, edge_definitions, transitions, roots) =
        parts(&definition.fragment())?;
    let contracts: Vec<Contract> = definition
        .contracts
        .iter()
        .map(|spec| registry.contract(spec))
        .collect();
    Kernel::admit(
        DefinitionId::new("lean-oracle").unwrap(),
        schema(&definition.schema)?,
        Graph::new(nodes, edges)?,
        contracts,
        node_definitions,
        edge_definitions,
        transitions,
        roots,
    )
}

/// The replacement an extension proposes: the current graph and annotations
/// under a new schema and contract registry.
pub fn extended(
    current: &Kernel,
    schema_spec: &SchemaSpec,
    contracts: &[ContractSpec],
    registry: &mut Registry,
) -> Result<Kernel, DefinitionError> {
    let contracts: Vec<Contract> = contracts
        .iter()
        .map(|spec| registry.contract(spec))
        .collect();
    Kernel::admit(
        current.id().clone(),
        schema(schema_spec)?,
        current.graph().clone(),
        contracts,
        current.node_definitions().iter().cloned(),
        current.edge_definitions().iter().cloned(),
        current.authority_transitions().iter().cloned(),
        current.roots().iter().cloned(),
    )
}

fn fragment(spec: &FragmentSpec) -> RewriteFragment {
    let (nodes, edges, node_definitions, edge_definitions, transitions, roots) =
        parts(spec).expect("production fragments are well formed");
    RewriteFragment::new(
        nodes,
        edges,
        node_definitions,
        edge_definitions,
        transitions,
        roots,
    )
}

pub fn grammar(specs: &[ProductionSpec]) -> RewriteGrammar {
    let names = |symbols: &[String]| symbols.iter().map(|id| Arc::from(id.as_str())).collect();
    RewriteGrammar::new(specs.iter().map(|spec| {
        RewriteProduction::new(
            spec.id.as_str(),
            fragment(&spec.left),
            names(&spec.interface_nodes),
            names(&spec.interface_edges),
            fragment(&spec.right),
        )
        .unwrap_or_else(|error| panic!("production {} is ill-shaped: {error}", spec.id))
    }))
    .expect("production identities are distinct")
}

pub fn request(production: &str, matching: &MatchSpec) -> RewriteRequest {
    let map = |pairs: &[(String, String)]| -> BTreeMap<Arc<str>, Arc<str>> {
        let map: BTreeMap<Arc<str>, Arc<str>> = pairs
            .iter()
            .map(|(symbol, id)| (Arc::from(symbol.as_str()), Arc::from(id.as_str())))
            .collect();
        assert_eq!(
            map.len(),
            pairs.len(),
            "a binding names each symbol once: {pairs:?}"
        );
        map
    };
    RewriteRequest::new(
        production,
        RewriteMatch::new(
            map(&matching.nodes),
            map(&matching.edges),
            map(&matching.fresh_nodes),
            map(&matching.fresh_edges),
        ),
    )
}

// The canonical state of `formal/TRACE_FORMAT.md`.

fn package_json(id: PackageId) -> Value {
    json!([
        activation_text(id.producer()),
        u64::try_from(id.output()).expect("output ordinals fit in u64")
    ])
}

fn strings<'a>(items: impl IntoIterator<Item = &'a str>) -> Vec<String> {
    let set: BTreeSet<&str> = items.into_iter().collect();
    set.into_iter().map(str::to_owned).collect()
}

fn tag_ids(authority: &Authority) -> Vec<String> {
    strings(authority.tags().map(AuthorityTag::id))
}

fn reason_name(reason: RetirementReason) -> &'static str {
    match reason {
        RetirementReason::HolderRemoved => "holder_removed",
        RetirementReason::NoAcceptingEdge => "no_accepting_edge",
        RetirementReason::RouteRemoved => "route_removed",
        RetirementReason::Explicit => "explicit",
    }
}

fn activation_json(id: ActivationId, activation: &Activation) -> Value {
    let trigger = match activation.trigger() {
        Trigger::Orig { node_id, authority } => {
            json!({"orig": {"node": &**node_id, "authority": tag_ids(authority)}})
        }
        Trigger::Pkgs { package_ids } => json!({
            "pkgs": package_ids.iter().map(|id| package_json(*id)).collect::<Vec<_>>()
        }),
    };
    let outputs = activation
        .package_outputs()
        .iter()
        .map(|(package, output)| {
            json!({
                "package": package_json(*package),
                "edge": output.edge_id(),
                "object_type": output.object_type(),
                "authority": tag_ids(output.authority()),
                "digest": output.content_digest().to_string(),
            })
        });
    json!({
        "id": activation_text(id),
        "node": activation.node_id(),
        "trigger": trigger,
        "result": hex(activation.result()),
        "outputs": outputs.collect::<Vec<_>>(),
    })
}

fn record_json(id: PackageId, record: &PackageRecord) -> Value {
    let status = match record.status() {
        PackageStatus::Live => json!("live"),
        PackageStatus::Consumed(consumer) => json!({"consumed": activation_text(*consumer)}),
        PackageStatus::Retired(retirement) => json!({"retired": {
            "reason": reason_name(retirement.reason()),
            "revision": retirement.revision(),
            "evidence": retirement.evidence().map(activation_text),
        }}),
    };
    json!({
        "id": package_json(id),
        "object_type": record.object_type(),
        "authority": tag_ids(record.authority()),
        "digest": record.content_digest().to_string(),
        "producer_node": record.producer_node(),
        "delivery": record.delivery().map(|delivery| json!({
            "edge": delivery.edge_id(),
            "receiver": delivery.receiver(),
        })),
        "status": status,
    })
}

/// A set of structured entries, each with its sort key: sorted by key,
/// lexicographic on lists of identifiers, with repeated entries removed.
fn entries(mut items: Vec<(Vec<Vec<String>>, Value)>) -> Value {
    items.sort_by(|left, right| left.0.cmp(&right.0));
    items.dedup();
    Value::Array(items.into_iter().map(|(_, value)| value).collect())
}

fn key(id: &str) -> Vec<Vec<String>> {
    vec![vec![id.to_owned()]]
}

fn arc_strings(items: &BTreeSet<Arc<str>>) -> Vec<String> {
    strings(items.iter().map(|item| &**item))
}

/// The current definition, component by component, each as a canonical set.
fn definition_json(kernel: &Kernel) -> Value {
    let schema = kernel.schema();
    let contracts = kernel
        .contracts()
        .iter()
        .map(|c| {
            (
                key(c.id()),
                json!({"id": c.id(), "object_type": c.object_type()}),
            )
        })
        .collect();
    let edges = kernel
        .graph()
        .edges()
        .iter()
        .map(|e| {
            let value = json!({"id": e.id(), "source": e.source(), "target": e.target()});
            (key(e.id()), value)
        })
        .collect();
    let node_definitions = kernel
        .node_definitions()
        .iter()
        .map(|d| {
            let value = json!({
                "node": d.node_id(),
                "types": arc_strings(d.types()),
                "result_contract": d.result_contract(),
                "ingress": match d.ingress_mode() {
                    IngressMode::Any => "any",
                    IngressMode::All => "all",
                },
            });
            (key(d.node_id()), value)
        })
        .collect();
    let edge_definitions = kernel
        .edge_definitions()
        .iter()
        .map(|d| {
            let value = json!({
                "edge": d.edge_id(),
                "types": arc_strings(d.types()),
                "source_requirements": arc_strings(d.source_requirements()),
                "target_requirements": arc_strings(d.target_requirements()),
                "package_contract": d.package_contract(),
                "tags": strings(d.authority_tags().iter().map(AuthorityTag::id)),
                "authority_match": match d.authority_match() {
                    AuthorityMatch::AnyOf => "any_of",
                    AuthorityMatch::AllOf => "all_of",
                },
            });
            (key(d.edge_id()), value)
        })
        .collect();
    let transitions = kernel
        .authority_transitions()
        .iter()
        .map(|rule| {
            let (source, target) = (tag_ids(rule.from()), tag_ids(rule.to()));
            let value = json!({"node": rule.node_id(), "source": source, "target": target});
            (vec![vec![rule.node_id().to_owned()], source, target], value)
        })
        .collect();
    let roots = kernel
        .roots()
        .iter()
        .map(|root| {
            let value = json!({"node": root.node_id(), "ceiling": tag_ids(root.ceiling())});
            (key(root.node_id()), value)
        })
        .collect();
    json!({
        "schema": {
            "node_types": strings(schema.node_types()),
            "object_types": strings(schema.object_types()),
            "tags": strings(schema.authority_tags().map(AuthorityTag::id)),
        },
        "contracts": entries(contracts),
        "nodes": strings(kernel.graph().nodes().iter().map(Node::id)),
        "edges": entries(edges),
        "node_definitions": entries(node_definitions),
        "edge_definitions": entries(edge_definitions),
        "transitions": entries(transitions),
        "roots": entries(roots),
    })
}

/// The canonical state after one op. Its entries are shared with the states
/// before it, so recording a state costs only the entries that changed.
pub struct Snapshot {
    definition: Arc<Value>,
    activations: Vec<Arc<Value>>,
    packages: Vec<Arc<Value>>,
    /// The remaining fields: lifetime identities, changes, and the revision.
    rest: serde_json::Map<String, Value>,
}

impl Snapshot {
    pub fn to_value(&self) -> Value {
        let entries = |values: &[Arc<Value>]| {
            Value::Array(values.iter().map(|value| Value::clone(value)).collect())
        };
        let mut state = self.rest.clone();
        state.insert("definition".to_owned(), Value::clone(&self.definition));
        state.insert("activations".to_owned(), entries(&self.activations));
        state.insert("packages".to_owned(), entries(&self.packages));
        Value::Object(state)
    }

    /// Whether the model's canonical state equals this one.
    pub fn matches(&self, model: &Value) -> bool {
        let entries = |kernel: &[Arc<Value>], model: Option<&Value>| {
            model.and_then(Value::as_array).is_some_and(|model| {
                model.len() == kernel.len()
                    && kernel
                        .iter()
                        .zip(model)
                        .all(|(kernel, model)| **kernel == *model)
            })
        };
        model.as_object().is_some_and(|model| {
            model.len() == self.rest.len() + 3
                && model.get("definition") == Some(&*self.definition)
                && entries(&self.activations, model.get("activations"))
                && entries(&self.packages, model.get("packages"))
                && self
                    .rest
                    .iter()
                    .all(|(key, value)| model.get(key) == Some(value))
        })
    }
}

/// Encodes a kernel and its state canonically, reusing the encoding of the
/// definition while it is unchanged and of every entry whose record is.
#[derive(Default)]
pub struct Canonical {
    definition: Option<(DefinitionFingerprint, Arc<Value>)>,
    activations: BTreeMap<ActivationId, (Activation, Arc<Value>)>,
    packages: BTreeMap<PackageId, (PackageRecord, Arc<Value>)>,
}

impl Canonical {
    pub fn encode(&mut self, kernel: &Kernel, checkpoint: &Checkpoint) -> Snapshot {
        let definition = match &self.definition {
            Some((fingerprint, value)) if fingerprint == kernel.fingerprint() => Arc::clone(value),
            _ => {
                let value = Arc::new(definition_json(kernel));
                self.definition = Some((*kernel.fingerprint(), Arc::clone(&value)));
                value
            }
        };
        let mut activations = Vec::with_capacity(checkpoint.activations.len());
        for (id, activation) in &checkpoint.activations {
            match self.activations.get(id) {
                Some((cached, value)) if cached == activation => {
                    activations.push(Arc::clone(value));
                }
                _ => {
                    let value = Arc::new(activation_json(*id, activation));
                    self.activations
                        .insert(*id, (activation.clone(), Arc::clone(&value)));
                    activations.push(value);
                }
            }
        }
        let mut packages = Vec::with_capacity(checkpoint.packages.len());
        for (id, record) in &checkpoint.packages {
            match self.packages.get(id) {
                Some((cached, value)) if cached == record => packages.push(Arc::clone(value)),
                _ => {
                    let value = Arc::new(record_json(*id, record));
                    self.packages
                        .insert(*id, (record.clone(), Arc::clone(&value)));
                    packages.push(value);
                }
            }
        }
        let Value::Object(rest) = json!({
            "used_nodes": strings(checkpoint.used_node_ids.iter().map(|id| &**id)),
            "used_edges": strings(checkpoint.used_edge_ids.iter().map(|id| &**id)),
            "definition_changes": checkpoint.definition_changes,
            "revision": checkpoint.revision,
        }) else {
            unreachable!("a JSON object literal is an object");
        };
        Snapshot {
            definition,
            activations,
            packages,
            rest,
        }
    }
}
