//! M2, the kernel against its Lean model: seeded random operation sequences
//! drive the in-memory kernel over a few fixed definitions, and each run is
//! recorded as a trace (`formal/TRACE_FORMAT.md`) holding the kernel's outcome
//! and canonical state after every operation. The Lean oracle
//! (`formal/Oracle`) replays the trace with the model's `step`; acceptance and
//! the canonical state must agree at every step. Error variants are not
//! compared, since the model's rules carry no rejection reason.
//!
//! Every run starts with its definition's required prefix. The prefix builds
//! the rare cases by construction (every root failure, every join shape,
//! transitions, edge matching, contract rejection, self-loops, parallel edges,
//! and each way a transfer or retirement can fail) and checks the kernel's
//! outcome for each before random exploration begins. Random choices index
//! packages in birth order, so a seed fixes the operation sequence even though
//! the kernel draws activation identities at random.
//!
//! The oracle is the executable named by `ONTOGRAPHY_LEAN_ORACLE`, by default
//! `formal/.lake/build/bin/oracle` (`cd formal && lake build oracle`). Without
//! it the tests skip loudly, or fail when `ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1`.
//! `ONTOGRAPHY_LEAN_ORACLE_SEEDS` adds seeds, as in `7,40..60`. A disagreement
//! writes its trace to `target/lean-oracle/<seed>.json`. The hand-written
//! regression traces in `tests/lean_traces/` replay on every run, and
//! `tests/lean_traces/disagreements/` keeps minimized known disagreements.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;

use ontography::{
    Activation, ActivationId, ActivationProposal, Authority, AuthorityMatch, AuthorityTag,
    AuthorityTransitionRule, Checkpoint, ContentDigest, Contract, ContractViolation, DefinitionId,
    Edge, EdgeDefinition, Emission, Graph, IngressMode, Kernel, Node, NodeDefinition,
    OutputAuthority, PackageId, PackageRecord, PackageStatus, Payload, RetirementReason, RootRule,
    Schema, State, Trigger,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

const FORMAT: &str = "ontography-lean-trace/1";

/// The fixed seeds; `ONTOGRAPHY_LEAN_ORACLE_SEEDS` adds more.
const SEEDS: std::ops::RangeInclusive<u64> = 1..=18;

/// Random operations after each run's required prefix.
const RANDOM_STEPS: usize = 150;

/// At most this many differing state paths are reported for one step.
const DIFFERENCE_LIMIT: usize = 16;

// The trace format of `formal/TRACE_FORMAT.md`.

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Trace {
    format: String,
    name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    seed: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    known_disagreement: Option<KnownDisagreement>,
    definition: DefinitionSpec,
    /// Payload hex to `ContentDigest::compute` of those bytes, in hex.
    digests: BTreeMap<String, String>,
    ops: Vec<TraceOp>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct KnownDisagreement {
    /// The first step at which the kernel and the model disagree.
    step: usize,
    summary: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DefinitionSpec {
    schema: SchemaSpec,
    contracts: Vec<ContractSpec>,
    nodes: Vec<String>,
    edges: Vec<EdgeSpec>,
    node_definitions: Vec<NodeSpec>,
    edge_definitions: Vec<EdgeDefinitionSpec>,
    transitions: Vec<TransitionSpec>,
    roots: Vec<RootSpec>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SchemaSpec {
    node_types: Vec<String>,
    object_types: Vec<String>,
    tags: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ContractSpec {
    id: String,
    object_type: String,
    validator: Validator,
}

/// The fixed validator menu both implementations provide.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum Validator {
    AcceptAll,
    RejectAll,
    /// Accepts exactly the bytes given in hex.
    BytesEqual(String),
    /// Accepts a nonempty payload whose first byte is even.
    FirstByteEven,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct EdgeSpec {
    id: String,
    source: String,
    target: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct NodeSpec {
    node: String,
    types: Vec<String>,
    result_contract: String,
    ingress: Ingress,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Ingress {
    Any,
    All,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct EdgeDefinitionSpec {
    edge: String,
    types: Vec<String>,
    source_requirements: Vec<String>,
    target_requirements: Vec<String>,
    package_contract: String,
    tags: Vec<String>,
    authority_match: Match,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum Match {
    AnyOf,
    AllOf,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct TransitionSpec {
    node: String,
    source: Vec<String>,
    target: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RootSpec {
    node: String,
    ceiling: Vec<String>,
}

/// A package identity `[producer, output]`: the producer's `u128` in decimal
/// and the output ordinal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct PackageRef(String, u64);

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum TraceOp {
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
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum TriggerSpec {
    Orig {
        node: String,
        authority: Vec<String>,
    },
    Pkgs(Vec<PackageRef>),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct EmissionSpec {
    destination: Destination,
    authority: AuthoritySpec,
    payload: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum Destination {
    Delivered(String),
    Outbound(String),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum AuthoritySpec {
    Carry,
    Transition(Vec<String>),
}

/// The kernel's outcome of one operation, and the canonical state after it.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Expectation {
    accepted: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    state: Option<Value>,
}

impl TraceOp {
    fn expect(&self) -> Option<&Expectation> {
        match self {
            Self::Activate { expect, .. }
            | Self::Transfer { expect, .. }
            | Self::Retire { expect, .. } => expect.as_ref(),
        }
    }

    fn expect_mut(&mut self) -> &mut Option<Expectation> {
        match self {
            Self::Activate { expect, .. }
            | Self::Transfer { expect, .. }
            | Self::Retire { expect, .. } => expect,
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            Self::Activate { .. } => "activate",
            Self::Transfer { .. } => "transfer",
            Self::Retire { .. } => "retire",
        }
    }

    /// The payloads the operation commits to or checks against a commitment.
    fn payloads(&self) -> Vec<&str> {
        match self {
            Self::Activate { emissions, .. } => emissions
                .iter()
                .map(|emission| emission.payload.as_str())
                .collect(),
            Self::Transfer { payload, .. } => vec![payload.as_str()],
            Self::Retire { .. } => Vec::new(),
        }
    }
}

impl Validator {
    fn accepts(&self, payload: &[u8]) -> bool {
        match self {
            Self::AcceptAll => true,
            Self::RejectAll => false,
            Self::BytesEqual(expected) => payload == unhex(expected).as_slice(),
            Self::FirstByteEven => payload.first().is_some_and(|byte| byte % 2 == 0),
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing to a string cannot fail");
    }
    text
}

fn unhex(text: &str) -> Vec<u8> {
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

fn activation_text(id: ActivationId) -> String {
    id.as_u128().to_string()
}

fn parse_activation(text: &str) -> ActivationId {
    ActivationId::from_u128(
        text.parse()
            .unwrap_or_else(|_| panic!("activation id {text:?} is not a decimal u128")),
    )
}

fn package_ref(id: PackageId) -> PackageRef {
    PackageRef(
        activation_text(id.producer()),
        u64::try_from(id.output()).expect("output ordinals fit in u64"),
    )
}

fn parse_package(reference: &PackageRef) -> PackageId {
    PackageId::from_parts(parse_activation(&reference.0), u128::from(reference.1))
}

// Admission of a trace definition.

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).expect("authority tags are nonempty")
}

fn authority(tags: &[String]) -> Authority {
    Authority::new(tags.iter().map(|id| tag(id)))
}

fn admit(definition: &DefinitionSpec) -> Kernel {
    let contracts = definition.contracts.iter().map(|spec| {
        let validator = spec.validator.clone();
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
    });
    let nodes = definition.node_definitions.iter().map(|node| {
        NodeDefinition::new(
            node.node.as_str(),
            node.types.iter().map(String::as_str),
            node.result_contract.as_str(),
        )
        .expect("node definitions are well formed")
        .with_ingress_mode(match node.ingress {
            Ingress::Any => IngressMode::Any,
            Ingress::All => IngressMode::All,
        })
    });
    let edges = definition.edge_definitions.iter().map(|edge| {
        EdgeDefinition::new(
            edge.edge.as_str(),
            edge.types.iter().map(String::as_str),
            edge.source_requirements.iter().map(String::as_str),
            edge.target_requirements.iter().map(String::as_str),
            edge.package_contract.as_str(),
            edge.tags.iter().map(|id| tag(id)),
        )
        .expect("edge definitions are well formed")
        .with_authority_match(match edge.authority_match {
            Match::AnyOf => AuthorityMatch::AnyOf,
            Match::AllOf => AuthorityMatch::AllOf,
        })
    });
    Kernel::admit(
        DefinitionId::new("lean-oracle").unwrap(),
        Schema::new(
            definition.schema.node_types.iter().map(String::as_str),
            definition.schema.object_types.iter().map(String::as_str),
            definition.schema.tags.iter().map(|id| tag(id)),
        )
        .expect("the schema is well formed"),
        Graph::new(
            definition
                .nodes
                .iter()
                .map(|id| Node::new(id.as_str()).unwrap()),
            definition.edges.iter().map(|edge| {
                Edge::new(edge.id.as_str(), edge.source.as_str(), edge.target.as_str()).unwrap()
            }),
        )
        .expect("the topology is admitted"),
        contracts,
        nodes,
        edges,
        definition.transitions.iter().map(|rule| {
            AuthorityTransitionRule::new(
                rule.node.as_str(),
                authority(&rule.source),
                authority(&rule.target),
            )
            .unwrap()
        }),
        definition
            .roots
            .iter()
            .map(|root| RootRule::new(root.node.as_str(), authority(&root.ceiling)).unwrap()),
    )
    .expect("the kernel admits the trace definition")
}

// The canonical state of `formal/TRACE_FORMAT.md`, from the kernel's checkpoint.

fn package_json(id: PackageId) -> Value {
    json!([
        activation_text(id.producer()),
        u64::try_from(id.output()).expect("output ordinals fit in u64")
    ])
}

fn authority_json(authority: &Authority) -> Value {
    json!(authority.tags().map(AuthorityTag::id).collect::<Vec<_>>())
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
            json!({"orig": {"node": &**node_id, "authority": authority_json(authority)}})
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
                "authority": authority_json(output.authority()),
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
        "authority": authority_json(record.authority()),
        "digest": record.content_digest().to_string(),
        "producer_node": record.producer_node(),
        "delivery": record.delivery().map(|delivery| json!({
            "edge": delivery.edge_id(),
            "receiver": delivery.receiver(),
        })),
        "status": status,
    })
}

/// The canonical state after one op. Its entries are shared with the states
/// before it, so recording a state costs only the entries that changed.
struct Snapshot {
    activations: Vec<Arc<Value>>,
    packages: Vec<Arc<Value>>,
    /// The remaining fields: lifetime identities, changes, and the revision.
    rest: serde_json::Map<String, Value>,
}

impl Snapshot {
    fn to_value(&self) -> Value {
        let entries = |values: &[Arc<Value>]| {
            Value::Array(values.iter().map(|value| Value::clone(value)).collect())
        };
        let mut state = self.rest.clone();
        state.insert("activations".to_owned(), entries(&self.activations));
        state.insert("packages".to_owned(), entries(&self.packages));
        Value::Object(state)
    }

    /// Whether the model's canonical state equals this one.
    fn matches(&self, model: &Value) -> bool {
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
            model.len() == self.rest.len() + 2
                && entries(&self.activations, model.get("activations"))
                && entries(&self.packages, model.get("packages"))
                && self
                    .rest
                    .iter()
                    .all(|(key, value)| model.get(key) == Some(value))
        })
    }
}

/// Encodes checkpoints canonically, reusing the encoding of every entry whose
/// record is unchanged since the last checkpoint it encoded.
#[derive(Default)]
struct Canonical {
    activations: BTreeMap<ActivationId, (Activation, Arc<Value>)>,
    packages: BTreeMap<PackageId, (PackageRecord, Arc<Value>)>,
}

impl Canonical {
    fn encode(&mut self, checkpoint: &Checkpoint) -> Snapshot {
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
            "used_nodes": checkpoint.used_node_ids.iter().map(|id| &**id).collect::<Vec<_>>(),
            "used_edges": checkpoint.used_edge_ids.iter().map(|id| &**id).collect::<Vec<_>>(),
            "definition_changes": checkpoint.definition_changes,
            "revision": checkpoint.revision,
        }) else {
            unreachable!("a JSON object literal is an object");
        };
        Snapshot {
            activations,
            packages,
            rest,
        }
    }
}

// Running operations on the kernel.

/// Where an activation's identity comes from.
#[derive(Clone, Copy)]
enum Identity {
    /// `Kernel::activate` draws it, and the recorder writes it into the op.
    /// A rejected proposal discloses no identity, so the recorder writes a
    /// fresh one, which the model's freshness premise treats alike.
    Drawn,
    /// The op's identity is evaluated and applied as given, which is what
    /// `Kernel::activate` does with the identity it draws.
    Recorded,
}

fn proposal(trigger: &TriggerSpec, result: &str, emissions: &[EmissionSpec]) -> ActivationProposal {
    let result: Payload = Arc::from(unhex(result));
    let mut proposal = match trigger {
        TriggerSpec::Orig {
            node,
            authority: tags,
        } => ActivationProposal::root(node.as_str(), authority(tags), result),
        TriggerSpec::Pkgs(inputs) => {
            ActivationProposal::join(inputs.iter().map(parse_package), result)
        }
    };
    for emission in emissions {
        let output_authority = match &emission.authority {
            AuthoritySpec::Carry => OutputAuthority::Carry,
            AuthoritySpec::Transition(tags) => OutputAuthority::Transition(authority(tags)),
        };
        let payload: Payload = Arc::from(unhex(&emission.payload));
        proposal.emit(match &emission.destination {
            Destination::Delivered(edge) => Emission::new(edge.as_str(), output_authority, payload),
            Destination::Outbound(object_type) => {
                Emission::outbound(object_type.as_str(), output_authority, payload)
            }
        });
    }
    proposal
}

fn fresh_identity(state: &State) -> ActivationId {
    loop {
        let id = ActivationId::fresh();
        if state.activation(id).is_none() {
            return id;
        }
    }
}

/// Runs one op on the kernel and reports whether it was accepted.
fn execute(kernel: &Kernel, state: &mut State, op: &mut TraceOp, identity: Identity) -> bool {
    match op {
        TraceOp::Activate {
            id,
            trigger,
            result,
            emissions,
            ..
        } => {
            let proposal = proposal(trigger, result, emissions);
            match identity {
                Identity::Drawn => {
                    let (drawn, accepted) = match kernel.activate(state, proposal) {
                        Ok(drawn) => (drawn, true),
                        Err(_) => (fresh_identity(state), false),
                    };
                    *id = activation_text(drawn);
                    accepted
                }
                Identity::Recorded => kernel
                    .evaluate_activation(state, parse_activation(id), proposal)
                    .is_ok_and(|transition| state.apply(kernel, &transition).is_ok()),
            }
        }
        TraceOp::Transfer {
            package,
            edge,
            payload,
            ..
        } => kernel
            .prepare_transfer(state, parse_package(package), edge, &unhex(payload))
            .and_then(|prepared| kernel.commit_transfer(state, prepared))
            .is_ok(),
        TraceOp::Retire {
            package, evidence, ..
        } => kernel
            .retire(
                state,
                parse_package(package),
                evidence.as_deref().map(parse_activation),
            )
            .is_ok(),
    }
}

/// The kernel's outcome of one op and its canonical state after it.
struct Outcome {
    accepted: bool,
    state: Snapshot,
}

/// One run of the kernel, recorded as a trace.
struct Run {
    name: String,
    seed: Option<u64>,
    definition: DefinitionSpec,
    kernel: Kernel,
    state: State,
    /// The ops as run, without expectations.
    ops: Vec<TraceOp>,
    outcomes: Vec<Outcome>,
    digests: BTreeMap<String, String>,
    /// Every package in birth order, whatever its status.
    packages: Vec<PackageId>,
    /// Every accepted activation in acceptance order.
    activations: Vec<ActivationId>,
    /// The bytes behind every digest an op has used.
    payloads: BTreeMap<ContentDigest, Vec<u8>>,
    canonical: Canonical,
}

impl Run {
    fn new(name: String, seed: Option<u64>, definition: DefinitionSpec) -> Self {
        let kernel = admit(&definition);
        let state = kernel.empty_state();
        Self {
            name,
            seed,
            definition,
            kernel,
            state,
            ops: Vec::new(),
            outcomes: Vec::new(),
            digests: BTreeMap::new(),
            packages: Vec::new(),
            activations: Vec::new(),
            payloads: BTreeMap::new(),
            canonical: Canonical::default(),
        }
    }

    /// Runs one op on the kernel and records it with the kernel's outcome and
    /// the canonical state after it.
    fn record(&mut self, mut op: TraceOp, identity: Identity) -> bool {
        *op.expect_mut() = None;
        for payload in op.payloads() {
            let bytes = unhex(payload);
            let digest = ContentDigest::compute(&bytes);
            self.digests
                .entry(payload.to_owned())
                .or_insert_with(|| digest.to_string());
            self.payloads.entry(digest).or_insert(bytes);
        }
        let accepted = execute(&self.kernel, &mut self.state, &mut op, identity);
        if accepted && let TraceOp::Activate { id, .. } = &op {
            let activation = parse_activation(id);
            self.activations.push(activation);
            self.packages.extend(
                self.state
                    .activation(activation)
                    .expect("an accepted activation is recorded")
                    .outputs(),
            );
        }
        self.outcomes.push(Outcome {
            accepted,
            state: self.canonical.encode(&self.state.checkpoint()),
        });
        self.ops.push(op);
        accepted
    }

    /// Records a prefix op that must have the stated outcome.
    fn want(&mut self, accepted: bool, why: &str, op: TraceOp) -> Option<ActivationId> {
        let outcome = self.record(op, Identity::Drawn);
        assert_eq!(
            outcome,
            accepted,
            "{}: prefix step {} ({why}) was meant to be {}",
            self.name,
            self.ops.len() - 1,
            verdict(accepted)
        );
        match self.ops.last() {
            Some(TraceOp::Activate { id, .. }) if accepted => Some(parse_activation(id)),
            _ => None,
        }
    }

    fn accept(&mut self, why: &str, op: TraceOp) {
        self.want(true, why, op);
    }

    fn accept_activation(&mut self, why: &str, op: TraceOp) -> ActivationId {
        self.want(true, why, op)
            .unwrap_or_else(|| panic!("{}: {why} is not an activation", self.name))
    }

    fn reject(&mut self, why: &str, op: TraceOp) {
        self.want(false, why, op);
    }

    /// The trace as the oracle reads it: the ops alone.
    fn trace(&self) -> Trace {
        Trace {
            format: FORMAT.to_owned(),
            name: self.name.clone(),
            seed: self.seed,
            known_disagreement: None,
            definition: self.definition.clone(),
            digests: self.digests.clone(),
            ops: self.ops.clone(),
        }
    }

    /// The trace with the kernel's outcome and state after every op.
    fn annotated(&self) -> Trace {
        let mut trace = self.trace();
        for (op, outcome) in trace.ops.iter_mut().zip(&self.outcomes) {
            *op.expect_mut() = Some(Expectation {
                accepted: outcome.accepted,
                state: Some(outcome.state.to_value()),
            });
        }
        trace
    }

    /// The live packages, in birth order, whose records satisfy `filter`.
    fn live(&self, filter: impl Fn(&PackageRecord) -> bool) -> Vec<PackageId> {
        self.packages
            .iter()
            .copied()
            .filter(|id| {
                self.state
                    .package(*id)
                    .is_some_and(|record| record.is_live() && filter(record))
            })
            .collect()
    }
}

fn verdict(accepted: bool) -> &'static str {
    if accepted { "accepted" } else { "rejected" }
}

// Op constructors for the prefixes and the random explorer.

fn names(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

fn orig(node: &str, tags: &[&str]) -> TriggerSpec {
    TriggerSpec::Orig {
        node: node.to_owned(),
        authority: names(tags),
    }
}

/// The canonical input set the kernel evaluates: sorted, without repeats.
fn pkgs(inputs: &[PackageId]) -> TriggerSpec {
    let inputs: BTreeSet<PackageId> = inputs.iter().copied().collect();
    TriggerSpec::Pkgs(inputs.into_iter().map(package_ref).collect())
}

fn carry() -> AuthoritySpec {
    AuthoritySpec::Carry
}

fn to(tags: &[&str]) -> AuthoritySpec {
    AuthoritySpec::Transition(names(tags))
}

fn delivered(edge: &str, authority: AuthoritySpec, payload: &[u8]) -> EmissionSpec {
    EmissionSpec {
        destination: Destination::Delivered(edge.to_owned()),
        authority,
        payload: hex(payload),
    }
}

fn outbound(object_type: &str, authority: AuthoritySpec, payload: &[u8]) -> EmissionSpec {
    EmissionSpec {
        destination: Destination::Outbound(object_type.to_owned()),
        authority,
        payload: hex(payload),
    }
}

fn activate(trigger: TriggerSpec, result: &[u8], emissions: Vec<EmissionSpec>) -> TraceOp {
    TraceOp::Activate {
        id: String::new(),
        trigger,
        result: hex(result),
        emissions,
        expect: None,
    }
}

fn transfer(package: PackageId, edge: &str, payload: &[u8]) -> TraceOp {
    TraceOp::Transfer {
        package: package_ref(package),
        edge: edge.to_owned(),
        payload: hex(payload),
        expect: None,
    }
}

fn retire(package: PackageId, evidence: Option<ActivationId>) -> TraceOp {
    TraceOp::Retire {
        package: package_ref(package),
        evidence: evidence.map(activation_text),
        expect: None,
    }
}

/// The first `N` outputs of an activation.
fn outputs<const N: usize>(activation: ActivationId) -> [PackageId; N] {
    std::array::from_fn(|index| {
        PackageId::from_parts(activation, u128::try_from(index).expect("small ordinal"))
    })
}

/// An identity no kernel draws: `ActivationId::fresh` is a version 4 UUID,
/// whose version bits are never all zero.
fn unknown_activation() -> ActivationId {
    ActivationId::from_u128(7)
}

fn unknown_package() -> PackageId {
    PackageId::from_parts(unknown_activation(), 0)
}

// The fixed definitions.

fn contract(id: &str, object_type: &str, validator: Validator) -> ContractSpec {
    ContractSpec {
        id: id.to_owned(),
        object_type: object_type.to_owned(),
        validator,
    }
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

/// `a` roots under `{run, audit}` and fans out to `b` over four parallel
/// edges (`AnyOf`, `AllOf`, a rejecting contract, and a `bytes_equal`
/// contract of another object type) and to the `All` node `j` over the
/// parallel edges `aj1` and `aj2`. `j` feeds `x`, which roots under `{run}`,
/// loops on itself, and closes a cycle back to `a`.
fn coverage_definition() -> DefinitionSpec {
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
    DefinitionSpec {
        schema: SchemaSpec {
            node_types: names(&["n"]),
            object_types: names(&["t", "u"]),
            tags: names(&["run", "audit", "admin"]),
        },
        contracts: vec![
            contract("c_any", "t", Validator::AcceptAll),
            contract("c_none", "t", Validator::RejectAll),
            contract("c_even", "t", Validator::FirstByteEven),
            contract("c_ok", "u", Validator::BytesEqual(hex(b"ok"))),
        ],
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
    }
}

/// `s` feeds the `All` node `m` over two parallel edges, and `m` also receives
/// on its own self-loop, so a join at `m` needs a delivery `m` made; `m` feeds
/// `k`, which loops on itself through a rejecting contract and closes the
/// cycle back to `s`.
fn cyclic_definition() -> DefinitionSpec {
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
    DefinitionSpec {
        schema: SchemaSpec {
            node_types: names(&["n"]),
            object_types: names(&["t"]),
            tags: names(&["p", "q"]),
        },
        contracts: vec![
            contract("acc", "t", Validator::AcceptAll),
            contract("even", "t", Validator::FirstByteEven),
            contract("rej", "t", Validator::RejectAll),
        ],
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
    }
}

/// `root` reaches the `leaf` node `sink` over an exact-bytes `AllOf` edge and a
/// parallel edge of another object type; `lonely` is an `All` node without
/// incoming edges whose root ceiling is empty. Nodes and edges are declared
/// out of order, since neither side may depend on declaration order.
fn sparse_definition() -> DefinitionSpec {
    let (mut edges, mut edge_definitions): (Vec<_>, Vec<_>) = [
        edge("rs", ("root", "sink"), "exact", &["r"], Match::AllOf),
        edge("ru", ("root", "sink"), "u_acc", &["r"], Match::AnyOf),
    ]
    .into_iter()
    .unzip();
    edge_definitions[0].target_requirements = names(&["leaf"]);
    edges.sort_by(|left, right| right.id.cmp(&left.id));
    DefinitionSpec {
        schema: SchemaSpec {
            node_types: names(&["n", "leaf"]),
            object_types: names(&["t", "u"]),
            tags: names(&["r"]),
        },
        contracts: vec![
            contract("acc", "t", Validator::AcceptAll),
            contract("u_acc", "u", Validator::AcceptAll),
            contract("exact", "t", Validator::BytesEqual(hex(b"\x00\x01"))),
        ],
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
    }
}

// The required prefixes. Each step states the kernel's intended outcome, so
// the prefix provably reaches every case it names before random exploration.

/// A root at `node` under `tags`.
fn rooted(node: &str, tags: &[&str], emissions: Vec<EmissionSpec>) -> TraceOp {
    activate(orig(node, tags), b"r", emissions)
}

/// A package trigger over `inputs`.
fn joined(inputs: &[PackageId], result: &[u8], emissions: Vec<EmissionSpec>) -> TraceOp {
    activate(pkgs(inputs), result, emissions)
}

fn coverage_prefix(run: &mut Run) {
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

struct Fixture {
    name: &'static str,
    definition: fn() -> DefinitionSpec,
    prefix: fn(&mut Run),
}

const FIXTURES: [Fixture; 3] = [
    Fixture {
        name: "coverage",
        definition: coverage_definition,
        prefix: coverage_prefix,
    },
    Fixture {
        name: "cyclic",
        definition: cyclic_definition,
        prefix: cyclic_prefix,
    },
    Fixture {
        name: "sparse",
        definition: sparse_definition,
        prefix: sparse_prefix,
    },
];

// Random exploration.

/// Deterministic xorshift choices.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).expect("small bound")).unwrap()
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
        (!items.is_empty()).then(|| &items[self.below(items.len())])
    }

    fn subset(&mut self, items: &[String]) -> Vec<String> {
        items.iter().filter(|_| self.chance(50)).cloned().collect()
    }
}

const PAYLOADS: [&[u8]; 9] = [
    b"",
    b"ok",
    b"no",
    b"\x00",
    b"\x01",
    b"\x00\x01",
    b"\x02A",
    b"\x03A",
    b"payload",
];

fn random_payload(rng: &mut Rng) -> Vec<u8> {
    PAYLOADS[rng.below(PAYLOADS.len())].to_vec()
}

/// Usually a payload `validator` accepts, otherwise any payload.
fn payload_for(rng: &mut Rng, validator: Option<&Validator>) -> Vec<u8> {
    let accepted: Vec<&[u8]> = validator.map_or_else(Vec::new, |validator| {
        PAYLOADS
            .into_iter()
            .filter(|payload| validator.accepts(payload))
            .collect()
    });
    match rng.pick(&accepted) {
        Some(payload) if rng.chance(80) => payload.to_vec(),
        _ => random_payload(rng),
    }
}

fn same_set(left: &[String], right: &[String]) -> bool {
    left.iter().collect::<BTreeSet<_>>() == right.iter().collect::<BTreeSet<_>>()
}

/// Structural lookups that steer the explorer toward admissible operations.
/// They only bias choices; the kernel and the model decide every outcome.
impl DefinitionSpec {
    fn validator(&self, contract: &str) -> Option<&Validator> {
        self.contracts
            .iter()
            .find(|spec| spec.id == contract)
            .map(|spec| &spec.validator)
    }

    fn edge_definition(&self, edge: &str) -> Option<&EdgeDefinitionSpec> {
        self.edge_definitions.iter().find(|spec| spec.edge == edge)
    }

    fn edge_validator(&self, edge: &str) -> Option<&Validator> {
        self.edge_definition(edge)
            .and_then(|spec| self.validator(&spec.package_contract))
    }

    fn result_validator(&self, node: &str) -> Option<&Validator> {
        self.node_definitions
            .iter()
            .find(|spec| spec.node == node)
            .and_then(|spec| self.validator(&spec.result_contract))
    }

    fn ceiling(&self, node: &str) -> Option<&[String]> {
        self.roots
            .iter()
            .find(|root| root.node == node)
            .map(|root| root.ceiling.as_slice())
    }

    fn is_all(&self, node: &str) -> bool {
        self.node_definitions
            .iter()
            .any(|spec| spec.node == node && spec.ingress == Ingress::All)
    }

    fn leaving(&self, node: &str) -> Vec<&str> {
        self.edges
            .iter()
            .filter(|edge| edge.source == node)
            .map(|edge| edge.id.as_str())
            .collect()
    }

    /// Whether `edge` would carry a package of this type and authority.
    fn fits(&self, edge: &str, object_type: Option<&str>, authority: &[String]) -> bool {
        self.edge_definition(edge).is_some_and(|spec| {
            let tags = spec.tags.iter();
            let matched = match spec.authority_match {
                Match::AnyOf => tags.clone().any(|tag| authority.contains(tag)),
                Match::AllOf => tags.clone().all(|tag| authority.contains(tag)),
            };
            let typed = object_type.is_none_or(|object_type| {
                self.contracts
                    .iter()
                    .any(|c| c.id == spec.package_contract && c.object_type == object_type)
            });
            matched && typed
        })
    }
}

/// One random op. Consumption and transfer need live work they could act on;
/// without it they usually yield to a root, which births more.
fn random_step(run: &mut Run, rng: &mut Rng) {
    let delivered = !run.live(|record| record.delivery().is_some()).is_empty();
    let transferable = !transferable(run).is_empty();
    match rng.below(100) {
        25..=56 if delivered || rng.chance(20) => random_consumption(run, rng),
        57..=77 if transferable || rng.chance(20) => random_transfer(run, rng),
        78..=89 => random_retirement(run, rng),
        90..=94 => random_stray(run, rng),
        _ => random_root(run, rng),
    }
}

/// Zero to three births at `node` under the governing authority `governing`,
/// mostly shaped to be admissible, and outbound ones mostly shaped for a
/// later transfer along an edge leaving `node`.
fn random_emissions(
    definition: &DefinitionSpec,
    rng: &mut Rng,
    node: &str,
    governing: &[String],
) -> Vec<EmissionSpec> {
    let leaving = definition.leaving(node);
    let rules: Vec<&TransitionSpec> = definition
        .transitions
        .iter()
        .filter(|rule| rule.node == node && same_set(&rule.source, governing))
        .collect();
    let count = rng.below(4);
    (0..count)
        .map(|_| {
            let (authority, carried) = match (rng.below(100), rng.pick(&rules)) {
                (0..=83, _) => (AuthoritySpec::Carry, governing.to_vec()),
                (84..=95, Some(rule)) => (
                    AuthoritySpec::Transition(rule.target.clone()),
                    rule.target.clone(),
                ),
                (84..=97, _) => (
                    AuthoritySpec::Transition(governing.to_vec()),
                    governing.to_vec(),
                ),
                _ => {
                    let target = rng.subset(&definition.schema.tags);
                    (AuthoritySpec::Transition(target.clone()), target)
                }
            };
            let fitting: Vec<&str> = leaving
                .iter()
                .copied()
                .filter(|edge| definition.fits(edge, None, &carried))
                .collect();
            let edge = match rng.below(100) {
                0..=64 => rng.pick(&fitting).map(|edge| (*edge).to_owned()),
                65..=68 => rng.pick(&leaving).map(|edge| (*edge).to_owned()),
                69..=71 => Some(rng.pick(&definition.edges).unwrap().id.clone()),
                72 => Some("zz".to_owned()),
                _ => None,
            };
            let (destination, payload) = if let Some(edge) = edge {
                let payload = payload_for(rng, definition.edge_validator(&edge));
                (Destination::Delivered(edge), payload)
            } else if rng.chance(2) {
                (
                    Destination::Outbound("nope".to_owned()),
                    random_payload(rng),
                )
            } else {
                let contract = rng
                    .pick(&fitting)
                    .filter(|_| rng.chance(75))
                    .and_then(|edge| {
                        let spec = definition.edge_definition(edge)?;
                        definition
                            .contracts
                            .iter()
                            .find(|contract| contract.id == spec.package_contract)
                    });
                match contract {
                    Some(contract) => (
                        Destination::Outbound(contract.object_type.clone()),
                        payload_for(rng, Some(&contract.validator)),
                    ),
                    None => (
                        Destination::Outbound(
                            rng.pick(&definition.schema.object_types).unwrap().clone(),
                        ),
                        random_payload(rng),
                    ),
                }
            };
            EmissionSpec {
                destination,
                authority,
                payload: hex(&payload),
            }
        })
        .collect()
}

fn random_root(run: &mut Run, rng: &mut Rng) {
    let definition = &run.definition;
    let node = match rng.below(100) {
        0..=84 => rng.pick(&definition.roots).unwrap().node.clone(),
        85..=96 => rng.pick(&definition.nodes).unwrap().clone(),
        _ => "nowhere".to_owned(),
    };
    let authority = match (rng.below(100), definition.ceiling(&node)) {
        (0..=84, Some(ceiling)) => rng.subset(ceiling),
        (0..=95, _) => rng.subset(&definition.schema.tags),
        _ => {
            let mut tags = rng.subset(&definition.schema.tags);
            tags.push("ghost".to_owned());
            tags
        }
    };
    let emissions = random_emissions(definition, rng, &node, &authority);
    let result = payload_for(rng, definition.result_validator(&node));
    let op = activate(TriggerSpec::Orig { node, authority }, &result, emissions);
    run.record(op, Identity::Drawn);
}

/// A package of any status, or occasionally one that was never born.
fn any_package(run: &Run, rng: &mut Rng) -> PackageId {
    match rng.pick(&run.packages) {
        Some(id) if !rng.chance(10) => *id,
        _ => stray_package(run, rng),
    }
}

/// A package identity no activation produced: an output ordinal beyond an
/// accepted activation's outputs, or a producer that never existed.
fn stray_package(run: &Run, rng: &mut Rng) -> PackageId {
    match rng.pick(&run.activations) {
        Some(activation) if rng.chance(50) => PackageId::from_parts(*activation, 99),
        _ => PackageId::from_parts(ActivationId::from_u128(u128::from(rng.next())), 0),
    }
}

/// Every complete `All` join the frontier offers: for each authority, the
/// first live package on every incoming edge, when each edge has one.
fn complete_joins(run: &Run) -> Vec<PackageId> {
    let mut joins = Vec::new();
    for node in &run.definition.node_definitions {
        if node.ingress != Ingress::All {
            continue;
        }
        let incoming = run
            .definition
            .edges
            .iter()
            .filter(|edge| edge.target == node.node)
            .count();
        let mut heads: BTreeMap<&Authority, BTreeMap<&str, PackageId>> = BTreeMap::new();
        for id in run.live(|record| record.holder() == node.node && record.delivery().is_some()) {
            let record = run.state.package(id).unwrap();
            heads
                .entry(record.authority())
                .or_default()
                .entry(record.delivery().unwrap().edge_id())
                .or_insert(id);
        }
        joins.extend(
            heads
                .values()
                .filter(|by_edge| incoming > 0 && by_edge.len() == incoming)
                .filter_map(|by_edge| by_edge.values().next().copied()),
        );
    }
    joins
}

/// A package trigger: usually a legal one, sometimes perturbed into one of
/// the ways a trigger can fail, and sometimes an arbitrary package set.
fn random_consumption(run: &mut Run, rng: &mut Rng) {
    let delivered = run.live(|record| record.delivery().is_some());
    let joins = complete_joins(run);
    let anchor = match rng.pick(&joins) {
        Some(join) if rng.chance(80) => Some(join),
        _ => rng.pick(&delivered),
    };
    let mut inputs = Vec::new();
    let (node, governing) = match anchor {
        Some(anchor) if !rng.chance(8) => {
            let anchor = *anchor;
            let record = run.state.package(anchor).unwrap().clone();
            let node = record.holder().to_owned();
            let at_node: Vec<PackageId> = delivered
                .iter()
                .copied()
                .filter(|id| *id != anchor && run.state.package(*id).unwrap().holder() == node)
                .collect();
            inputs.push(anchor);
            if run.definition.is_all(&node) {
                let anchor_edge = record.delivery().unwrap().edge_id();
                for edge in run
                    .definition
                    .edges
                    .iter()
                    .filter(|edge| edge.target == node && edge.id != anchor_edge)
                {
                    let candidates: Vec<PackageId> = at_node
                        .iter()
                        .copied()
                        .filter(|id| {
                            let candidate = run.state.package(*id).unwrap();
                            candidate.delivery().unwrap().edge_id() == edge.id
                                && candidate.authority() == record.authority()
                        })
                        .collect();
                    if let Some(candidate) = rng.pick(&candidates) {
                        inputs.push(*candidate);
                    }
                }
            }
            match rng.below(14) {
                0 if inputs.len() > 1 => {
                    inputs.remove(rng.below(inputs.len()));
                }
                1 | 2 => {
                    if let Some(other) = rng.pick(&at_node) {
                        inputs.push(*other);
                    }
                }
                3 => {
                    let outbound = run.live(|candidate| candidate.delivery().is_none());
                    if let Some(package) = rng.pick(&outbound) {
                        inputs.push(*package);
                    }
                }
                4 => inputs.push(any_package(run, rng)),
                _ => {}
            }
            let governing = record
                .authority()
                .tags()
                .map(|tag| tag.id().to_owned())
                .collect();
            (node, governing)
        }
        _ => {
            for _ in 0..=rng.below(2) {
                inputs.push(any_package(run, rng));
            }
            (rng.pick(&run.definition.nodes).unwrap().clone(), Vec::new())
        }
    };
    let emissions = random_emissions(&run.definition, rng, &node, &governing);
    let result = payload_for(rng, run.definition.result_validator(&node));
    run.record(activate(pkgs(&inputs), &result, emissions), Identity::Drawn);
}

/// The edges leaving a package's producer that would carry it: its type and
/// authority fit, and the contract accepts its committed bytes.
fn carrying_edges<'a>(run: &'a Run, record: &PackageRecord) -> Vec<&'a str> {
    let authority: Vec<String> = record
        .authority()
        .tags()
        .map(|tag| tag.id().to_owned())
        .collect();
    let committed = run.payloads.get(&record.content_digest());
    run.definition
        .leaving(record.producer_node())
        .into_iter()
        .filter(|edge| {
            run.definition
                .fits(edge, Some(record.object_type()), &authority)
                && committed.is_some_and(|bytes| {
                    run.definition
                        .edge_validator(edge)
                        .is_some_and(|validator| validator.accepts(bytes))
                })
        })
        .collect()
}

/// The live outbound packages some edge would carry.
fn transferable(run: &Run) -> Vec<PackageId> {
    run.live(|record| record.delivery().is_none() && !carrying_edges(run, record).is_empty())
}

fn random_transfer(run: &mut Run, rng: &mut Rng) {
    let outbound = run.live(|record| record.delivery().is_none());
    let transferable = transferable(run);
    let package = match (rng.below(100), rng.pick(&transferable), rng.pick(&outbound)) {
        (0..=79, Some(id), _) | (0..=91, _, Some(id)) => *id,
        _ => any_package(run, rng),
    };
    let record = run.state.package(package).cloned();
    let (carrying, leaving) = record.as_ref().map_or_else(Default::default, |record| {
        (
            carrying_edges(run, record),
            run.definition.leaving(record.producer_node()),
        )
    });
    let edge = match rng.below(100) {
        0..=69 => rng.pick(&carrying).or_else(|| rng.pick(&leaving)),
        70..=84 => rng.pick(&leaving),
        _ => None,
    }
    .map_or_else(
        || {
            if rng.chance(90) {
                rng.pick(&run.definition.edges).unwrap().id.clone()
            } else {
                "zz".to_owned()
            }
        },
        |edge| (*edge).to_owned(),
    );
    let committed = record.and_then(|record| run.payloads.get(&record.content_digest()).cloned());
    let payload = match committed {
        Some(bytes) if rng.chance(88) => bytes,
        _ => random_payload(rng),
    };
    run.record(transfer(package, &edge, &payload), Identity::Drawn);
}

fn random_retirement(run: &mut Run, rng: &mut Rng) {
    let live = run.live(|_| true);
    let package = match rng.pick(&live) {
        Some(id) if rng.chance(75) => *id,
        _ => any_package(run, rng),
    };
    let evidence = match rng.below(100) {
        0..=44 => None,
        45..=89 => rng.pick(&run.activations).copied(),
        _ => Some(ActivationId::from_u128(u128::from(rng.next()))),
    };
    run.record(retire(package, evidence), Identity::Drawn);
}

/// Ops over identities that were never born.
fn random_stray(run: &mut Run, rng: &mut Rng) {
    let package = stray_package(run, rng);
    let op = match rng.below(4) {
        0 => activate(pkgs(&[]), b"", Vec::new()),
        1 => activate(pkgs(&[package]), b"", Vec::new()),
        2 => {
            let edge = rng.pick(&run.definition.edges).unwrap().id.clone();
            transfer(package, &edge, b"ok")
        }
        _ => retire(package, None),
    };
    run.record(op, Identity::Drawn);
}

fn random_run(seed: u64) -> Run {
    let fixture = &FIXTURES[usize::try_from(seed % 3).unwrap()];
    let mut run = Run::new(
        format!("{}-{seed}", fixture.name),
        Some(seed),
        (fixture.definition)(),
    );
    (fixture.prefix)(&mut run);
    let mut rng = Rng::new(seed);
    for _ in 0..RANDOM_STEPS {
        random_step(&mut run, &mut rng);
    }
    run
}

fn seeds() -> BTreeSet<u64> {
    let mut seeds: BTreeSet<u64> = SEEDS.collect();
    let Ok(extra) = std::env::var("ONTOGRAPHY_LEAN_ORACLE_SEEDS") else {
        return seeds;
    };
    let parse = |text: &str| -> u64 {
        text.trim().parse().unwrap_or_else(|_| {
            panic!("ONTOGRAPHY_LEAN_ORACLE_SEEDS: {text:?} is not a seed; use a list like 7,40..60")
        })
    };
    for item in extra.split(',').filter(|item| !item.trim().is_empty()) {
        if let Some((start, end)) = item.split_once("..=") {
            seeds.extend(parse(start)..=parse(end));
        } else if let Some((start, end)) = item.split_once("..") {
            seeds.extend(parse(start)..parse(end));
        } else {
            seeds.insert(parse(item));
        }
    }
    seeds
}

// The oracle.

/// The oracle executable, or `None` after a loud skip notice when it is
/// absent and not required.
fn oracle() -> Option<PathBuf> {
    let path = std::env::var_os("ONTOGRAPHY_LEAN_ORACLE").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("formal/.lake/build/bin/oracle"),
        PathBuf::from,
    );
    if path.is_file() {
        return Some(path);
    }
    assert!(
        std::env::var("ONTOGRAPHY_REQUIRE_LEAN_ORACLE").as_deref() != Ok("1"),
        "ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1, but the Lean oracle {} does not exist; \
         build it with `cd formal && lake build oracle`",
        path.display()
    );
    eprintln!(
        "\n\
         ************************************************************************\n\
         SKIPPED: the Lean oracle {} does not exist, so the kernel is NOT being\n\
         checked against the Lean model. Build it with `cd formal && lake build\n\
         oracle`, or set ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1 to fail instead.\n\
         ************************************************************************\n",
        path.display()
    );
    None
}

/// Replays a run's trace with the oracle: acceptance and canonical state per
/// step, or why the oracle did not produce them.
fn replay_in_model(oracle: &Path, run: &Run) -> Result<Vec<(bool, Value)>, String> {
    let trace = run.trace();
    let mut child = Command::new(oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("cannot run the Lean oracle {}: {error}", oracle.display()))?;
    let input = serde_json::to_vec(&trace).unwrap();
    let written = child
        .stdin
        .take()
        .expect("the oracle's stdin is piped")
        .write_all(&input);
    let output = child
        .wait_with_output()
        .map_err(|error| format!("the Lean oracle did not finish: {error}"))?;
    if written.is_err() || !output.status.success() {
        return Err(format!(
            "the Lean oracle failed on trace {} ({}, {written:?}): {}",
            trace.name,
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8(output.stdout).map_err(|error| error.to_string())?;
    let steps = stdout
        .lines()
        .enumerate()
        .map(|(step, line)| {
            let mut result: Value = serde_json::from_str(line)
                .map_err(|error| format!("oracle line {step} is not JSON: {error}"))?;
            if result["step"] != json!(step) {
                return Err(format!(
                    "oracle line {step} reports step {}",
                    result["step"]
                ));
            }
            let accepted = result["accepted"]
                .as_bool()
                .ok_or_else(|| format!("oracle line {step} reports no acceptance"))?;
            Ok((accepted, result["state"].take()))
        })
        .collect::<Result<Vec<_>, String>>()?;
    if steps.len() != trace.ops.len() {
        return Err(format!(
            "the oracle replayed {} of the {} ops of trace {}",
            steps.len(),
            trace.ops.len(),
            trace.name
        ));
    }
    Ok(steps)
}

struct Mismatch {
    step: usize,
    kernel_accepted: bool,
    model_accepted: bool,
    differences: Vec<String>,
}

/// The first step at which the kernel's outcome or state differs from the
/// model's.
fn first_mismatch(run: &Run, model: &[(bool, Value)]) -> Option<Mismatch> {
    run.outcomes
        .iter()
        .zip(model)
        .enumerate()
        .find(|(_, (kernel, (accepted, state)))| {
            kernel.accepted != *accepted || !kernel.state.matches(state)
        })
        .map(|(step, (kernel, (accepted, state)))| {
            let mut differences = Vec::new();
            difference(
                "state",
                Some(&kernel.state.to_value()),
                Some(state),
                &mut differences,
            );
            Mismatch {
                step,
                kernel_accepted: kernel.accepted,
                model_accepted: *accepted,
                differences,
            }
        })
}

/// Entries keyed by their `id`, when every element of an array has one.
fn keyed(items: &[Value]) -> Option<BTreeMap<String, &Value>> {
    let keyed: BTreeMap<String, &Value> = items
        .iter()
        .map(|item| item.get("id").map(|id| (id.to_string(), item)))
        .collect::<Option<_>>()?;
    (keyed.len() == items.len()).then_some(keyed)
}

fn show(value: Option<&Value>) -> String {
    value.map_or_else(|| "absent".to_owned(), Value::to_string)
}

/// Appends the paths at which two canonical values differ.
fn difference(path: &str, kernel: Option<&Value>, model: Option<&Value>, out: &mut Vec<String>) {
    if kernel == model || out.len() >= DIFFERENCE_LIMIT {
        return;
    }
    match (kernel, model) {
        (Some(Value::Object(kernel)), Some(Value::Object(model))) => {
            let keys: BTreeSet<&String> = kernel.keys().chain(model.keys()).collect();
            for key in keys {
                difference(
                    &format!("{path}.{key}"),
                    kernel.get(key),
                    model.get(key),
                    out,
                );
            }
        }
        (Some(Value::Array(kernel)), Some(Value::Array(model))) => {
            if let (Some(kernel), Some(model)) = (keyed(kernel), keyed(model)) {
                let keys: BTreeSet<&String> = kernel.keys().chain(model.keys()).collect();
                for key in keys {
                    difference(
                        &format!("{path}[{key}]"),
                        kernel.get(key).copied(),
                        model.get(key).copied(),
                        out,
                    );
                }
            } else {
                for index in 0..kernel.len().max(model.len()) {
                    difference(
                        &format!("{path}[{index}]"),
                        kernel.get(index),
                        model.get(index),
                        out,
                    );
                }
            }
        }
        _ => out.push(format!(
            "{path}: kernel {}, model {}",
            show(kernel),
            show(model)
        )),
    }
}

/// Writes the run's trace, with the kernel's outcome and state after every
/// op, to `target/lean-oracle/<seed>.json`, or `<name>.json` without a seed.
fn write_artifact(run: &Run) -> PathBuf {
    let stem = run
        .seed
        .map_or_else(|| run.name.clone(), |seed| seed.to_string());
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/lean-oracle")
        .join(format!("{stem}.json"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(
        &path,
        serde_json::to_string_pretty(&run.annotated()).unwrap(),
    )
    .unwrap();
    path
}

fn describe(run: &Run, mismatch: &Mismatch, artifact: &Path) -> String {
    let op = serde_json::to_string(&run.ops[mismatch.step]).unwrap();
    let mut message = format!(
        "the kernel and the Lean model disagree on trace {} at step {}\n  op: {op}\n",
        run.name, mismatch.step
    );
    if mismatch.kernel_accepted != mismatch.model_accepted {
        writeln!(
            message,
            "  the kernel {} it and the model {} it",
            verdict(mismatch.kernel_accepted),
            verdict(mismatch.model_accepted)
        )
        .unwrap();
    }
    for difference in &mismatch.differences {
        writeln!(message, "  {difference}").unwrap();
    }
    writeln!(message, "  trace written to {}", artifact.display()).unwrap();
    message
}

/// Replays the run in the model and requires agreement at every step.
fn check(oracle: &Path, run: &Run) {
    let model = replay_in_model(oracle, run).unwrap_or_else(|failure| {
        let artifact = write_artifact(run);
        panic!("{failure}\n  trace written to {}", artifact.display())
    });
    if let Some(mismatch) = first_mismatch(run, &model) {
        let artifact = write_artifact(run);
        panic!("{}", describe(run, &mismatch, &artifact));
    }
}

// Committed traces.

fn committed_traces(directory: &str) -> Vec<Trace> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join(directory);
    let Ok(entries) = std::fs::read_dir(&directory) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect();
    paths.sort();
    paths
        .iter()
        .map(|path| {
            let text = std::fs::read_to_string(path).unwrap();
            serde_json::from_str(&text)
                .unwrap_or_else(|error| panic!("{} is not a trace: {error}", path.display()))
        })
        .collect()
}

/// Replays a committed trace on the kernel under its recorded identities,
/// checking its digest table and every expectation it states.
fn replay_in_kernel(file: &Trace) -> Run {
    assert_eq!(file.format, FORMAT, "{}: unsupported format", file.name);
    for (payload, digest) in &file.digests {
        assert_eq!(
            &ContentDigest::compute(&unhex(payload)).to_string(),
            digest,
            "{}: the digest table entry for {payload} is not ContentDigest::compute",
            file.name
        );
    }
    let mut run = Run::new(file.name.clone(), file.seed, file.definition.clone());
    for (step, op) in file.ops.iter().enumerate() {
        if let TraceOp::Activate {
            trigger: TriggerSpec::Pkgs(inputs),
            ..
        } = op
        {
            let distinct: BTreeSet<PackageId> = inputs.iter().map(parse_package).collect();
            assert_eq!(
                distinct.len(),
                inputs.len(),
                "{}: step {step} repeats an input; a trigger names a set",
                file.name
            );
        }
        let accepted = run.record(op.clone(), Identity::Recorded);
        if let Some(expect) = op.expect() {
            assert_eq!(
                accepted,
                expect.accepted,
                "{}: the kernel {} step {step}, which the trace expects to be {}",
                file.name,
                verdict(accepted),
                verdict(expect.accepted)
            );
            if let Some(state) = &expect.state {
                assert!(
                    run.outcomes[step].state.matches(state),
                    "{}: the kernel's state after step {step} differs from the trace's",
                    file.name
                );
            }
        }
    }
    for payload in run.digests.keys() {
        assert!(
            file.digests.contains_key(payload),
            "{}: payload {payload} has no entry in the digest table",
            file.name
        );
    }
    run.digests.clone_from(&file.digests);
    run
}

#[derive(Default)]
struct Tally {
    traces: usize,
    ops: usize,
    kinds: BTreeMap<&'static str, (usize, usize)>,
}

impl Tally {
    fn add(&mut self, run: &Run) {
        self.traces += 1;
        for (op, outcome) in run.ops.iter().zip(&run.outcomes) {
            self.ops += 1;
            let (accepted, rejected) = self.kinds.entry(op.kind()).or_default();
            if outcome.accepted {
                *accepted += 1;
            } else {
                *rejected += 1;
            }
        }
    }

    fn report(&self) -> String {
        let mut report = format!(
            "the kernel and the Lean model agree on {} traces of {} ops:\n",
            self.traces, self.ops
        );
        for (kind, (accepted, rejected)) in &self.kinds {
            writeln!(
                report,
                "  {kind:<9} {accepted:>6} accepted {rejected:>6} rejected"
            )
            .unwrap();
        }
        report
    }
}

#[test]
fn kernel_and_lean_model_agree_on_random_traces() {
    let Some(oracle) = oracle() else {
        return;
    };
    let mut tally = Tally::default();
    for seed in seeds() {
        let run = random_run(seed);
        check(&oracle, &run);
        tally.add(&run);
    }
    println!("{}", tally.report());
    for kind in ["activate", "transfer", "retire"] {
        let (accepted, rejected) = tally.kinds.get(kind).copied().unwrap_or_default();
        assert!(
            accepted > 0 && rejected > 0,
            "{kind}: {accepted} accepted and {rejected} rejected; both must occur"
        );
    }
}

#[test]
fn kernel_and_lean_model_agree_on_regression_traces() {
    let traces = committed_traces("tests/lean_traces");
    assert!(
        !traces.is_empty(),
        "no regression traces in tests/lean_traces"
    );
    let runs: Vec<Run> = traces
        .iter()
        .map(|trace| {
            assert!(
                trace.known_disagreement.is_none(),
                "{}: a known disagreement belongs in tests/lean_traces/disagreements",
                trace.name
            );
            replay_in_kernel(trace)
        })
        .collect();
    let Some(oracle) = oracle() else {
        return;
    };
    for run in &runs {
        check(&oracle, run);
    }
}

#[test]
fn known_disagreements_still_reproduce() {
    let traces = committed_traces("tests/lean_traces/disagreements");
    if traces.is_empty() {
        return;
    }
    let runs: Vec<(Run, KnownDisagreement)> = traces
        .iter()
        .map(|trace| {
            let known = trace.known_disagreement.clone().unwrap_or_else(|| {
                panic!(
                    "{}: a trace in tests/lean_traces/disagreements names its known_disagreement",
                    trace.name
                )
            });
            (replay_in_kernel(trace), known)
        })
        .collect();
    let Some(oracle) = oracle() else {
        return;
    };
    for (run, known) in &runs {
        let model = replay_in_model(&oracle, run).unwrap_or_else(|failure| panic!("{failure}"));
        let Some(mismatch) = first_mismatch(run, &model) else {
            panic!(
                "{}: the known disagreement no longer reproduces; the kernel and the model \
                 now agree, so move the trace to tests/lean_traces without known_disagreement",
                run.name
            );
        };
        if mismatch.step != known.step {
            let artifact = write_artifact(run);
            panic!(
                "{}: the known disagreement moved from step {}\n{}",
                run.name,
                known.step,
                describe(run, &mismatch, &artifact)
            );
        }
    }
}
