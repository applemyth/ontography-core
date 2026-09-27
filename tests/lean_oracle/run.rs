//! One run of the kernel: operations executed against it and recorded as a
//! trace, with the kernel's outcome and canonical state after each.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, ContentDigest, Emission, ExtensionError, Kernel,
    OutputAuthority, PackageId, PackageRecord, Payload, PreparedExtension, PreparedRewrite,
    RewriteError, RewriteGrammar, State,
};

use crate::format::{
    AuthoritySpec, Canonical, ContractSpec, DefinitionSpec, Destination, EmissionSpec, Expectation,
    FORMAT, MatchSpec, ProductionSpec, Registry, SchemaSpec, Snapshot, Trace, TraceOp, TriggerSpec,
    Validator, activation_text, admit, authority, extended, grammar, hex, package_ref,
    parse_activation, parse_digest, parse_package, request, unhex,
};

/// Where an activation's identity comes from.
#[derive(Clone, Copy)]
pub enum Identity {
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

fn evidence(offered: &BTreeMap<String, String>) -> BTreeMap<ContentDigest, Payload> {
    offered
        .iter()
        .map(|(digest, bytes)| (parse_digest(digest), Arc::from(unhex(bytes))))
        .collect()
}

fn fresh_identity(state: &State) -> ActivationId {
    loop {
        let id = ActivationId::fresh();
        if state.activation(id).is_none() {
            return id;
        }
    }
}

/// The kernel's outcome of one op and its canonical state after it.
pub struct Outcome {
    pub accepted: bool,
    pub state: Snapshot,
}

/// A rewrite or extension the kernel has prepared but not committed.
pub struct Plan {
    op: TraceOp,
    prepared: Prepared,
}

enum Prepared {
    Rewrite(PreparedRewrite),
    Extension(PreparedExtension),
}

/// One run of the kernel, recorded as a trace.
pub struct Run {
    pub name: String,
    pub seed: Option<u64>,
    /// The initial definition.
    pub definition: DefinitionSpec,
    pub productions: Vec<ProductionSpec>,
    pub registry: Registry,
    pub grammar: RewriteGrammar,
    pub kernel: Arc<Kernel>,
    pub state: State,
    /// The ops as run, without expectations.
    pub ops: Vec<TraceOp>,
    pub outcomes: Vec<Outcome>,
    pub digests: BTreeMap<String, String>,
    /// Every package in birth order, whatever its status.
    pub packages: Vec<PackageId>,
    /// Every accepted activation in acceptance order.
    pub activations: Vec<ActivationId>,
    /// The bytes behind every digest an op has used.
    pub payloads: BTreeMap<ContentDigest, Vec<u8>>,
    /// Committed plans the kernel refused as stale. The model has no plans, so
    /// these are checked against the kernel alone and are not in the trace.
    pub stale: usize,
    fresh: usize,
    canonical: Canonical,
}

impl Run {
    pub fn new(
        name: String,
        seed: Option<u64>,
        definition: DefinitionSpec,
        productions: Vec<ProductionSpec>,
        validators: BTreeMap<String, Validator>,
    ) -> Self {
        let mut registry = Registry::new(validators);
        let kernel = Arc::new(
            admit(&definition, &mut registry).expect("the kernel admits the trace definition"),
        );
        let grammar = grammar(&productions);
        let state = kernel.empty_state();
        Self {
            name,
            seed,
            definition,
            productions,
            registry,
            grammar,
            kernel,
            state,
            ops: Vec::new(),
            outcomes: Vec::new(),
            digests: BTreeMap::new(),
            packages: Vec::new(),
            activations: Vec::new(),
            payloads: BTreeMap::new(),
            stale: 0,
            fresh: 0,
            canonical: Canonical::default(),
        }
    }

    /// A name no identity of this run has used.
    pub fn fresh_name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}~{}", self.fresh)
    }

    fn remember(&mut self, op: &TraceOp) {
        for payload in op.payloads() {
            let bytes = unhex(payload);
            let digest = ContentDigest::compute(&bytes);
            self.digests
                .entry(payload.to_owned())
                .or_insert_with(|| digest.to_string());
            self.payloads.entry(digest).or_insert(bytes);
        }
    }

    /// Runs one op on the kernel and reports whether it was accepted.
    fn execute(&mut self, op: &mut TraceOp, identity: Identity) -> bool {
        let kernel = Arc::clone(&self.kernel);
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
                        let (drawn, accepted) = match kernel.activate(&mut self.state, proposal) {
                            Ok(drawn) => (drawn, true),
                            Err(_) => (fresh_identity(&self.state), false),
                        };
                        *id = activation_text(drawn);
                        accepted
                    }
                    Identity::Recorded => kernel
                        .evaluate_activation(&self.state, parse_activation(id), proposal)
                        .is_ok_and(|transition| self.state.apply(&kernel, &transition).is_ok()),
                }
            }
            TraceOp::Transfer {
                package,
                edge,
                payload,
                ..
            } => kernel
                .prepare_transfer(&self.state, parse_package(package), edge, &unhex(payload))
                .and_then(|prepared| kernel.commit_transfer(&mut self.state, prepared))
                .is_ok(),
            TraceOp::Retire {
                package, evidence, ..
            } => kernel
                .retire(
                    &mut self.state,
                    parse_package(package),
                    evidence.as_deref().map(parse_activation),
                )
                .is_ok(),
            TraceOp::Rewrite { .. } | TraceOp::Extend { .. } => match self.prepare(op) {
                Some(prepared) => self.commit(prepared).is_ok(),
                None => false,
            },
        }
    }

    /// Prepares a rewrite or extension, or `None` when the kernel refuses it.
    fn prepare(&mut self, op: &TraceOp) -> Option<Prepared> {
        match op {
            TraceOp::Rewrite {
                production,
                matching,
                evidence: offered,
                ..
            } => self
                .kernel
                .prepare_rewrite(
                    &self.state,
                    &self.grammar,
                    &request(production, matching),
                    &evidence(offered),
                )
                .ok()
                .map(Prepared::Rewrite),
            TraceOp::Extend {
                schema, contracts, ..
            } => {
                let next = extended(&self.kernel, schema, contracts, &mut self.registry).ok()?;
                self.kernel
                    .prepare_extension(&self.state, Arc::new(next))
                    .ok()
                    .map(Prepared::Extension)
            }
            _ => unreachable!("only rewrites and extensions are prepared"),
        }
    }

    /// Commits a prepared change and installs the next kernel.
    fn commit(&mut self, prepared: Prepared) -> Result<(), Stale> {
        let kernel = Arc::clone(&self.kernel);
        let next = match prepared {
            Prepared::Rewrite(prepared) => kernel
                .commit_rewrite(&mut self.state, prepared)
                .map_err(|error| Stale(error == RewriteError::Stale)),
            Prepared::Extension(prepared) => kernel
                .commit_extension(&mut self.state, prepared)
                .map_err(|error| Stale(error == ExtensionError::Stale)),
        }?;
        self.kernel = next;
        Ok(())
    }

    fn log(&mut self, op: TraceOp, accepted: bool) {
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
            state: self
                .canonical
                .encode(&self.kernel, &self.state.checkpoint()),
        });
        self.ops.push(op);
    }

    /// Runs one op on the kernel and records it with the kernel's outcome and
    /// the canonical state after it.
    pub fn record(&mut self, mut op: TraceOp, identity: Identity) -> bool {
        *op.expect_mut() = None;
        self.remember(&op);
        let accepted = self.execute(&mut op, identity);
        self.log(op, accepted);
        accepted
    }

    /// Prepares a rewrite or extension to commit later. A change the kernel
    /// refuses to prepare is recorded as rejected.
    pub fn plan(&mut self, mut op: TraceOp) -> Option<Plan> {
        *op.expect_mut() = None;
        self.remember(&op);
        if let Some(prepared) = self.prepare(&op) {
            Some(Plan { op, prepared })
        } else {
            self.log(op, false);
            None
        }
    }

    /// Commits a plan. If the state has changed since preparation, the kernel
    /// must refuse the plan as stale and leave the state unchanged; the model
    /// has no plans, so the refusal is checked here and not recorded.
    /// Otherwise the plan must commit, and it is recorded.
    pub fn commit_plan(&mut self, plan: Plan) -> bool {
        let base = match &plan.prepared {
            Prepared::Rewrite(prepared) => prepared.transition().base().clone(),
            Prepared::Extension(prepared) => prepared.transition().base().clone(),
        };
        if self.state.binding() == base {
            assert!(
                self.commit(plan.prepared).is_ok(),
                "{}: a current plan must commit",
                self.name
            );
            self.log(plan.op, true);
            true
        } else {
            let before = self.state.checkpoint();
            let refused = self.commit(plan.prepared);
            assert_eq!(
                refused,
                Err(Stale(true)),
                "{}: a plan prepared before a change is stale",
                self.name
            );
            assert_eq!(
                self.state.checkpoint(),
                before,
                "{}: a refused plan leaves the state unchanged",
                self.name
            );
            self.stale += 1;
            false
        }
    }

    /// Records a prefix op that must have the stated outcome.
    pub fn want(&mut self, accepted: bool, why: &str, op: TraceOp) -> Option<ActivationId> {
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

    pub fn accept(&mut self, why: &str, op: TraceOp) {
        self.want(true, why, op);
    }

    pub fn accept_activation(&mut self, why: &str, op: TraceOp) -> ActivationId {
        self.want(true, why, op)
            .unwrap_or_else(|| panic!("{}: {why} is not an activation", self.name))
    }

    pub fn reject(&mut self, why: &str, op: TraceOp) {
        self.want(false, why, op);
    }

    /// The trace as the oracle reads it: the ops alone.
    pub fn trace(&self) -> Trace {
        Trace {
            format: FORMAT.to_owned(),
            name: self.name.clone(),
            seed: self.seed,
            known_disagreement: None,
            validators: self.registry.validators().clone(),
            digests: self.digests.clone(),
            grammar: self.productions.clone(),
            definition: self.definition.clone(),
            ops: self.ops.clone(),
        }
    }

    /// The trace with the kernel's outcome and state after every op.
    pub fn annotated(&self) -> Trace {
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
    pub fn live(&self, filter: impl Fn(&PackageRecord) -> bool) -> Vec<PackageId> {
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

    /// Every payload the run has seen, as rewrite evidence.
    pub fn known_evidence(&self) -> BTreeMap<String, String> {
        self.payloads
            .iter()
            .map(|(digest, bytes)| (digest.to_string(), hex(bytes)))
            .collect()
    }
}

/// A commit failure; `true` when the kernel refused the plan as stale.
#[derive(Debug, Eq, PartialEq)]
pub struct Stale(bool);

pub fn verdict(accepted: bool) -> &'static str {
    if accepted { "accepted" } else { "rejected" }
}

// Op constructors for the prefixes and the random explorer.

pub fn names(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

pub fn orig(node: &str, tags: &[&str]) -> TriggerSpec {
    TriggerSpec::Orig {
        node: node.to_owned(),
        authority: names(tags),
    }
}

/// The canonical input set the kernel evaluates: sorted, without repeats.
pub fn pkgs(inputs: &[PackageId]) -> TriggerSpec {
    let inputs: BTreeSet<PackageId> = inputs.iter().copied().collect();
    TriggerSpec::Pkgs(inputs.into_iter().map(package_ref).collect())
}

pub fn carry() -> AuthoritySpec {
    AuthoritySpec::Carry
}

pub fn to(tags: &[&str]) -> AuthoritySpec {
    AuthoritySpec::Transition(names(tags))
}

pub fn delivered(edge: &str, authority: AuthoritySpec, payload: &[u8]) -> EmissionSpec {
    EmissionSpec {
        destination: Destination::Delivered(edge.to_owned()),
        authority,
        payload: hex(payload),
    }
}

pub fn outbound(object_type: &str, authority: AuthoritySpec, payload: &[u8]) -> EmissionSpec {
    EmissionSpec {
        destination: Destination::Outbound(object_type.to_owned()),
        authority,
        payload: hex(payload),
    }
}

pub fn activate(trigger: TriggerSpec, result: &[u8], emissions: Vec<EmissionSpec>) -> TraceOp {
    TraceOp::Activate {
        id: String::new(),
        trigger,
        result: hex(result),
        emissions,
        expect: None,
    }
}

/// A root at `node` under `tags`.
pub fn rooted(node: &str, tags: &[&str], emissions: Vec<EmissionSpec>) -> TraceOp {
    activate(orig(node, tags), b"r", emissions)
}

/// A package trigger over `inputs`.
pub fn joined(inputs: &[PackageId], result: &[u8], emissions: Vec<EmissionSpec>) -> TraceOp {
    activate(pkgs(inputs), result, emissions)
}

pub fn transfer(package: PackageId, edge: &str, payload: &[u8]) -> TraceOp {
    TraceOp::Transfer {
        package: package_ref(package),
        edge: edge.to_owned(),
        payload: hex(payload),
        expect: None,
    }
}

pub fn retire(package: PackageId, evidence: Option<ActivationId>) -> TraceOp {
    TraceOp::Retire {
        package: package_ref(package),
        evidence: evidence.map(activation_text),
        expect: None,
    }
}

pub fn rewrite(
    production: &str,
    matching: MatchSpec,
    evidence: BTreeMap<String, String>,
) -> TraceOp {
    TraceOp::Rewrite {
        production: production.to_owned(),
        matching,
        evidence,
        expect: None,
    }
}

pub fn extend(schema: SchemaSpec, contracts: Vec<ContractSpec>) -> TraceOp {
    TraceOp::Extend {
        schema,
        contracts,
        expect: None,
    }
}

/// Symbol bindings from `(symbol, identity)` pairs.
pub fn bind(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(symbol, id)| ((*symbol).to_owned(), (*id).to_owned()))
        .collect()
}

/// The evidence offering each payload under its own commitment.
pub fn offer(payloads: &[&[u8]]) -> BTreeMap<String, String> {
    payloads
        .iter()
        .map(|bytes| (ContentDigest::compute(bytes).to_string(), hex(bytes)))
        .collect()
}

/// Evidence offering the second payload of each pair under the commitment of
/// the first.
pub fn offer_instead(pairs: &[(&[u8], &[u8])]) -> BTreeMap<String, String> {
    pairs
        .iter()
        .map(|(committed, offered)| (ContentDigest::compute(committed).to_string(), hex(offered)))
        .collect()
}

/// The first `N` outputs of an activation.
pub fn outputs<const N: usize>(activation: ActivationId) -> [PackageId; N] {
    std::array::from_fn(|index| {
        PackageId::from_parts(activation, u128::try_from(index).expect("small ordinal"))
    })
}

/// An identity no kernel draws: `ActivationId::fresh` is a version 4 UUID,
/// whose version bits are never all zero.
pub fn unknown_activation() -> ActivationId {
    ActivationId::from_u128(7)
}

pub fn unknown_package() -> PackageId {
    PackageId::from_parts(unknown_activation(), 0)
}
