//! Random exploration. Choices read the current kernel's graph and the run's
//! live work, index packages in birth order, and lean toward admissible
//! operations, then perturb some into each way an operation can fail. The
//! structural reading only biases choices: the kernel and the model decide
//! every outcome.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{ActivationId, Authority, Kernel, PackageId, PackageRecord};

use crate::fixtures::{
    Annotation, LATE_CONTRACTS, LATE_NODE_TYPE, LATE_OBJECT_TYPE, LATE_TAG, Profile, annotation_of,
    profile_of,
};
use crate::format::{
    AuthoritySpec, ContractSpec, Destination, EditSpec, EmissionSpec, FragmentSpec, NodeSpec,
    RootSpec, SchemaSpec, TraceOp, TransitionSpec, TriggerSpec, Validator, authority, hex,
};
use crate::run::{
    DENIED, Identity, MANAGER, Run, activate, extend, pkgs, retire, rewrite_by, transfer,
};

/// Deterministic xorshift choices.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
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

fn tag_ids(authority: &Authority) -> Vec<String> {
    authority.tags().map(|tag| tag.id().to_owned()).collect()
}

fn same_set(left: &[String], right: &[String]) -> bool {
    left.iter().collect::<BTreeSet<_>>() == right.iter().collect::<BTreeSet<_>>()
}

// Structural reading of the current kernel.

fn nodes(kernel: &Kernel) -> Vec<String> {
    kernel
        .graph()
        .nodes()
        .iter()
        .map(|node| node.id().to_owned())
        .collect()
}

fn edge_ids(kernel: &Kernel) -> Vec<String> {
    kernel
        .graph()
        .edges()
        .iter()
        .map(|edge| edge.id().to_owned())
        .collect()
}

fn leaving(kernel: &Kernel, node: &str) -> Vec<String> {
    kernel
        .graph()
        .edges()
        .iter()
        .filter(|edge| edge.source() == node)
        .map(|edge| edge.id().to_owned())
        .collect()
}

fn validator<'a>(run: &'a Run, contract: &str) -> Option<&'a Validator> {
    run.registry.validators().get(contract)
}

fn edge_validator<'a>(run: &'a Run, edge: &str) -> Option<&'a Validator> {
    let contract = run
        .kernel
        .edge_definition(edge)?
        .package_contract()
        .to_owned();
    validator(run, &contract)
}

fn result_validator<'a>(run: &'a Run, node: &str) -> Option<&'a Validator> {
    let contract = run
        .kernel
        .node_definition(node)?
        .result_contract()
        .to_owned();
    validator(run, &contract)
}

/// Whether `edge` would carry a package of this type and authority.
fn fits(kernel: &Kernel, edge: &str, object_type: Option<&str>, tags: &[String]) -> bool {
    kernel.edge_definition(edge).is_some_and(|definition| {
        definition.matches_authority(&authority(tags))
            && object_type.is_none_or(|object_type| {
                kernel
                    .contract(definition.package_contract())
                    .is_some_and(|contract| contract.object_type() == object_type)
            })
    })
}

fn is_all(kernel: &Kernel, node: &str) -> bool {
    kernel
        .node_definition(node)
        .is_some_and(|definition| definition.ingress_mode() == ontography::IngressMode::All)
}

/// One random op. Consumption and transfer need live work they could act on;
/// without it they usually yield to a root, which births more.
pub fn random_step(run: &mut Run, rng: &mut Rng, plans: bool) {
    let delivered = !run.live(|record| record.delivery().is_some()).is_empty();
    let transferable = !transferable(run).is_empty();
    match rng.below(100) {
        22..=47 if delivered || rng.chance(20) => random_consumption(run, rng),
        48..=63 if transferable || rng.chance(20) => random_transfer(run, rng),
        64..=73 => random_retirement(run, rng),
        74..=77 => random_stray(run, rng),
        78..=90 => {
            let op = random_rewrite(run, rng);
            run.record(op, Identity::Drawn);
        }
        91..=96 => {
            let op = random_extension(run, rng);
            run.record(op, Identity::Drawn);
        }
        97..=99 if plans => random_plan(run, rng),
        _ => random_root(run, rng),
    }
}

/// Zero to three births at `node` under the governing authority `governing`,
/// mostly shaped to be admissible, and outbound ones mostly shaped for a
/// later transfer along an edge leaving `node`.
fn random_emissions(
    run: &Run,
    rng: &mut Rng,
    node: &str,
    governing: &[String],
) -> Vec<EmissionSpec> {
    let kernel = &run.kernel;
    let leaving = leaving(kernel, node);
    let rules: Vec<Vec<String>> = kernel
        .authority_transitions()
        .iter()
        .filter(|rule| rule.node_id() == node && same_set(&tag_ids(rule.from()), governing))
        .map(|rule| tag_ids(rule.to()))
        .collect();
    let object_types: Vec<String> = kernel.schema().object_types().map(str::to_owned).collect();
    let tags: Vec<String> = kernel
        .schema()
        .authority_tags()
        .map(|tag| tag.id().to_owned())
        .collect();
    let edges = edge_ids(kernel);
    let count = rng.below(4);
    (0..count)
        .map(|_| {
            let (output, carried) = match (rng.below(100), rng.pick(&rules)) {
                (0..=83, _) => (AuthoritySpec::Carry, governing.to_vec()),
                (84..=95, Some(target)) => {
                    (AuthoritySpec::Transition(target.clone()), target.clone())
                }
                (84..=97, _) => (
                    AuthoritySpec::Transition(governing.to_vec()),
                    governing.to_vec(),
                ),
                _ => {
                    let target = rng.subset(&tags);
                    (AuthoritySpec::Transition(target.clone()), target)
                }
            };
            let fitting: Vec<&String> = leaving
                .iter()
                .filter(|edge| fits(kernel, edge, None, &carried))
                .collect();
            let edge = match rng.below(100) {
                0..=64 => rng.pick(&fitting).map(|edge| (*edge).clone()),
                65..=68 => rng.pick(&leaving).cloned(),
                69..=71 => rng.pick(&edges).cloned(),
                72 => Some("zz".to_owned()),
                _ => None,
            };
            let (destination, payload) = if let Some(edge) = edge {
                let payload = payload_for(rng, edge_validator(run, &edge));
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
                    .and_then(|edge| kernel.edge_definition(edge))
                    .and_then(|definition| kernel.contract(definition.package_contract()));
                match contract {
                    Some(contract) => (
                        Destination::Outbound(contract.object_type().to_owned()),
                        payload_for(rng, validator(run, contract.id())),
                    ),
                    None => (
                        Destination::Outbound(rng.pick(&object_types).unwrap().clone()),
                        random_payload(rng),
                    ),
                }
            };
            EmissionSpec {
                destination,
                authority: output,
                payload: hex(&payload),
            }
        })
        .collect()
}

fn random_root(run: &mut Run, rng: &mut Rng) {
    let kernel = Arc::clone(&run.kernel);
    let rootable: Vec<String> = kernel
        .roots()
        .iter()
        .map(|root| root.node_id().to_owned())
        .collect();
    let all = nodes(&kernel);
    let node = match (rng.below(100), rng.pick(&rootable)) {
        (0..=84, Some(node)) => node.clone(),
        (0..=96, _) => rng
            .pick(&all)
            .cloned()
            .unwrap_or_else(|| "nowhere".to_owned()),
        _ => "nowhere".to_owned(),
    };
    let tags: Vec<String> = kernel
        .schema()
        .authority_tags()
        .map(|tag| tag.id().to_owned())
        .collect();
    let ceiling = kernel.root_ceiling(&node).map(tag_ids);
    let governing = match (rng.below(100), ceiling) {
        (0..=84, Some(ceiling)) => rng.subset(&ceiling),
        (0..=95, _) => rng.subset(&tags),
        _ => {
            let mut chosen = rng.subset(&tags);
            chosen.push("ghost".to_owned());
            chosen
        }
    };
    let emissions = random_emissions(run, rng, &node, &governing);
    let result = payload_for(rng, result_validator(run, &node));
    let op = activate(
        TriggerSpec::Orig {
            node,
            authority: governing,
        },
        &result,
        emissions,
    );
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
    let kernel = &run.kernel;
    let mut joins = Vec::new();
    for node in kernel.node_definitions() {
        if node.ingress_mode() != ontography::IngressMode::All {
            continue;
        }
        let incoming = kernel
            .graph()
            .incoming_edge_ids(node.node_id())
            .map_or(0, BTreeSet::len);
        let mut heads: BTreeMap<&Authority, BTreeMap<&str, PackageId>> = BTreeMap::new();
        for id in
            run.live(|record| record.holder() == node.node_id() && record.delivery().is_some())
        {
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
    let kernel = Arc::clone(&run.kernel);
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
            if is_all(&kernel, &node) {
                let anchor_edge = record.delivery().unwrap().edge_id();
                for edge in kernel
                    .graph()
                    .edges()
                    .iter()
                    .filter(|edge| edge.target() == node && edge.id() != anchor_edge)
                {
                    let candidates: Vec<PackageId> = at_node
                        .iter()
                        .copied()
                        .filter(|id| {
                            let candidate = run.state.package(*id).unwrap();
                            candidate.delivery().unwrap().edge_id() == edge.id()
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
            (node, tag_ids(record.authority()))
        }
        _ => {
            for _ in 0..=rng.below(2) {
                inputs.push(any_package(run, rng));
            }
            let all = nodes(&kernel);
            (
                rng.pick(&all)
                    .cloned()
                    .unwrap_or_else(|| "nowhere".to_owned()),
                Vec::new(),
            )
        }
    };
    let emissions = random_emissions(run, rng, &node, &governing);
    let result = payload_for(rng, result_validator(run, &node));
    run.record(activate(pkgs(&inputs), &result, emissions), Identity::Drawn);
}

/// The edges leaving a package's producer that would carry it: its type and
/// authority fit, and the contract accepts its committed bytes.
fn carrying_edges(run: &Run, record: &PackageRecord) -> Vec<String> {
    let tags = tag_ids(record.authority());
    let committed = run.payloads.get(&record.content_digest());
    leaving(&run.kernel, record.producer_node())
        .into_iter()
        .filter(|edge| {
            fits(&run.kernel, edge, Some(record.object_type()), &tags)
                && committed.is_some_and(|bytes| {
                    edge_validator(run, edge).is_some_and(|validator| validator.accepts(bytes))
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
            leaving(&run.kernel, record.producer_node()),
        )
    });
    let edges = edge_ids(&run.kernel);
    let edge = match rng.below(100) {
        0..=69 => rng.pick(&carrying).or_else(|| rng.pick(&leaving)).cloned(),
        70..=84 => rng.pick(&leaving).cloned(),
        _ => None,
    }
    .unwrap_or_else(|| match rng.pick(&edges) {
        Some(edge) if rng.chance(90) => edge.clone(),
        _ => "zz".to_owned(),
    });
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
    let edges = edge_ids(&run.kernel);
    let op = match rng.below(4) {
        0 => activate(pkgs(&[]), b"", Vec::new()),
        1 => activate(pkgs(&[package]), b"", Vec::new()),
        2 => {
            let edge = rng.pick(&edges).cloned().unwrap_or_else(|| "zz".to_owned());
            transfer(package, &edge, b"ok")
        }
        _ => retire(package, None),
    };
    run.record(op, Identity::Drawn);
}

// Rewrites.

/// An edit under construction: the removals as sets, and the fragment added.
#[derive(Default)]
struct Draft {
    remove_nodes: BTreeSet<String>,
    remove_edges: BTreeSet<String>,
    add: FragmentSpec,
}

impl Draft {
    /// Removes `node` with every edge touching it.
    fn drop_node(&mut self, kernel: &Kernel, node: &str) {
        self.remove_nodes.insert(node.to_owned());
        self.remove_edges.extend(incident(kernel, node));
    }

    fn finish(self) -> EditSpec {
        EditSpec {
            remove_nodes: self.remove_nodes.into_iter().collect(),
            remove_edges: self.remove_edges.into_iter().collect(),
            add: self.add,
        }
    }
}

fn incident(kernel: &Kernel, node: &str) -> Vec<String> {
    kernel
        .graph()
        .edges()
        .iter()
        .filter(|edge| edge.source() == node || edge.target() == node)
        .map(|edge| edge.id().to_owned())
        .collect()
}

fn types_of(kernel: &Kernel, node: &str) -> BTreeSet<String> {
    profile_of(kernel, node).map_or_else(BTreeSet::new, |profile| profile.types().clone())
}

/// The kind of a random current node, sometimes carrying a type only an
/// extension adds.
fn node_kind(run: &Run, rng: &mut Rng) -> Option<Profile> {
    let kernel = &run.kernel;
    let profile = profile_of(kernel, rng.pick(&nodes(kernel))?)?;
    Some(if rng.chance(5) {
        profile.with_type(LATE_NODE_TYPE)
    } else {
        profile
    })
}

/// The kind of a random current edge: usually as it is, sometimes with a
/// contract that rejects every payload (which retires waiting work it would
/// have carried), and sometimes needing a contract or tag only an extension
/// adds.
fn edge_kind(run: &Run, rng: &mut Rng) -> Option<Annotation> {
    let kernel = &run.kernel;
    let annotation = annotation_of(kernel, rng.pick(&edge_ids(kernel))?)?;
    let rejecting = kernel
        .contracts()
        .iter()
        .find(|contract| validator(run, contract.id()) == Some(&Validator::RejectAll))
        .map_or("late_deny", |contract| contract.id())
        .to_owned();
    Some(match rng.below(100) {
        0..=74 => annotation,
        75..=89 => annotation.with_contract(&rejecting),
        90..=94 => annotation.with_contract("late"),
        _ => annotation.with_tag(LATE_TAG),
    })
}

/// A current node that may be the source (or, with `source` false, the
/// target) of an edge of `kind` whose other end has `other` types: usually
/// one the kind's requirements admit, occasionally any.
fn endpoint(
    run: &Run,
    rng: &mut Rng,
    kind: &Annotation,
    source: bool,
    other: &BTreeSet<String>,
) -> Option<String> {
    let kernel = &run.kernel;
    let all = nodes(kernel);
    let fitting: Vec<String> = all
        .iter()
        .filter(|node| {
            let types = types_of(kernel, node);
            if source {
                kind.fits(&types, other)
            } else {
                kind.fits(other, &types)
            }
        })
        .cloned()
        .collect();
    match rng.pick(&fitting) {
        Some(node) if rng.chance(90) => Some(node.clone()),
        _ => rng.pick(&all).cloned(),
    }
}

/// A holder of live outbound work, whose outgoing edges an edit may change.
fn waiting_holder(run: &Run, rng: &mut Rng) -> Option<String> {
    let holders: Vec<String> = run
        .live(|record| record.delivery().is_none())
        .into_iter()
        .map(|id| run.state.package(id).unwrap().holder().to_owned())
        .collect();
    rng.pick(&holders).cloned()
}

/// An edge added between current nodes, often from a holder of waiting work,
/// whose packages the kernel then rechecks against the holder's new outgoing
/// edges.
fn mend(run: &mut Run, rng: &mut Rng, draft: &mut Draft) {
    let Some(kind) = edge_kind(run, rng) else {
        return;
    };
    let source = match waiting_holder(run, rng) {
        Some(holder) if rng.chance(45) => Some(holder),
        _ => endpoint(run, rng, &kind, true, &BTreeSet::new()),
    };
    let Some(source) = source else {
        return;
    };
    let source_types = types_of(&run.kernel, &source);
    let target = if rng.chance(8) {
        Some(source.clone())
    } else {
        endpoint(run, rng, &kind, false, &source_types)
    };
    if let Some(target) = target {
        let id = run.fresh_name("e");
        kind.connect(&mut draft.add, &id, &source, &target);
    }
}

/// A node added of a current kind, sometimes wired to current nodes.
fn spawn(run: &mut Run, rng: &mut Rng, draft: &mut Draft) {
    let Some(profile) = node_kind(run, rng) else {
        return;
    };
    let id = run.fresh_name("n");
    profile.place(&mut draft.add, &id);
    let types = profile.types().clone();
    if rng.chance(50)
        && let Some(kind) = edge_kind(run, rng)
        && let Some(source) = endpoint(run, rng, &kind, true, &types)
    {
        let edge = run.fresh_name("e");
        kind.connect(&mut draft.add, &edge, &source, &id);
    }
    if rng.chance(50)
        && let Some(kind) = edge_kind(run, rng)
        && let Some(target) = endpoint(run, rng, &kind, false, &types)
    {
        let edge = run.fresh_name("e");
        kind.connect(&mut draft.add, &edge, &id, &target);
    }
}

/// A node inserted on a current edge: the edge usually removed, which at an
/// `All` receiver retires the receipts it delivered, and a node of the
/// target's kind added between its ends.
fn stage(run: &mut Run, rng: &mut Rng, draft: &mut Draft) {
    let kernel = Arc::clone(&run.kernel);
    let Some(edge) = rng.pick(kernel.graph().edges()).cloned() else {
        return;
    };
    let (Some(kind), Some(profile)) = (
        annotation_of(&kernel, edge.id()),
        profile_of(&kernel, edge.target()),
    ) else {
        return;
    };
    if rng.chance(75) {
        draft.remove_edges.insert(edge.id().to_owned());
    }
    let node = run.fresh_name("n");
    profile.place(&mut draft.add, &node);
    let (into, onward) = (run.fresh_name("e"), run.fresh_name("e"));
    kind.connect(&mut draft.add, &into, edge.source(), &node);
    kind.connect(&mut draft.add, &onward, &node, edge.target());
}

/// A node removed with its incident edges, sometimes bridged: an edge added
/// from one of its predecessors to one of its successors.
fn drop_node(run: &mut Run, rng: &mut Rng, draft: &mut Draft) {
    let kernel = Arc::clone(&run.kernel);
    let Some(node) = rng.pick(&nodes(&kernel)).cloned() else {
        return;
    };
    draft.drop_node(&kernel, &node);
    if !rng.chance(50) {
        return;
    }
    let edges = kernel.graph().edges();
    let incoming: Vec<_> = edges
        .iter()
        .filter(|edge| edge.target() == node && edge.source() != node)
        .collect();
    let outgoing: Vec<_> = edges
        .iter()
        .filter(|edge| edge.source() == node && edge.target() != node)
        .collect();
    if let (Some(into), Some(onward)) = (rng.pick(&incoming), rng.pick(&outgoing))
        && let Some(kind) = annotation_of(&kernel, into.id())
    {
        let id = run.fresh_name("e");
        kind.connect(&mut draft.add, &id, into.source(), onward.target());
    }
}

/// A current edge removed.
fn cut(run: &Run, rng: &mut Rng, draft: &mut Draft) {
    if let Some(edge) = rng.pick(&edge_ids(&run.kernel)) {
        draft.remove_edges.insert(edge.clone());
    }
}

/// Identities of the run's lifetime that are no longer current.
fn removed_ids(current: &[String], used: impl Iterator<Item = String>) -> Vec<String> {
    used.filter(|id| !current.contains(id)).collect()
}

/// One of the ways an edit can fail, applied to an otherwise shaped edit.
fn perturb(run: &mut Run, rng: &mut Rng, draft: &mut Draft) {
    let kernel = Arc::clone(&run.kernel);
    let current_nodes = nodes(&kernel);
    let current_edges = edge_ids(&kernel);
    let used_nodes: Vec<String> = run
        .state
        .used_node_ids()
        .iter()
        .map(ToString::to_string)
        .collect();
    let used_edges: Vec<String> = run
        .state
        .used_edge_ids()
        .iter()
        .map(ToString::to_string)
        .collect();
    let survivors: Vec<String> = current_nodes
        .iter()
        .filter(|node| !draft.remove_nodes.contains(*node))
        .cloned()
        .collect();
    match rng.below(10) {
        // A removal the graph cannot make: never born, or already removed.
        0 => {
            let removed = removed_ids(&current_nodes, used_nodes.into_iter());
            let node = rng
                .pick(&removed)
                .cloned()
                .unwrap_or_else(|| "ghost".to_owned());
            draft.remove_nodes.insert(node);
        }
        1 => {
            let removed = removed_ids(&current_edges, used_edges.into_iter());
            let edge = rng
                .pick(&removed)
                .cloned()
                .unwrap_or_else(|| "zz".to_owned());
            draft.remove_edges.insert(edge);
        }
        // A removed node left with an incident edge.
        2 => {
            let touched: Vec<&String> = current_nodes
                .iter()
                .filter(|node| !incident(&kernel, node).is_empty())
                .collect();
            if let Some(node) = rng.pick(&touched) {
                draft.drop_node(&kernel, node);
                let kept = rng.pick(&incident(&kernel, node)).cloned().unwrap();
                draft.remove_edges.remove(&kept);
            }
        }
        // An added node or edge reusing an identity of the run.
        3 => {
            if let (Some(profile), Some(used)) = (node_kind(run, rng), rng.pick(&used_nodes)) {
                profile.place(&mut draft.add, used);
            }
        }
        4 => {
            let (Some(kind), Some(used)) = (edge_kind(run, rng), rng.pick(&used_edges)) else {
                return;
            };
            if let (Some(source), Some(target)) =
                (rng.pick(&current_nodes), rng.pick(&current_nodes))
            {
                kind.connect(&mut draft.add, used, source, target);
            }
        }
        // An empty identity.
        5 => {
            if let Some(profile) = node_kind(run, rng) {
                profile.place(&mut draft.add, "");
            }
        }
        // An annotation of a surviving node or edge.
        6 => {
            let Some(node) = rng.pick(&survivors) else {
                return;
            };
            let profile = profile_of(&kernel, node).unwrap();
            let tags: Vec<String> = kernel
                .schema()
                .authority_tags()
                .map(|tag| tag.id().to_owned())
                .collect();
            match rng.below(3) {
                0 => {
                    let mut scratch = FragmentSpec::default();
                    profile.place(&mut scratch, node);
                    draft.add.node_definitions.extend(scratch.node_definitions);
                }
                1 => draft.add.roots.push(RootSpec {
                    node: node.clone(),
                    ceiling: rng.subset(&tags),
                }),
                _ => draft.add.transitions.push(TransitionSpec {
                    node: node.clone(),
                    source: rng.subset(&tags),
                    target: rng.subset(&tags),
                }),
            }
        }
        7 => {
            if let Some(edge) = rng.pick(&current_edges) {
                let kind = annotation_of(&kernel, edge).unwrap();
                draft.add.edge_definitions.push(kind.definition(edge));
            }
        }
        // A fragment admission refuses: a node added twice, an added node
        // without a definition, or an added edge ending at a node the edit
        // removes or the graph lacks.
        8 => {
            if let Some(repeated) = draft.add.nodes.first().cloned() {
                let definition: Vec<NodeSpec> = draft
                    .add
                    .node_definitions
                    .iter()
                    .filter(|definition| definition.node == repeated)
                    .cloned()
                    .collect();
                draft.add.nodes.push(repeated);
                draft.add.node_definitions.extend(definition);
            } else {
                draft.add.nodes.push(run.fresh_name("n"));
            }
        }
        _ => {
            let (Some(kind), Some(source)) = (edge_kind(run, rng), rng.pick(&current_nodes)) else {
                return;
            };
            let target = rng
                .pick(&draft.remove_nodes.iter().cloned().collect::<Vec<_>>())
                .cloned()
                .unwrap_or_else(|| "nowhere".to_owned());
            let id = run.fresh_name("e");
            kind.connect(&mut draft.add, &id, source, &target);
        }
    }
}

/// Evidence mapping each known commitment to another payload's bytes.
fn corrupted(run: &Run) -> BTreeMap<String, String> {
    let known: Vec<(String, Vec<u8>)> = run
        .payloads
        .iter()
        .map(|(digest, bytes)| (digest.to_string(), bytes.clone()))
        .collect();
    known
        .iter()
        .enumerate()
        .map(|(at, (digest, bytes))| {
            let other = &known[(at + 1) % known.len()].1;
            let offered = if other == bytes {
                b"\xff\xff".to_vec()
            } else {
                other.clone()
            };
            (digest.clone(), hex(&offered))
        })
        .collect()
}

/// A rewrite: usually an edit of one or a few shapes built from the current
/// graph's own kinds, with complete evidence, asked by the manager;
/// sometimes perturbed into a failing edit, offered missing or mismatched
/// evidence, or asked by the principal the policy refuses.
fn random_rewrite(run: &mut Run, rng: &mut Rng) -> TraceOp {
    let mut draft = Draft::default();
    let shapes = match rng.below(100) {
        0..=3 => 0,
        4..=79 => 1,
        _ => 2 + rng.below(2),
    };
    for _ in 0..shapes {
        match rng.below(100) {
            0..=17 => cut(run, rng, &mut draft),
            18..=45 => mend(run, rng, &mut draft),
            46..=61 => spawn(run, rng, &mut draft),
            62..=79 => stage(run, rng, &mut draft),
            _ => drop_node(run, rng, &mut draft),
        }
    }
    if rng.chance(15) {
        perturb(run, rng, &mut draft);
    }
    let evidence = match rng.below(100) {
        0..=84 => run.known_evidence(),
        85..=92 => BTreeMap::new(),
        _ => corrupted(run),
    };
    let principal = if rng.chance(3) { DENIED } else { MANAGER };
    rewrite_by(principal, draft.finish(), evidence)
}

// Extensions.

fn current_schema(kernel: &Kernel) -> SchemaSpec {
    SchemaSpec {
        node_types: kernel.schema().node_types().map(str::to_owned).collect(),
        object_types: kernel.schema().object_types().map(str::to_owned).collect(),
        tags: kernel
            .schema()
            .authority_tags()
            .map(|tag| tag.id().to_owned())
            .collect(),
    }
}

fn current_contracts(kernel: &Kernel) -> Vec<ContractSpec> {
    kernel
        .contracts()
        .iter()
        .map(|contract| ContractSpec {
            id: contract.id().to_owned(),
            object_type: contract.object_type().to_owned(),
        })
        .collect()
}

fn add(items: &mut Vec<String>, item: &str) {
    if !items.iter().any(|existing| existing == item) {
        items.push(item.to_owned());
    }
}

/// An extension: usually late vocabulary and contracts added, sometimes
/// nothing added, vocabulary or a contract removed, or a contract's object
/// type changed.
fn random_extension(run: &mut Run, rng: &mut Rng) -> TraceOp {
    let kernel = Arc::clone(&run.kernel);
    let mut schema = current_schema(&kernel);
    let mut contracts = current_contracts(&kernel);
    match rng.below(10) {
        0..=5 => {
            for (items, item) in [
                (&mut schema.node_types, LATE_NODE_TYPE),
                (&mut schema.object_types, LATE_OBJECT_TYPE),
                (&mut schema.tags, LATE_TAG),
            ] {
                if rng.chance(40) {
                    add(items, item);
                }
            }
            for (id, object_type, _) in LATE_CONTRACTS {
                if rng.chance(35) && contracts.iter().all(|contract| contract.id != id) {
                    contracts.push(ContractSpec {
                        id: id.to_owned(),
                        object_type: object_type.to_owned(),
                    });
                }
            }
        }
        6 => {}
        7 => {
            let lists = [
                &mut schema.node_types,
                &mut schema.object_types,
                &mut schema.tags,
            ];
            let list = lists.into_iter().nth(rng.below(3)).unwrap();
            if !list.is_empty() {
                list.remove(rng.below(list.len()));
            }
        }
        8 if !contracts.is_empty() => {
            contracts.remove(rng.below(contracts.len()));
        }
        _ => {
            if let Some(contract) = contracts.first_mut() {
                let other = schema
                    .object_types
                    .iter()
                    .find(|object_type| **object_type != contract.object_type)
                    .cloned()
                    .unwrap_or_else(|| LATE_OBJECT_TYPE.to_owned());
                contract.object_type = other;
            }
        }
    }
    extend(schema, contracts)
}

/// A rewrite or extension prepared, an unrelated op run, then the plan
/// committed: stale when the op changed the state, current otherwise.
fn random_plan(run: &mut Run, rng: &mut Rng) {
    let op = if rng.chance(70) {
        random_rewrite(run, rng)
    } else {
        random_extension(run, rng)
    };
    if let Some(plan) = run.plan(op) {
        random_step(run, rng, false);
        run.commit_plan(plan);
    }
}
