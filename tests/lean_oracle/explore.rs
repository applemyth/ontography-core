//! Random exploration. Choices read the current kernel's graph and the run's
//! live work, index packages in birth order, and lean toward admissible
//! operations, then perturb some into each way an operation can fail. The
//! structural reading only biases choices: the kernel and the model decide
//! every outcome.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{ActivationId, Authority, Kernel, PackageId, PackageRecord};

use crate::fixtures::{
    LATE_CONTRACTS, LATE_NODE_TYPE, LATE_OBJECT_TYPE, LATE_TAG, annotation_in, annotation_of,
    profile_in, profile_of,
};
use crate::format::{
    AuthoritySpec, ContractSpec, Destination, EmissionSpec, MatchSpec, ProductionSpec, SchemaSpec,
    TraceOp, TriggerSpec, Validator, authority, hex,
};
use crate::run::{Identity, Run, activate, extend, pkgs, retire, rewrite, transfer};

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

/// Whether a match deletes a node that keeps an unmatched incident edge.
fn dangles(kernel: &Kernel, production: &ProductionSpec, matching: &MatchSpec) -> bool {
    let kept: BTreeSet<&String> = production.interface_nodes.iter().collect();
    let kept_edges: BTreeSet<&String> = production.interface_edges.iter().collect();
    let deleted: BTreeSet<&str> = matching
        .nodes
        .iter()
        .filter(|(symbol, _)| !kept.contains(symbol))
        .map(|(_, host)| host.as_str())
        .collect();
    let deleted_edges: BTreeSet<&str> = matching
        .edges
        .iter()
        .filter(|(symbol, _)| !kept_edges.contains(symbol))
        .map(|(_, host)| host.as_str())
        .collect();
    kernel.graph().edges().iter().any(|edge| {
        (deleted.contains(edge.source()) || deleted.contains(edge.target()))
            && !deleted_edges.contains(edge.id())
    })
}

/// A legal match, preferring one whose deletions leave nothing dangling when
/// a few tries find one.
fn admissible_match(
    run: &mut Run,
    production: &ProductionSpec,
    rng: &mut Rng,
) -> Option<MatchSpec> {
    let mut first = None;
    for _ in 0..8 {
        let matching = legal_match(run, production, rng)?;
        if !dangles(&run.kernel, production, &matching) {
            return Some(matching);
        }
        first.get_or_insert(matching);
    }
    first
}

/// A match of `production` the kernel should admit: each `L` edge bound to a
/// current edge of its kind between nodes of its end kinds, each other `L`
/// node to a node of its kind, all injectively, and fresh identities for
/// `R ∖ K`. `None` when the current graph has no such match.
fn legal_match(run: &mut Run, production: &ProductionSpec, rng: &mut Rng) -> Option<MatchSpec> {
    let kernel = Arc::clone(&run.kernel);
    let left = &production.left;
    let mut bound: BTreeMap<String, String> = BTreeMap::new();
    let mut bound_edges: BTreeMap<String, String> = BTreeMap::new();
    for pattern in &left.edges {
        let kind = annotation_in(left, &pattern.id);
        let ends = (
            profile_in(left, &pattern.source),
            profile_in(left, &pattern.target),
        );
        let candidates: Vec<&ontography::Edge> = kernel
            .graph()
            .edges()
            .iter()
            .filter(|host| {
                annotation_of(&kernel, host.id()).as_ref() == Some(&kind)
                    && !bound_edges.values().any(|id| id == host.id())
                    && profile_of(&kernel, host.source()).as_ref() == Some(&ends.0)
                    && profile_of(&kernel, host.target()).as_ref() == Some(&ends.1)
                    && bound
                        .get(&pattern.source)
                        .is_none_or(|id| id == host.source())
                    && bound
                        .get(&pattern.target)
                        .is_none_or(|id| id == host.target())
                    && (pattern.source == pattern.target) == (host.source() == host.target())
            })
            .collect();
        let host = *rng.pick(&candidates)?;
        bound.insert(pattern.source.clone(), host.source().to_owned());
        bound.insert(pattern.target.clone(), host.target().to_owned());
        bound_edges.insert(pattern.id.clone(), host.id().to_owned());
    }
    for symbol in &left.nodes {
        if bound.contains_key(symbol) {
            continue;
        }
        let kind = profile_in(left, symbol);
        let candidates: Vec<String> = nodes(&kernel)
            .into_iter()
            .filter(|id| {
                profile_of(&kernel, id).as_ref() == Some(&kind)
                    && !bound.values().any(|other| other == id)
            })
            .collect();
        let host = rng.pick(&candidates)?.clone();
        bound.insert(symbol.clone(), host);
    }
    if bound.values().collect::<BTreeSet<_>>().len() != bound.len() {
        return None;
    }
    let kept: BTreeSet<&String> = production.interface_nodes.iter().collect();
    let kept_edges: BTreeSet<&String> = production.interface_edges.iter().collect();
    let fresh_nodes = production
        .right
        .nodes
        .iter()
        .filter(|symbol| !kept.contains(symbol))
        .map(|symbol| (symbol.clone(), run.fresh_name("n")))
        .collect();
    let fresh_edges = production
        .right
        .edges
        .iter()
        .filter(|edge| !kept_edges.contains(&edge.id))
        .map(|edge| (edge.id.clone(), run.fresh_name("e")))
        .collect();
    Some(MatchSpec {
        nodes: bound.into_iter().collect(),
        edges: bound_edges.into_iter().collect(),
        fresh_nodes,
        fresh_edges,
    })
}

/// A legal match turned into one of the ways a match can fail.
fn perturb(run: &mut Run, mut matching: MatchSpec, rng: &mut Rng) -> MatchSpec {
    let kernel = Arc::clone(&run.kernel);
    let hosts = nodes(&kernel);
    let host_edges = edge_ids(&kernel);
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
    match rng.below(7) {
        // Not exact: a symbol left unbound.
        0 if !matching.nodes.is_empty() || !matching.edges.is_empty() => {
            if matching.edges.is_empty() || rng.chance(50) && !matching.nodes.is_empty() {
                matching.nodes.remove(rng.below(matching.nodes.len()));
            } else {
                matching.edges.remove(rng.below(matching.edges.len()));
            }
        }
        // Not injective: two symbols bound to one identity.
        1 if matching.nodes.len() >= 2 => {
            let first = matching.nodes[0].1.clone();
            matching.nodes[1].1 = first;
        }
        1 if matching.fresh_edges.len() >= 2 => {
            let first = matching.fresh_edges[0].1.clone();
            matching.fresh_edges[1].1 = first;
        }
        // A fresh identity used before, current or removed.
        2 if !matching.fresh_nodes.is_empty() => {
            if let Some(used) = rng.pick(&used_nodes) {
                let at = rng.below(matching.fresh_nodes.len());
                matching.fresh_nodes[at].1.clone_from(used);
            }
        }
        2 if !matching.fresh_edges.is_empty() => {
            if let Some(used) = rng.pick(&used_edges) {
                let at = rng.below(matching.fresh_edges.len());
                matching.fresh_edges[at].1.clone_from(used);
            }
        }
        // An empty identity.
        3 if !matching.fresh_nodes.is_empty() => matching.fresh_nodes[0].1.clear(),
        // A node or edge of another kind or incidence.
        4 if !matching.nodes.is_empty() => {
            if let Some(host) = rng.pick(&hosts) {
                let at = rng.below(matching.nodes.len());
                matching.nodes[at].1.clone_from(host);
            }
        }
        5 if !matching.edges.is_empty() => {
            if let Some(host) = rng.pick(&host_edges) {
                let at = rng.below(matching.edges.len());
                matching.edges[at].1.clone_from(host);
            }
        }
        // Not exact: a symbol the production does not have.
        _ => {
            if let Some(host) = rng.pick(&hosts) {
                matching.nodes.push(("W".to_owned(), host.clone()));
            }
        }
    }
    matching
}

/// A match chosen without regard to kinds, which usually fails.
fn blind_match(run: &mut Run, production: &ProductionSpec, rng: &mut Rng) -> MatchSpec {
    let kernel = Arc::clone(&run.kernel);
    let hosts = nodes(&kernel);
    let host_edges = edge_ids(&kernel);
    let mut matching = MatchSpec::default();
    for symbol in &production.left.nodes {
        if let Some(host) = rng.pick(&hosts) {
            matching.nodes.push((symbol.clone(), host.clone()));
        }
    }
    for edge in &production.left.edges {
        if let Some(host) = rng.pick(&host_edges) {
            matching.edges.push((edge.id.clone(), host.clone()));
        }
    }
    let kept: BTreeSet<&String> = production.interface_nodes.iter().collect();
    for symbol in &production.right.nodes {
        if !kept.contains(symbol) {
            matching
                .fresh_nodes
                .push((symbol.clone(), run.fresh_name("n")));
        }
    }
    let kept_edges: BTreeSet<&String> = production.interface_edges.iter().collect();
    for edge in &production.right.edges {
        if !kept_edges.contains(&edge.id) {
            matching
                .fresh_edges
                .push((edge.id.clone(), run.fresh_name("e")));
        }
    }
    matching
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

/// A rewrite request: usually a legal match of a grammar production with
/// complete evidence, sometimes a perturbed or blind match, missing or
/// mismatched evidence, or a production outside the grammar.
fn random_rewrite(run: &mut Run, rng: &mut Rng) -> TraceOp {
    if rng.chance(3) {
        return rewrite("nope", MatchSpec::default(), run.known_evidence());
    }
    let production = run.productions[rng.below(run.productions.len())].clone();
    let matching = match admissible_match(run, &production, rng) {
        Some(matching) if !rng.chance(15) => matching,
        Some(matching) => perturb(run, matching, rng),
        None => blind_match(run, &production, rng),
    };
    let evidence = match rng.below(100) {
        0..=84 => run.known_evidence(),
        85..=92 => BTreeMap::new(),
        _ => corrupted(run),
    };
    rewrite(&production.id, matching, evidence)
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
