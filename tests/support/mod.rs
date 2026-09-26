//! Rewrite fixtures shared by the ported calculus suites: a five-contract
//! vocabulary, root-driven package births, and identity-symbol productions.

use ontography::{
    ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract, ContractViolation,
    DefinitionId, Edge, EdgeDefinition, Emission, Graph, Kernel, Node, NodeDefinition,
    OutputAuthority, PackageId, Payload, RewriteFragment, RewriteGrammar, RewriteMatch,
    RewriteProduction, RewriteRequest, RootRule, Schema, State,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}
pub fn authority() -> Authority {
    Authority::new([tag("run")])
}
pub fn payload() -> Payload {
    Arc::from(b"payload".as_slice())
}
pub fn evidence() -> BTreeMap<ContentDigest, Payload> {
    BTreeMap::from([(ContentDigest::compute(&payload()), payload())])
}
pub fn names(items: &[&str]) -> BTreeSet<Arc<str>> {
    items.iter().map(|id| Arc::from(*id)).collect()
}
pub fn bindings(items: &[&str]) -> BTreeMap<Arc<str>, Arc<str>> {
    items
        .iter()
        .map(|id| (Arc::from(*id), Arc::from(*id)))
        .collect()
}

pub fn kernel(nodes: &[&str], edges: &[(&str, &str, &str, &str)]) -> Kernel {
    let contracts = vec![
        Contract::new("result", "t", |_| Ok(())).unwrap(),
        Contract::new("payload", "t", |bytes| {
            if bytes == b"payload" {
                Ok(())
            } else {
                Err(ContractViolation::new("bytes"))
            }
        })
        .unwrap(),
        Contract::new("deny", "t", |_| Err(ContractViolation::new("denied"))).unwrap(),
        Contract::new("other", "other", |_| Ok(())).unwrap(),
        Contract::new("panic", "t", |_| panic!("validator fault")).unwrap(),
    ];
    Kernel::admit(
        DefinitionId::new("rewrite-tests").unwrap(),
        Schema::new(["n"], ["t", "other"], [tag("run"), tag("other")]).unwrap(),
        Graph::new(
            nodes.iter().map(|id| Node::new(*id).unwrap()),
            edges
                .iter()
                .map(|(id, source, target, _)| Edge::new(*id, *source, *target).unwrap()),
        )
        .unwrap(),
        contracts,
        nodes
            .iter()
            .map(|id| NodeDefinition::new(*id, ["n"], "result").unwrap()),
        edges.iter().map(|(id, _, _, contract)| {
            EdgeDefinition::new(
                *id,
                ["flow"],
                ["n"],
                ["n"],
                if *contract == "unauthorized" {
                    "payload"
                } else {
                    contract
                },
                [tag(if *contract == "unauthorized" {
                    "other"
                } else {
                    "run"
                })],
            )
            .unwrap()
        }),
        [],
        nodes
            .iter()
            .map(|id| RootRule::new(*id, authority()).unwrap()),
    )
    .unwrap()
}

pub fn outbound(kernel: &Kernel, state: &mut State, node: &str) -> PackageId {
    let mut proposal = ActivationProposal::root(node, authority(), payload());
    proposal.emit(Emission::outbound("t", OutputAuthority::Carry, payload()));
    let activation = kernel.activate(state, proposal).unwrap();
    state
        .activation(activation)
        .unwrap()
        .outputs()
        .next()
        .unwrap()
}

pub fn delivered(kernel: &Kernel, state: &mut State, edge: &str) -> PackageId {
    let source = kernel.graph().edge(edge).unwrap().source();
    let mut proposal = ActivationProposal::root(source, authority(), payload());
    proposal.emit(Emission::new(edge, OutputAuthority::Carry, payload()));
    let activation = kernel.activate(state, proposal).unwrap();
    state
        .activation(activation)
        .unwrap()
        .outputs()
        .next()
        .unwrap()
}

pub fn rule(
    id: &str,
    left: &Kernel,
    right: &Kernel,
    interface_nodes: &[&str],
    interface_edges: &[&str],
) -> (RewriteProduction, RewriteRequest) {
    let interface_nodes = names(interface_nodes);
    let interface_edges = names(interface_edges);
    let matching = RewriteMatch::new(
        left.graph()
            .nodes()
            .iter()
            .map(|node| (Arc::from(node.id()), Arc::from(node.id())))
            .collect(),
        left.graph()
            .edges()
            .iter()
            .map(|edge| (Arc::from(edge.id()), Arc::from(edge.id())))
            .collect(),
        right
            .graph()
            .nodes()
            .iter()
            .filter(|node| !interface_nodes.contains(node.id()))
            .map(|node| (Arc::from(node.id()), Arc::from(node.id())))
            .collect(),
        right
            .graph()
            .edges()
            .iter()
            .filter(|edge| !interface_edges.contains(edge.id()))
            .map(|edge| (Arc::from(edge.id()), Arc::from(edge.id())))
            .collect(),
    );
    (
        RewriteProduction::new(
            id,
            RewriteFragment::from_kernel(left),
            interface_nodes,
            interface_edges,
            RewriteFragment::from_kernel(right),
        )
        .unwrap(),
        RewriteRequest::new(id, matching),
    )
}

pub fn normalization() -> (RewriteGrammar, RewriteRequest) {
    let empty = kernel(&[], &[]);
    let (production, request) = rule("normalize", &empty, &empty, &[], &[]);
    (RewriteGrammar::new([production]).unwrap(), request)
}
