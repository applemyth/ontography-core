//! Rewrite fixtures shared by the ported calculus suites: a five-contract
//! vocabulary, root-driven package births, and graph edits described as a
//! subgraph replaced around a preserved interface.

use ontography::{
    ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract, ContractViolation,
    DefinitionId, Edge, EdgeDefinition, Emission, Graph, GraphEdit, GraphFragment, Kernel, Node,
    NodeDefinition, OutputAuthority, PackageId, Payload, Principal, RewriteRequest, RootRule,
    Schema, State,
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

/// The edit that replaces the host subgraph `left` by `right`, keeping the
/// named interface: `left`'s other elements are removed, and `right`'s other
/// elements are added with their definitions, roots, and transitions. Both
/// sides use the host's own identities.
pub fn replace(
    left: &Kernel,
    right: &Kernel,
    interface_nodes: &[&str],
    interface_edges: &[&str],
) -> GraphEdit {
    let kept_nodes = names(interface_nodes);
    let kept_edges = names(interface_edges);
    let added_node = |id: &str| !kept_nodes.contains(id);
    let added_edge = |id: &str| !kept_edges.contains(id);
    GraphEdit::new(
        left.graph()
            .nodes()
            .iter()
            .map(|node| Arc::from(node.id()))
            .filter(|id: &Arc<str>| added_node(id))
            .collect(),
        left.graph()
            .edges()
            .iter()
            .map(Edge::id_arc)
            .filter(|id: &Arc<str>| added_edge(id))
            .collect(),
        GraphFragment::new(
            right
                .graph()
                .nodes()
                .iter()
                .filter(|node| added_node(node.id()))
                .cloned()
                .collect(),
            right
                .graph()
                .edges()
                .iter()
                .filter(|edge| added_edge(edge.id()))
                .cloned()
                .collect(),
            right
                .node_definitions()
                .iter()
                .filter(|definition| added_node(definition.node_id()))
                .cloned()
                .collect(),
            right
                .edge_definitions()
                .iter()
                .filter(|definition| added_edge(definition.edge_id()))
                .cloned()
                .collect(),
            right
                .authority_transitions()
                .iter()
                .filter(|rule| added_node(rule.node_id()))
                .cloned()
                .collect(),
            right
                .roots()
                .iter()
                .filter(|root| added_node(root.node_id()))
                .cloned()
                .collect(),
        ),
    )
}

/// A request from the suites' single principal.
pub fn request(edit: GraphEdit) -> RewriteRequest {
    RewriteRequest::new(Principal::new("test"), edit)
}

/// The identity rewrite: nothing removed, nothing added.
pub fn normalization() -> RewriteRequest {
    request(GraphEdit::default())
}
