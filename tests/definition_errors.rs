//! Every `DefinitionError` variant, pinned by name through the constructors
//! and `Kernel::admit`.

use ontography::{
    Authority, AuthorityTag, AuthorityTransitionRule, Contract, DefinitionError, DefinitionId,
    Edge, EdgeDefinition, Graph, Kernel, Node, NodeDefinition, RootRule, Schema,
};

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

fn contract(id: &str, object_type: &str) -> Contract {
    Contract::new(id, object_type, |_| Ok(())).unwrap()
}

fn schema() -> Schema {
    Schema::new(["Node"], ["Value"], [tag("t")]).unwrap()
}

fn graph() -> Graph {
    Graph::new(
        [Node::new("a").unwrap(), Node::new("b").unwrap()],
        [Edge::new("ab", "a", "b").unwrap()],
    )
    .unwrap()
}

fn node(id: &str) -> NodeDefinition {
    NodeDefinition::new(id, ["Node"], "value").unwrap()
}

fn edge(id: &str) -> EdgeDefinition {
    EdgeDefinition::new(id, ["Flow"], ["Node"], ["Node"], "value", [tag("t")]).unwrap()
}

/// Admits the fixture with one list replaced.
fn admit(
    contracts: Vec<Contract>,
    nodes: Vec<NodeDefinition>,
    edges: Vec<EdgeDefinition>,
    transitions: Vec<AuthorityTransitionRule>,
    roots: Vec<RootRule>,
) -> Result<Kernel, DefinitionError> {
    Kernel::admit(
        DefinitionId::new("errors").unwrap(),
        schema(),
        graph(),
        contracts,
        nodes,
        edges,
        transitions,
        roots,
    )
}

fn ok() -> (Vec<Contract>, Vec<NodeDefinition>, Vec<EdgeDefinition>) {
    (
        vec![contract("value", "Value")],
        vec![node("a"), node("b")],
        vec![edge("ab")],
    )
}

#[test]
fn constructors_reject_empty_identifiers() {
    assert_eq!(
        DefinitionId::new("").unwrap_err(),
        DefinitionError::EmptyIdentifier("definition ID")
    );
    assert_eq!(
        AuthorityTag::new("").unwrap_err(),
        DefinitionError::EmptyIdentifier("authority tag")
    );
    assert_eq!(
        Node::new("").unwrap_err(),
        DefinitionError::EmptyIdentifier("node ID")
    );
    assert_eq!(
        Edge::new("e", "", "b").unwrap_err(),
        DefinitionError::EmptyIdentifier("edge source")
    );
    assert_eq!(
        Contract::new("", "Value", |_| Ok(())).err(),
        Some(DefinitionError::EmptyIdentifier("contract ID"))
    );
    assert_eq!(
        NodeDefinition::new("a", ["Node"], "").unwrap_err(),
        DefinitionError::EmptyIdentifier("result contract ID")
    );
    assert_eq!(
        Schema::new([""], ["Value"], [tag("t")]).unwrap_err(),
        DefinitionError::EmptyIdentifier("schema node type")
    );
}

#[test]
fn constructors_reject_missing_types_and_tags() {
    assert!(matches!(
        NodeDefinition::new("a", [] as [&str; 0], "value").unwrap_err(),
        DefinitionError::MissingNodeTypes(id) if &*id == "a"
    ));
    assert!(matches!(
        EdgeDefinition::new("ab", [] as [&str; 0], ["Node"], ["Node"], "value", [tag("t")])
            .unwrap_err(),
        DefinitionError::MissingEdgeTypes(id) if &*id == "ab"
    ));
    assert!(matches!(
        EdgeDefinition::new("ab", ["Flow"], ["Node"], ["Node"], "value", [] as [AuthorityTag; 0])
            .unwrap_err(),
        DefinitionError::MissingEdgeAuthorityTags(id) if &*id == "ab"
    ));
}

#[test]
fn graph_rejects_duplicate_identities_and_unknown_endpoints() {
    assert!(matches!(
        Graph::new([Node::new("a").unwrap(), Node::new("a").unwrap()], []).unwrap_err(),
        DefinitionError::DuplicateNode(id) if &*id == "a"
    ));
    assert!(matches!(
        Graph::new(
            [Node::new("a").unwrap()],
            [Edge::new("e", "a", "a").unwrap(), Edge::new("e", "a", "a").unwrap()],
        )
        .unwrap_err(),
        DefinitionError::DuplicateEdge(id) if &*id == "e"
    ));
    assert!(matches!(
        Graph::new([Node::new("a").unwrap()], [Edge::new("e", "a", "zz").unwrap()]).unwrap_err(),
        DefinitionError::UnknownEndpoint(id) if &*id == "zz"
    ));
}

#[test]
fn admission_rejects_every_inconsistent_annotation() {
    let (contracts, nodes, edges) = ok();

    assert!(matches!(
        admit(
            vec![contract("value", "Value"), contract("value", "Value")],
            nodes.clone(),
            edges.clone(),
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::DuplicateContract(id) if &*id == "value"
    ));
    assert!(matches!(
        admit(vec![contract("value", "Other")], nodes.clone(), edges.clone(), vec![], vec![])
            .unwrap_err(),
        DefinitionError::UnknownContractObjectType(t) if &*t == "Other"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            vec![node("a"), node("b"), node("zz")],
            edges.clone(),
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::UnknownDefinedNode(id) if &*id == "zz"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            vec![node("a"), node("b"), node("a")],
            edges.clone(),
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::DuplicateNodeDefinition(id) if &*id == "a"
    ));
    assert!(matches!(
        admit(contracts.clone(), vec![node("a")], edges.clone(), vec![], vec![]).unwrap_err(),
        DefinitionError::MissingNodeDefinition(id) if &*id == "b"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            vec![NodeDefinition::new("a", ["Ghost"], "value").unwrap(), node("b")],
            edges.clone(),
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::UnknownNodeType { node, node_type } if &*node == "a" && &*node_type == "Ghost"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            vec![NodeDefinition::new("a", ["Node"], "missing").unwrap(), node("b")],
            edges.clone(),
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::UnknownContract(id) if &*id == "missing"
    ));
    assert!(matches!(
        admit(contracts.clone(), nodes.clone(), vec![edge("ab"), edge("zz")], vec![], vec![])
            .unwrap_err(),
        DefinitionError::UnknownDefinedEdge(id) if &*id == "zz"
    ));
    assert!(matches!(
        admit(contracts.clone(), nodes.clone(), vec![edge("ab"), edge("ab")], vec![], vec![])
            .unwrap_err(),
        DefinitionError::DuplicateEdgeDefinition(id) if &*id == "ab"
    ));
    assert!(matches!(
        admit(contracts.clone(), nodes.clone(), vec![], vec![], vec![]).unwrap_err(),
        DefinitionError::MissingEdgeDefinition(id) if &*id == "ab"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            vec![EdgeDefinition::new("ab", ["Flow"], ["Node"], ["Node"], "value", [tag("x")]).unwrap()],
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::ForbiddenAuthorityTag { edge, .. } if &*edge == "ab"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            vec![EdgeDefinition::new("ab", ["Flow"], ["Ghost"], ["Node"], "value", [tag("t")]).unwrap()],
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::EdgeSourceRequirements { edge, .. } if &*edge == "ab"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            vec![EdgeDefinition::new("ab", ["Flow"], ["Node"], ["Ghost"], "value", [tag("t")]).unwrap()],
            vec![],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::EdgeTargetRequirements { edge, .. } if &*edge == "ab"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            edges.clone(),
            vec![AuthorityTransitionRule::new("zz", Authority::new([]), Authority::new([])).unwrap()],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::UnknownAuthorityTransitionNode(id) if &*id == "zz"
    ));
    assert_eq!(
        admit(
            contracts.clone(),
            nodes.clone(),
            edges.clone(),
            vec![
                AuthorityTransitionRule::new("a", Authority::new([tag("x")]), Authority::new([]))
                    .unwrap()
            ],
            vec![]
        )
        .unwrap_err(),
        DefinitionError::AuthorityTransitionOutsideSchema
    );
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            edges.clone(),
            vec![],
            vec![RootRule::new("zz", Authority::new([])).unwrap()]
        )
        .unwrap_err(),
        DefinitionError::UnknownRootNode(id) if &*id == "zz"
    ));
    assert!(matches!(
        admit(
            contracts.clone(),
            nodes.clone(),
            edges.clone(),
            vec![],
            vec![
                RootRule::new("a", Authority::new([])).unwrap(),
                RootRule::new("a", Authority::new([])).unwrap()
            ]
        )
        .unwrap_err(),
        DefinitionError::DuplicateRootRule(id) if &*id == "a"
    ));
    assert_eq!(
        admit(
            contracts,
            nodes,
            edges,
            vec![],
            vec![RootRule::new("a", Authority::new([tag("x")])).unwrap()]
        )
        .unwrap_err(),
        DefinitionError::RootAuthorityOutsideSchema
    );
}
