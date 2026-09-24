//! Immutable admitted rulebook and its static indexes.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use crate::graph::{
    Authority, AuthorityTag, AuthorityTransitionRule, Contract, DefinitionError,
    DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition, Graph, Node, NodeDefinition,
    RootRule, Schema,
};

use super::occurrence::State;

struct AdmittedEdge {
    definition: usize,
    package_contract: usize,
}

fn contract_index(contracts: &[Contract], contract_id: &str) -> Option<usize> {
    contracts
        .binary_search_by(|contract| contract.id().cmp(contract_id))
        .ok()
}

fn node_definition_index(definitions: &[NodeDefinition], node_id: &str) -> Option<usize> {
    definitions
        .binary_search_by(|definition| definition.node_id().cmp(node_id))
        .ok()
}

fn edge_definition_index(definitions: &[EdgeDefinition], edge_id: &str) -> Option<usize> {
    definitions
        .binary_search_by(|definition| definition.edge_id().cmp(edge_id))
        .ok()
}

fn root_index(roots: &[RootRule], node_id: &str) -> Option<usize> {
    roots
        .binary_search_by(|root| root.node_id().cmp(node_id))
        .ok()
}

/// Immutable static rulebook and dynamic admission kernel.
pub struct Kernel {
    id: DefinitionId,
    fingerprint: DefinitionFingerprint,
    schema: Schema,
    graph: Graph,
    contracts: Vec<Contract>,
    node_definitions: Vec<NodeDefinition>,
    edge_definitions: Vec<EdgeDefinition>,
    authority_transitions: Vec<AuthorityTransitionRule>,
    roots: Vec<RootRule>,
    admitted_edges: Vec<AdmittedEdge>,
}

impl fmt::Debug for Kernel {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Kernel")
            .field("id", &self.id)
            .field("fingerprint", &self.fingerprint)
            .finish_non_exhaustive()
    }
}

impl Kernel {
    /// Admits one complete static workflow definition.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError`] when the graph annotations, contracts, or
    /// policies are inconsistent.
    #[allow(clippy::too_many_arguments)]
    pub fn admit<C, D, E, T, R>(
        id: DefinitionId,
        schema: Schema,
        graph: Graph,
        contracts: C,
        node_definitions: D,
        edge_definitions: E,
        authority_transitions: T,
        roots: R,
    ) -> Result<Self, DefinitionError>
    where
        C: IntoIterator<Item = Contract>,
        D: IntoIterator<Item = NodeDefinition>,
        E: IntoIterator<Item = EdgeDefinition>,
        T: IntoIterator<Item = AuthorityTransitionRule>,
        R: IntoIterator<Item = RootRule>,
    {
        let mut contracts = contracts.into_iter().collect::<Vec<_>>();
        let mut node_definitions = node_definitions.into_iter().collect::<Vec<_>>();
        let mut edge_definitions = edge_definitions.into_iter().collect::<Vec<_>>();
        let mut authority_transitions = authority_transitions.into_iter().collect::<Vec<_>>();
        let mut roots = roots.into_iter().collect::<Vec<_>>();
        contracts.sort_unstable_by(|left, right| left.id.cmp(&right.id));
        node_definitions.sort_unstable_by(|left, right| {
            left.node_id()
                .cmp(right.node_id())
                .then_with(|| left.cmp(right))
        });
        edge_definitions.sort_unstable_by(|left, right| {
            left.edge_id()
                .cmp(right.edge_id())
                .then_with(|| left.cmp(right))
        });
        roots.sort_unstable_by(|left, right| {
            left.node_id()
                .cmp(right.node_id())
                .then_with(|| left.cmp(right))
        });

        let mut previous_contract_id = None;
        for contract in &contracts {
            if !schema.admits_object_type(contract.object_type()) {
                return Err(DefinitionError::UnknownContractObjectType(
                    contract.object_type.clone(),
                ));
            }
            if previous_contract_id == Some(contract.id()) {
                return Err(DefinitionError::DuplicateContract(contract.id.clone()));
            }
            previous_contract_id = Some(contract.id());
        }

        let mut previous_node_id = None;
        for definition in &node_definitions {
            if graph.node(&definition.node_id).is_none() {
                return Err(DefinitionError::UnknownDefinedNode(
                    definition.node_id.clone(),
                ));
            }
            for node_type in &definition.types {
                if !schema.admits_node_type(node_type) {
                    return Err(DefinitionError::UnknownNodeType {
                        node: definition.node_id.clone(),
                        node_type: node_type.clone(),
                    });
                }
            }
            if contract_index(&contracts, &definition.result_contract).is_none() {
                return Err(DefinitionError::UnknownContract(
                    definition.result_contract.clone(),
                ));
            }
            if previous_node_id == Some(definition.node_id()) {
                return Err(DefinitionError::DuplicateNodeDefinition(
                    definition.node_id.clone(),
                ));
            }
            previous_node_id = Some(definition.node_id());
        }
        for node in graph.nodes() {
            if node_definition_index(&node_definitions, node.id()).is_none() {
                return Err(DefinitionError::MissingNodeDefinition(Arc::from(node.id())));
            }
        }

        let mut previous_edge_id = None;
        for definition in &edge_definitions {
            let Some(edge) = graph.edge(&definition.edge_id) else {
                return Err(DefinitionError::UnknownDefinedEdge(
                    definition.edge_id.clone(),
                ));
            };
            if contract_index(&contracts, &definition.package_contract).is_none() {
                return Err(DefinitionError::UnknownContract(
                    definition.package_contract.clone(),
                ));
            }
            if let Some(tag) = definition
                .authority_tags
                .iter()
                .find(|tag| !schema.admits_authority_tag(tag))
            {
                return Err(DefinitionError::ForbiddenAuthorityTag {
                    edge: Arc::from(edge.id()),
                    tag: tag.clone(),
                });
            }
            let Some(source_index) = node_definition_index(&node_definitions, edge.source()) else {
                return Err(DefinitionError::MissingNodeDefinition(Arc::from(
                    edge.source(),
                )));
            };
            let source = &node_definitions[source_index];
            if !definition.source_requirements.is_subset(&source.types) {
                return Err(DefinitionError::EdgeSourceRequirements {
                    edge: definition.edge_id.clone(),
                    required: definition.source_requirements.clone(),
                    actual: source.types.clone(),
                });
            }
            let Some(target_index) = node_definition_index(&node_definitions, edge.target()) else {
                return Err(DefinitionError::MissingNodeDefinition(Arc::from(
                    edge.target(),
                )));
            };
            let target = &node_definitions[target_index];
            if !definition.target_requirements.is_subset(&target.types) {
                return Err(DefinitionError::EdgeTargetRequirements {
                    edge: definition.edge_id.clone(),
                    required: definition.target_requirements.clone(),
                    actual: target.types.clone(),
                });
            }
            if previous_edge_id == Some(definition.edge_id()) {
                return Err(DefinitionError::DuplicateEdgeDefinition(
                    definition.edge_id.clone(),
                ));
            }
            previous_edge_id = Some(definition.edge_id());
        }
        let mut admitted_edges = Vec::with_capacity(graph.edges().len());
        for edge in graph.edges() {
            let Some(definition) = edge_definition_index(&edge_definitions, edge.id()) else {
                return Err(DefinitionError::MissingEdgeDefinition(Arc::from(edge.id())));
            };
            let Some(package_contract) =
                contract_index(&contracts, edge_definitions[definition].package_contract())
            else {
                return Err(DefinitionError::UnknownContract(
                    edge_definitions[definition].package_contract.clone(),
                ));
            };
            admitted_edges.push(AdmittedEdge {
                definition,
                package_contract,
            });
        }

        for transition in &authority_transitions {
            if graph.node(&transition.node_id).is_none() {
                return Err(DefinitionError::UnknownAuthorityTransitionNode(
                    transition.node_id.clone(),
                ));
            }
            if !schema.admits_authority(&transition.from)
                || !schema.admits_authority(&transition.to)
            {
                return Err(DefinitionError::AuthorityTransitionOutsideSchema);
            }
        }
        authority_transitions.sort_unstable_by(|left, right| {
            (left.node_id(), left.from(), left.to()).cmp(&(
                right.node_id(),
                right.from(),
                right.to(),
            ))
        });
        authority_transitions.dedup();

        let mut previous_root_node = None;
        for root in &roots {
            if graph.node(&root.node_id).is_none() {
                return Err(DefinitionError::UnknownRootNode(root.node_id.clone()));
            }
            if !schema.admits_authority(&root.ceiling) {
                return Err(DefinitionError::RootAuthorityOutsideSchema);
            }
            if previous_root_node == Some(root.node_id()) {
                return Err(DefinitionError::DuplicateRootRule(root.node_id.clone()));
            }
            previous_root_node = Some(root.node_id());
        }

        let fingerprint = DefinitionFingerprint::compute(
            &schema,
            &graph,
            &contracts,
            &node_definitions,
            &edge_definitions,
            &authority_transitions,
            &roots,
        );

        Ok(Self {
            id,
            fingerprint,
            schema,
            graph,
            contracts,
            node_definitions,
            edge_definitions,
            authority_transitions,
            roots,
            admitted_edges,
        })
    }

    /// Returns the stable workflow-definition identity.
    #[must_use]
    pub const fn id(&self) -> &DefinitionId {
        &self.id
    }

    /// Returns the stable fingerprint of this kernel's static rulebook.
    #[must_use]
    pub const fn fingerprint(&self) -> &DefinitionFingerprint {
        &self.fingerprint
    }

    /// Returns the admitted schema.
    #[must_use]
    pub const fn schema(&self) -> &Schema {
        &self.schema
    }

    /// Returns the topology-only graph.
    #[must_use]
    pub const fn graph(&self) -> &Graph {
        &self.graph
    }

    /// Returns the node annotations.
    #[must_use]
    pub fn node_definitions(&self) -> &[NodeDefinition] {
        &self.node_definitions
    }

    /// Returns the explicit edge annotations.
    #[must_use]
    pub fn edge_definitions(&self) -> &[EdgeDefinition] {
        &self.edge_definitions
    }

    /// Returns the exact payload contracts.
    #[must_use]
    pub fn contracts(&self) -> &[Contract] {
        &self.contracts
    }

    /// Returns the canonical sealed authority-transition policy.
    #[must_use]
    pub fn authority_transitions(&self) -> &[AuthorityTransitionRule] {
        &self.authority_transitions
    }

    /// Returns the root-authority rules.
    #[must_use]
    pub fn roots(&self) -> &[RootRule] {
        &self.roots
    }

    /// Looks up node annotations.
    #[must_use]
    pub fn node_definition(&self, node_id: &str) -> Option<&NodeDefinition> {
        node_definition_index(&self.node_definitions, node_id)
            .and_then(|index| self.node_definitions.get(index))
    }

    /// Looks up explicit edge annotations.
    #[must_use]
    pub fn edge_definition(&self, edge_id: &str) -> Option<&EdgeDefinition> {
        edge_definition_index(&self.edge_definitions, edge_id)
            .and_then(|index| self.edge_definitions.get(index))
    }

    /// Returns the authority tags declared by an admitted concrete edge.
    #[must_use]
    pub fn edge_authority_tags(&self, edge_id: &str) -> Option<&BTreeSet<AuthorityTag>> {
        self.edge_definition(edge_id)
            .map(EdgeDefinition::authority_tags)
    }

    /// Returns a node's root-authority ceiling, or `None` when it is not rootable.
    #[must_use]
    pub fn root_ceiling(&self, node_id: &str) -> Option<&Authority> {
        root_index(&self.roots, node_id).map(|index| self.roots[index].ceiling())
    }

    /// Looks up an exact payload contract.
    #[must_use]
    pub fn contract(&self, contract_id: &str) -> Option<&Contract> {
        contract_index(&self.contracts, contract_id).and_then(|index| self.contracts.get(index))
    }

    pub(super) fn admitted_edge(
        &self,
        edge_id: &str,
    ) -> Option<(&Edge, &EdgeDefinition, usize, &Contract)> {
        let index = self.graph.edge_index(edge_id)?;
        let edge = &self.graph.edges()[index];
        let admitted = &self.admitted_edges[index];
        let definition = &self.edge_definitions[admitted.definition];
        let contract = &self.contracts[admitted.package_contract];
        Some((edge, definition, admitted.package_contract, contract))
    }

    pub(super) fn incoming_edge_ids(&self, node_id: &str) -> &BTreeSet<Arc<str>> {
        self.graph
            .incoming_edge_ids(node_id)
            .expect("admitted node has an incoming-edge index")
    }

    pub(super) fn allows_authority_transition(
        &self,
        node: &str,
        from: &Authority,
        to: &Authority,
    ) -> bool {
        self.authority_transitions
            .binary_search_by(|rule| (&*rule.node_id, &rule.from, &rule.to).cmp(&(node, from, to)))
            .is_ok()
    }

    /// Creates the empty realized occurrence graph.
    #[must_use]
    pub fn empty_state(&self) -> State {
        State {
            definition_id: self.id().clone(),
            definition_fingerprint: *self.fingerprint(),
            activations: BTreeMap::new(),
            packages: BTreeMap::new(),
            consumed_by: BTreeMap::new(),
            positions: BTreeMap::new(),
            deliveries: BTreeMap::new(),
            revision: 0,
            used_node_ids: self.graph.nodes().iter().map(Node::id_arc).collect(),
            used_edge_ids: self.graph.edges().iter().map(Edge::id_arc).collect(),
        }
    }
}
