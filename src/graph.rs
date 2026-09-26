use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

/// Opaque bytes submitted as package content or retained as activation results.
pub type Payload = Arc<[u8]>;

/// Stable SHA-256 commitment to exact package payload bytes.
///
/// The digest uses the domain-separated `ontography-payload/v1` scheme. It is
/// an integrity commitment, not a content location or a confidentiality
/// mechanism.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentDigest([u8; 32]);

impl ContentDigest {
    const DOMAIN: &'static [u8] = b"ontography-payload/v1\0";

    /// Reconstructs a content digest from its durable bytes.
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Computes the versioned commitment to exact payload bytes.
    #[must_use]
    pub fn compute(payload: &[u8]) -> Self {
        let mut hash = Sha256::new();
        hash.update(Self::DOMAIN);
        hash.update(payload);
        Self(hash.finalize().into())
    }

    /// Returns the stable digest bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Reports whether payload bytes match this commitment.
    #[must_use]
    pub fn verifies(self, payload: &[u8]) -> bool {
        self == Self::compute(payload)
    }
}

impl fmt::Debug for ContentDigest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "ContentDigest({self})")
    }
}

impl fmt::Display for ContentDigest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Stable identity of one workflow and its semantic contract registry.
///
/// Rewrites may change topology under this identity; fingerprints distinguish
/// the admitted graph versions. Reusing the identity requires unchanged meanings
/// for referenced contracts.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefinitionId(Arc<str>);

impl DefinitionId {
    /// Creates a stable workflow-definition identity.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the ID is empty.
    pub fn new(value: impl Into<Arc<str>>) -> Result<Self, DefinitionError> {
        identifier(value, "definition ID").map(Self)
    }

    /// Returns the stable identifier.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for DefinitionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

/// Stable SHA-256 fingerprint of one definition's canonical static structure.
///
/// The fingerprint excludes [`DefinitionId`], which is checked separately. It
/// includes contract IDs and object types but cannot inspect validator code;
/// reconstruction therefore relies on the contract-ID semantic promise.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefinitionFingerprint([u8; 32]);

impl DefinitionFingerprint {
    /// Reconstructs a fingerprint from persisted bytes.
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Returns the stable fingerprint bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub(crate) fn compute(
        schema: &Schema,
        graph: &Graph,
        contracts: &[Contract],
        node_definitions: &[NodeDefinition],
        edge_definitions: &[EdgeDefinition],
        authority_transitions: &[AuthorityTransitionRule],
        roots: &[RootRule],
    ) -> Self {
        let mut hash = FingerprintBuilder::new();
        hash.text("ontography-definition-fingerprint/v3");

        hash.count(schema.node_types.len());
        for node_type in &schema.node_types {
            hash.text(node_type);
        }
        hash.count(schema.object_types.len());
        for object_type in &schema.object_types {
            hash.text(object_type);
        }
        hash.authority_tags(&schema.authority_tags);

        hash.count(graph.nodes.len());
        for node in &graph.nodes {
            hash.text(&node.id);
        }
        hash.count(graph.edges.len());
        for edge in &graph.edges {
            hash.text(&edge.id);
            hash.text(&edge.source);
            hash.text(&edge.target);
        }

        hash.count(contracts.len());
        for contract in contracts {
            hash.text(&contract.id);
            hash.text(&contract.object_type);
        }
        hash.count(node_definitions.len());
        for definition in node_definitions {
            hash.text(&definition.node_id);
            hash.count(definition.types.len());
            for node_type in &definition.types {
                hash.text(node_type);
            }
            hash.text(&definition.result_contract);
            hash.text(match definition.ingress_mode {
                IngressMode::Any => "any",
                IngressMode::All => "all",
            });
        }
        hash.count(edge_definitions.len());
        for definition in edge_definitions {
            hash.text(&definition.edge_id);
            hash.count(definition.types.len());
            for edge_type in &definition.types {
                hash.text(edge_type);
            }
            hash.count(definition.source_requirements.len());
            for node_type in &definition.source_requirements {
                hash.text(node_type);
            }
            hash.count(definition.target_requirements.len());
            for node_type in &definition.target_requirements {
                hash.text(node_type);
            }
            hash.text(&definition.package_contract);
            hash.text(match definition.authority_match {
                AuthorityMatch::AnyOf => "any-of",
                AuthorityMatch::AllOf => "all-of",
            });
            hash.authority_tags(&definition.authority_tags);
        }
        hash.count(authority_transitions.len());
        for transition in authority_transitions {
            hash.text(&transition.node_id);
            hash.authority(&transition.from);
            hash.authority(&transition.to);
        }
        hash.count(roots.len());
        for root in roots {
            hash.text(&root.node_id);
            hash.authority(&root.ceiling);
        }

        Self(hash.finish())
    }
}

impl fmt::Debug for DefinitionFingerprint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "DefinitionFingerprint({self})")
    }
}

impl fmt::Display for DefinitionFingerprint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

struct FingerprintBuilder(Sha256);

impl FingerprintBuilder {
    fn new() -> Self {
        Self(Sha256::new())
    }

    fn count(&mut self, count: usize) {
        self.0
            .update(u64::try_from(count).expect("usize fits u64").to_be_bytes());
    }

    fn text(&mut self, value: &str) {
        self.count(value.len());
        self.0.update(value.as_bytes());
    }

    fn authority_tag(&mut self, tag: &AuthorityTag) {
        self.text(&tag.id);
    }

    fn authority_tags(&mut self, tags: &BTreeSet<AuthorityTag>) {
        self.count(tags.len());
        for tag in tags {
            self.authority_tag(tag);
        }
    }

    fn authority(&mut self, authority: &Authority) {
        self.authority_tags(&authority.tags);
    }

    fn finish(self) -> [u8; 32] {
        self.0.finalize().into()
    }
}

fn identifier(value: impl Into<Arc<str>>, kind: &'static str) -> Result<Arc<str>, DefinitionError> {
    let value = value.into();
    if value.is_empty() {
        return Err(DefinitionError::EmptyIdentifier(kind));
    }
    Ok(value)
}

fn identifiers<I, S>(values: I, kind: &'static str) -> Result<BTreeSet<Arc<str>>, DefinitionError>
where
    I: IntoIterator<Item = S>,
    S: Into<Arc<str>>,
{
    values
        .into_iter()
        .map(|value| identifier(value, kind))
        .collect()
}

/// Stable identity of one authority classification.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct AuthorityTag {
    id: Arc<str>,
}

impl<'de> Deserialize<'de> for AuthorityTag {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Tag {
            id: Arc<str>,
        }
        Self::new(Tag::deserialize(deserializer)?.id).map_err(serde::de::Error::custom)
    }
}

impl AuthorityTag {
    /// Creates an authority tag.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the identity is empty.
    pub fn new(id: impl Into<Arc<str>>) -> Result<Self, DefinitionError> {
        Ok(Self {
            id: identifier(id, "authority tag")?,
        })
    }

    /// Returns the stable authority-tag identity.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }
}

/// Closed vocabulary of node types, object types, and authority tags.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Schema {
    node_types: BTreeSet<Arc<str>>,
    object_types: BTreeSet<Arc<str>>,
    authority_tags: BTreeSet<AuthorityTag>,
}

impl Schema {
    /// Creates a closed schema vocabulary.
    ///
    /// # Errors
    ///
    /// Returns an error when a node or object type identifier is empty.
    pub fn new<N, O, A, NS, OS>(
        node_types: N,
        object_types: O,
        authority_tags: A,
    ) -> Result<Self, DefinitionError>
    where
        N: IntoIterator<Item = NS>,
        O: IntoIterator<Item = OS>,
        A: IntoIterator<Item = AuthorityTag>,
        NS: Into<Arc<str>>,
        OS: Into<Arc<str>>,
    {
        let node_types = node_types
            .into_iter()
            .map(|value| identifier(value, "schema node type"))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let object_types = object_types
            .into_iter()
            .map(|value| identifier(value, "schema object type"))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let authority_tags = authority_tags.into_iter().collect::<BTreeSet<_>>();
        Ok(Self {
            node_types,
            object_types,
            authority_tags,
        })
    }

    pub(crate) fn admits_node_type(&self, node_type: &str) -> bool {
        self.node_types.contains(node_type)
    }

    pub(crate) fn admits_object_type(&self, object_type: &str) -> bool {
        self.object_types.contains(object_type)
    }

    pub(crate) fn admits_authority_tag(&self, tag: &AuthorityTag) -> bool {
        self.authority_tags.contains(tag)
    }

    pub(crate) fn admits_authority(&self, authority: &Authority) -> bool {
        authority.tags.is_subset(&self.authority_tags)
    }

    pub(crate) fn is_subset_of(&self, other: &Self) -> bool {
        self.node_types.is_subset(&other.node_types)
            && self.object_types.is_subset(&other.object_types)
            && self.authority_tags.is_subset(&other.authority_tags)
    }

    /// Returns the admitted authority tags.
    #[must_use]
    pub fn authority_tags(&self) -> impl ExactSizeIterator<Item = &AuthorityTag> {
        self.authority_tags.iter()
    }
}

/// Immutable tagged capacity carried by a package.
///
/// Clones share the canonical tag set while retaining value equality and
/// ordering.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Authority {
    tags: Arc<BTreeSet<AuthorityTag>>,
}

impl Authority {
    /// Creates authority from tags.
    #[must_use]
    pub fn new<T>(tags: T) -> Self
    where
        T: IntoIterator<Item = AuthorityTag>,
    {
        Self {
            tags: Arc::new(tags.into_iter().collect()),
        }
    }

    /// Reports whether this authority contains a tag.
    #[must_use]
    pub fn contains(&self, tag: &AuthorityTag) -> bool {
        self.tags.contains(tag)
    }

    /// Reports whether every tag here is present in `other`.
    #[must_use]
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.tags.is_subset(&other.tags)
    }

    /// Returns the carried authority tags.
    #[must_use]
    pub fn tags(&self) -> impl ExactSizeIterator<Item = &AuthorityTag> {
        self.tags.iter()
    }
}

/// A payload-contract rejection.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
#[error("{message}")]
pub struct ContractViolation {
    message: String,
}

impl ContractViolation {
    /// Creates a contract rejection.
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

type Validator = dyn Fn(&[u8]) -> Result<(), ContractViolation> + Send + Sync + 'static;

/// A named exact payload predicate for one object type.
///
/// Validators are part of the trusted static definition. They must be pure,
/// deterministic, and total except for returning [`ContractViolation`]. They
/// must not observe clocks or mutable external state, and must not perform
/// externally visible effects. The kernel may reuse a successful validation of
/// the same content commitment under the same admitted contract within one
/// operation, so validators must not rely on invocation counts. A panic
/// propagates to the caller; only kernel state, not validator-owned state, is
/// protected by activation atomicity.
///
/// Across reconstruction, the same contract ID and object type must denote the
/// same accepted payload set.
#[derive(Clone)]
pub struct Contract {
    pub(crate) id: Arc<str>,
    pub(crate) object_type: Arc<str>,
    validate: Arc<Validator>,
}

impl Contract {
    /// Creates an exact payload contract.
    ///
    /// `validate` must satisfy the purity, determinism, and stable-identity
    /// requirements documented on [`Contract`].
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the contract ID or
    /// object type is empty.
    pub fn new<V>(
        id: impl Into<Arc<str>>,
        object_type: impl Into<Arc<str>>,
        validate: V,
    ) -> Result<Self, DefinitionError>
    where
        V: Fn(&[u8]) -> Result<(), ContractViolation> + Send + Sync + 'static,
    {
        Ok(Self {
            id: identifier(id, "contract ID")?,
            object_type: identifier(object_type, "contract object type")?,
            validate: Arc::new(validate),
        })
    }

    /// Returns the contract ID.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Returns the contract's object type.
    #[must_use]
    pub fn object_type(&self) -> &str {
        &self.object_type
    }

    pub(crate) fn validate(&self, payload: &[u8]) -> Result<(), ContractViolation> {
        (self.validate)(payload)
    }

    pub(crate) fn shares_validator_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.validate, &other.validate)
    }
}

/// One concrete topology node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Node {
    id: Arc<str>,
}

impl Node {
    /// Creates a topology node.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the ID is empty.
    pub fn new(id: impl Into<Arc<str>>) -> Result<Self, DefinitionError> {
        Ok(Self {
            id: identifier(id, "node ID")?,
        })
    }

    /// Returns the stable node ID.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    pub(crate) fn id_arc(&self) -> Arc<str> {
        Arc::clone(&self.id)
    }
}

/// One concrete directed topology edge.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Edge {
    id: Arc<str>,
    source: Arc<str>,
    target: Arc<str>,
}

impl Edge {
    /// Creates a topology edge.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the edge ID, source,
    /// or target is empty.
    pub fn new(
        id: impl Into<Arc<str>>,
        source: impl Into<Arc<str>>,
        target: impl Into<Arc<str>>,
    ) -> Result<Self, DefinitionError> {
        Ok(Self {
            id: identifier(id, "edge ID")?,
            source: identifier(source, "edge source")?,
            target: identifier(target, "edge target")?,
        })
    }

    /// Returns the stable edge ID.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    pub(crate) fn id_arc(&self) -> Arc<str> {
        Arc::clone(&self.id)
    }

    /// Returns the source node ID.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns the target node ID.
    #[must_use]
    pub fn target(&self) -> &str {
        &self.target
    }

    pub(crate) fn target_arc(&self) -> Arc<str> {
        Arc::clone(&self.target)
    }
}

/// A finite directed multigraph containing topology only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Graph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    node_by_id: BTreeMap<Arc<str>, usize>,
    edge_by_id: BTreeMap<Arc<str>, usize>,
    incoming_by_node: BTreeMap<Arc<str>, BTreeSet<Arc<str>>>,
}

impl Graph {
    /// Admits topology with unique identities and existing endpoints.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError`] when the topology is invalid.
    pub fn new<N, E>(nodes: N, edges: E) -> Result<Self, DefinitionError>
    where
        N: IntoIterator<Item = Node>,
        E: IntoIterator<Item = Edge>,
    {
        let mut nodes = nodes.into_iter().collect::<Vec<_>>();
        let mut edges = edges.into_iter().collect::<Vec<_>>();
        nodes.sort_unstable();
        edges.sort_unstable();

        let mut node_by_id = BTreeMap::new();
        for (index, node) in nodes.iter().enumerate() {
            if node_by_id.insert(node.id.clone(), index).is_some() {
                return Err(DefinitionError::DuplicateNode(node.id.clone()));
            }
        }

        let mut edge_by_id = BTreeMap::new();
        let mut incoming_by_node = nodes
            .iter()
            .map(|node| (Arc::clone(&node.id), BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (index, edge) in edges.iter().enumerate() {
            if !node_by_id.contains_key(&edge.source) {
                return Err(DefinitionError::UnknownEndpoint(edge.source.clone()));
            }
            if !node_by_id.contains_key(&edge.target) {
                return Err(DefinitionError::UnknownEndpoint(edge.target.clone()));
            }
            if edge_by_id.insert(edge.id.clone(), index).is_some() {
                return Err(DefinitionError::DuplicateEdge(edge.id.clone()));
            }
            let incoming = incoming_by_node
                .get_mut(&edge.target)
                .ok_or_else(|| DefinitionError::UnknownEndpoint(edge.target.clone()))?;
            let inserted = incoming.insert(Arc::clone(&edge.id));
            debug_assert!(inserted);
        }

        Ok(Self {
            nodes,
            edges,
            node_by_id,
            edge_by_id,
            incoming_by_node,
        })
    }

    /// Returns the topology nodes.
    #[must_use]
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Returns the topology edges.
    #[must_use]
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    /// Looks up a topology node.
    #[must_use]
    pub fn node(&self, id: &str) -> Option<&Node> {
        self.node_by_id
            .get(id)
            .and_then(|index| self.nodes.get(*index))
    }

    /// Looks up a topology edge.
    #[must_use]
    pub fn edge(&self, id: &str) -> Option<&Edge> {
        self.edge_by_id
            .get(id)
            .and_then(|index| self.edges.get(*index))
    }

    pub(crate) fn edge_index(&self, id: &str) -> Option<usize> {
        self.edge_by_id.get(id).copied()
    }

    pub(crate) fn incoming_edge_ids(&self, node_id: &str) -> Option<&BTreeSet<Arc<str>>> {
        self.incoming_by_node.get(node_id)
    }
}

/// How package occurrences may trigger a node activation.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum IngressMode {
    /// Exactly one package arriving on any incoming edge.
    #[default]
    Any,
    /// Exactly one package occurrence from every incoming static edge.
    All,
}

/// How an edge compares its authority tags with a package's carried authority.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum AuthorityMatch {
    /// At least one edge tag must be present in the package authority.
    #[default]
    AnyOf,
    /// Every edge tag must be present in the package authority.
    AllOf,
}

/// Ontography annotations for one concrete topology node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct NodeDefinition {
    pub(crate) node_id: Arc<str>,
    pub(crate) types: BTreeSet<Arc<str>>,
    pub(crate) result_contract: Arc<str>,
    ingress_mode: IngressMode,
}

impl NodeDefinition {
    /// Creates a node definition.
    ///
    /// # Errors
    ///
    /// Returns an error when an ID or type is empty, or when no semantic node
    /// type is supplied.
    pub fn new<I, S>(
        node_id: impl Into<Arc<str>>,
        types: I,
        result_contract: impl Into<Arc<str>>,
    ) -> Result<Self, DefinitionError>
    where
        I: IntoIterator<Item = S>,
        S: Into<Arc<str>>,
    {
        let node_id = identifier(node_id, "defined node ID")?;
        let types = identifiers(types, "node type")?;
        if types.is_empty() {
            return Err(DefinitionError::MissingNodeTypes(node_id));
        }
        Ok(Self {
            node_id,
            types,
            result_contract: identifier(result_contract, "result contract ID")?,
            ingress_mode: IngressMode::Any,
        })
    }

    /// Selects whether package activation consumes one or all incoming edges.
    #[must_use]
    pub fn with_ingress_mode(mut self, ingress_mode: IngressMode) -> Self {
        self.ingress_mode = ingress_mode;
        self
    }

    /// Returns the topology node ID.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Returns the semantic node types.
    #[must_use]
    pub fn types(&self) -> &BTreeSet<Arc<str>> {
        &self.types
    }

    /// Reports whether this node has a semantic type.
    #[must_use]
    pub fn has_type(&self, node_type: &str) -> bool {
        self.types.contains(node_type)
    }

    /// Returns the exact result contract ID.
    #[must_use]
    pub fn result_contract(&self) -> &str {
        &self.result_contract
    }

    /// Returns this node's package-ingress mode.
    #[must_use]
    pub const fn ingress_mode(&self) -> IngressMode {
        self.ingress_mode
    }
}

/// Semantic annotations for one concrete topology edge.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct EdgeDefinition {
    pub(crate) edge_id: Arc<str>,
    pub(crate) types: BTreeSet<Arc<str>>,
    pub(crate) source_requirements: BTreeSet<Arc<str>>,
    pub(crate) target_requirements: BTreeSet<Arc<str>>,
    pub(crate) package_contract: Arc<str>,
    pub(crate) authority_tags: BTreeSet<AuthorityTag>,
    pub(crate) authority_match: AuthorityMatch,
}

impl EdgeDefinition {
    /// Creates an explicit semantic definition for one topology edge.
    ///
    /// # Errors
    ///
    /// Returns an error when an identity or type is empty, or when no semantic
    /// edge type or authority tag is supplied.
    pub fn new<ET, ETS, SR, SRS, TR, TRS, AT>(
        edge_id: impl Into<Arc<str>>,
        types: ET,
        source_requirements: SR,
        target_requirements: TR,
        package_contract: impl Into<Arc<str>>,
        authority_tags: AT,
    ) -> Result<Self, DefinitionError>
    where
        ET: IntoIterator<Item = ETS>,
        ETS: Into<Arc<str>>,
        SR: IntoIterator<Item = SRS>,
        SRS: Into<Arc<str>>,
        TR: IntoIterator<Item = TRS>,
        TRS: Into<Arc<str>>,
        AT: IntoIterator<Item = AuthorityTag>,
    {
        let edge_id = identifier(edge_id, "defined edge ID")?;
        let types = identifiers(types, "edge type")?;
        if types.is_empty() {
            return Err(DefinitionError::MissingEdgeTypes(edge_id));
        }
        let authority_tags = authority_tags.into_iter().collect::<BTreeSet<_>>();
        if authority_tags.is_empty() {
            return Err(DefinitionError::MissingEdgeAuthorityTags(edge_id));
        }
        Ok(Self {
            edge_id,
            types,
            source_requirements: identifiers(source_requirements, "edge source requirement")?,
            target_requirements: identifiers(target_requirements, "edge target requirement")?,
            package_contract: identifier(package_contract, "edge package contract ID")?,
            authority_tags,
            authority_match: AuthorityMatch::AnyOf,
        })
    }

    /// Selects how package authority is matched against this edge's tags.
    #[must_use]
    pub const fn with_authority_match(mut self, authority_match: AuthorityMatch) -> Self {
        self.authority_match = authority_match;
        self
    }

    /// Returns the topology edge ID.
    #[must_use]
    pub fn edge_id(&self) -> &str {
        &self.edge_id
    }

    /// Returns the semantic edge types.
    #[must_use]
    pub fn types(&self) -> &BTreeSet<Arc<str>> {
        &self.types
    }

    /// Returns the node types required at the source.
    #[must_use]
    pub fn source_requirements(&self) -> &BTreeSet<Arc<str>> {
        &self.source_requirements
    }

    /// Returns the node types required at the target.
    #[must_use]
    pub fn target_requirements(&self) -> &BTreeSet<Arc<str>> {
        &self.target_requirements
    }

    /// Returns the exact package-contract ID.
    #[must_use]
    pub fn package_contract(&self) -> &str {
        &self.package_contract
    }

    /// Returns the authority tags recognized by this edge.
    #[must_use]
    pub const fn authority_tags(&self) -> &BTreeSet<AuthorityTag> {
        &self.authority_tags
    }

    /// Returns how package authority is matched against this edge's tags.
    #[must_use]
    pub const fn authority_match(&self) -> AuthorityMatch {
        self.authority_match
    }

    /// Reports whether a package authority satisfies this edge's tag rule.
    #[must_use]
    pub fn matches_authority(&self, authority: &Authority) -> bool {
        match self.authority_match {
            AuthorityMatch::AnyOf => !self.authority_tags.is_disjoint(&authority.tags),
            AuthorityMatch::AllOf => self.authority_tags.is_subset(&authority.tags),
        }
    }
}

/// One sealed authority transition available at a concrete node.
///
/// A transition may attenuate, preserve, or amplify authority. Its source must
/// exactly equal the activation's governing authority. Its target becomes the
/// authority carried by an output package in the same atomic activation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct AuthorityTransitionRule {
    pub(crate) node_id: Arc<str>,
    pub(crate) from: Authority,
    pub(crate) to: Authority,
}

impl AuthorityTransitionRule {
    /// Creates an authority-transition rule.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the node ID is empty.
    pub fn new(
        node_id: impl Into<Arc<str>>,
        from: Authority,
        to: Authority,
    ) -> Result<Self, DefinitionError> {
        Ok(Self {
            node_id: identifier(node_id, "authority-transition node ID")?,
            from,
            to,
        })
    }

    /// Returns the node allowed to establish the transition.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Returns the required governing authority.
    #[must_use]
    pub fn from(&self) -> &Authority {
        &self.from
    }

    /// Returns the permitted output authority.
    #[must_use]
    pub fn to(&self) -> &Authority {
        &self.to
    }
}

/// Maximum initial authority with which a root may begin at one node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct RootRule {
    pub(crate) node_id: Arc<str>,
    pub(crate) ceiling: Authority,
}

impl RootRule {
    /// Creates a root-authority rule.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionError::EmptyIdentifier`] when the node ID is empty.
    pub fn new(node_id: impl Into<Arc<str>>, ceiling: Authority) -> Result<Self, DefinitionError> {
        Ok(Self {
            node_id: identifier(node_id, "root node ID")?,
            ceiling,
        })
    }

    /// Returns the rootable node ID.
    #[must_use]
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Returns the maximum initial authority for a root activation.
    #[must_use]
    pub fn ceiling(&self) -> &Authority {
        &self.ceiling
    }
}

/// Static workflow-admission failure.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum DefinitionError {
    /// An identifier was empty.
    #[error("{0} must not be empty")]
    EmptyIdentifier(&'static str),
    /// A contract ID is duplicated.
    #[error("duplicate contract ID: {0}")]
    DuplicateContract(Arc<str>),
    /// A contract's object type is outside the schema.
    #[error("unknown contract object type: {0}")]
    UnknownContractObjectType(Arc<str>),
    /// A topology node ID is duplicated.
    #[error("duplicate node ID: {0}")]
    DuplicateNode(Arc<str>),
    /// A topology edge ID is duplicated.
    #[error("duplicate edge ID: {0}")]
    DuplicateEdge(Arc<str>),
    /// An edge endpoint does not exist.
    #[error("unknown edge endpoint: {0}")]
    UnknownEndpoint(Arc<str>),
    /// Node annotations refer to no topology node.
    #[error("definition refers to unknown node: {0}")]
    UnknownDefinedNode(Arc<str>),
    /// More than one annotation describes a topology node.
    #[error("duplicate node definition: {0}")]
    DuplicateNodeDefinition(Arc<str>),
    /// A topology node has no Ontography annotation.
    #[error("missing node definition: {0}")]
    MissingNodeDefinition(Arc<str>),
    /// A node definition declares no semantic type.
    #[error("node definition has no semantic types: {0}")]
    MissingNodeTypes(Arc<str>),
    /// Edge annotations refer to no topology edge.
    #[error("definition refers to unknown edge: {0}")]
    UnknownDefinedEdge(Arc<str>),
    /// More than one annotation describes a topology edge.
    #[error("duplicate edge definition: {0}")]
    DuplicateEdgeDefinition(Arc<str>),
    /// A topology edge has no Ontography annotation.
    #[error("missing edge definition: {0}")]
    MissingEdgeDefinition(Arc<str>),
    /// An edge definition declares no semantic type.
    #[error("edge definition has no semantic types: {0}")]
    MissingEdgeTypes(Arc<str>),
    /// An edge definition declares no authority tag.
    #[error("edge definition has no authority tags: {0}")]
    MissingEdgeAuthorityTags(Arc<str>),
    /// A concrete node uses a type outside the schema.
    #[error("node {node} has unknown type {node_type}")]
    UnknownNodeType {
        /// Node ID.
        node: Arc<str>,
        /// Unknown node type.
        node_type: Arc<str>,
    },
    /// An edge's source does not have every required semantic type.
    #[error("edge {edge} source types {actual:?} do not satisfy {required:?}")]
    EdgeSourceRequirements {
        /// Edge ID.
        edge: Arc<str>,
        /// Types required by the edge definition.
        required: BTreeSet<Arc<str>>,
        /// Types declared by the source node.
        actual: BTreeSet<Arc<str>>,
    },
    /// An edge's target does not have every required semantic type.
    #[error("edge {edge} target types {actual:?} do not satisfy {required:?}")]
    EdgeTargetRequirements {
        /// Edge ID.
        edge: Arc<str>,
        /// Types required by the edge definition.
        required: BTreeSet<Arc<str>>,
        /// Types declared by the target node.
        actual: BTreeSet<Arc<str>>,
    },
    /// A referenced exact contract does not exist.
    #[error("unknown contract: {0}")]
    UnknownContract(Arc<str>),
    /// A concrete edge declares an authority tag outside the schema.
    #[error("edge {edge} uses forbidden authority tag {tag:?}")]
    ForbiddenAuthorityTag {
        /// Edge ID.
        edge: Arc<str>,
        /// Rejected authority tag.
        tag: AuthorityTag,
    },
    /// An authority transition refers to an unknown topology node.
    #[error("authority transition refers to unknown node: {0}")]
    UnknownAuthorityTransitionNode(Arc<str>),
    /// An authority transition contains authority outside the schema.
    #[error("authority-transition endpoints must be subsets of schema authority tags")]
    AuthorityTransitionOutsideSchema,
    /// A root rule refers to an unknown topology node.
    #[error("root rule refers to unknown node: {0}")]
    UnknownRootNode(Arc<str>),
    /// More than one root rule governs the same node.
    #[error("duplicate root rule for node: {0}")]
    DuplicateRootRule(Arc<str>),
    /// A root ceiling contains authority outside the schema.
    #[error("root authority ceiling must be a subset of schema authority tags")]
    RootAuthorityOutsideSchema,
}
