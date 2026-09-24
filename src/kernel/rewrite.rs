//! Admitted interface-preserving rewrites and explicit package transfer.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use serde::Serialize;
use thiserror::Error;

use crate::graph::{
    AuthorityTransitionRule, ContentDigest, DefinitionError, Edge, EdgeDefinition, Graph, Node,
    NodeDefinition, Payload, RootRule,
};

use super::definition::Kernel;
use super::frontier::{Delivery, Phase, Position, RetirementReason, cleanup};
use super::occurrence::{Package, PackageId, State};

/// One annotated fragment in a production; its identifiers are rule-local symbols.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct RewriteFragment {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    node_definitions: Vec<NodeDefinition>,
    edge_definitions: Vec<EdgeDefinition>,
    authority_transitions: Vec<AuthorityTransitionRule>,
    roots: Vec<RootRule>,
}

impl RewriteFragment {
    /// Constructs a fragment, whose topology/annotations are checked at admission.
    #[must_use]
    pub fn new(
        nodes: Vec<Node>,
        edges: Vec<Edge>,
        node_definitions: Vec<NodeDefinition>,
        edge_definitions: Vec<EdgeDefinition>,
        authority_transitions: Vec<AuthorityTransitionRule>,
        roots: Vec<RootRule>,
    ) -> Self {
        Self {
            nodes,
            edges,
            node_definitions,
            edge_definitions,
            authority_transitions,
            roots,
        }
    }

    /// Uses an admitted definition as a fragment, with its IDs as local symbols.
    #[must_use]
    pub fn from_kernel(kernel: &Kernel) -> Self {
        Self {
            nodes: kernel.graph().nodes().to_vec(),
            edges: kernel.graph().edges().to_vec(),
            node_definitions: kernel.node_definitions().to_vec(),
            edge_definitions: kernel.edge_definitions().to_vec(),
            authority_transitions: kernel.authority_transitions().to_vec(),
            roots: kernel.roots().to_vec(),
        }
    }

    fn admit(&self, kernel: &Kernel) -> Result<Kernel, DefinitionError> {
        Kernel::admit(
            kernel.id().clone(),
            kernel.schema().clone(),
            Graph::new(self.nodes.clone(), self.edges.clone())?,
            kernel.contracts().iter().cloned(),
            self.node_definitions.clone(),
            self.edge_definitions.clone(),
            self.authority_transitions.clone(),
            self.roots.clone(),
        )
    }

    fn canonicalize(&mut self) {
        self.nodes.sort_unstable();
        self.edges.sort_unstable();
        self.node_definitions.sort_unstable();
        self.edge_definitions.sort_unstable();
        self.authority_transitions.sort_unstable();
        self.authority_transitions.dedup();
        self.roots.sort_unstable();
    }
}

/// A registered annotated production L ← K → R, with an explicit preserved interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteProduction {
    id: Arc<str>,
    left: RewriteFragment,
    interface_nodes: BTreeSet<Arc<str>>,
    interface_edges: BTreeSet<Arc<str>>,
    right: RewriteFragment,
}

impl RewriteProduction {
    /// Constructs an interface-preserving production.
    ///
    /// # Errors
    /// Rejects empty identities, invalid topology, or an invalid preserved interface.
    pub fn new(
        id: impl Into<Arc<str>>,
        left: RewriteFragment,
        interface_nodes: BTreeSet<Arc<str>>,
        interface_edges: BTreeSet<Arc<str>>,
        right: RewriteFragment,
    ) -> Result<Self, RewriteError> {
        let mut production = Self {
            id: id.into(),
            left,
            interface_nodes,
            interface_edges,
            right,
        };
        production.left.canonicalize();
        production.right.canonicalize();
        production.check_shape()?;
        Ok(production)
    }

    /// Returns its identity in the permitted grammar.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    fn check_shape(&self) -> Result<(), RewriteError> {
        if self.id.is_empty() {
            return Err(invalid_production("empty production ID"));
        }
        let left = Graph::new(self.left.nodes.clone(), self.left.edges.clone())?;
        let right = Graph::new(self.right.nodes.clone(), self.right.edges.clone())?;
        for node in &self.interface_nodes {
            if left.node(node).is_none() || right.node(node).is_none() {
                return Err(invalid_production(
                    "interface node is absent from a production side",
                ));
            }
        }
        for id in &self.interface_edges {
            let Some(a) = left.edge(id) else {
                return Err(invalid_production("interface edge is absent from L"));
            };
            let Some(b) = right.edge(id) else {
                return Err(invalid_production("interface edge is absent from R"));
            };
            if a != b
                || !self.interface_nodes.contains(a.source())
                || !self.interface_nodes.contains(a.target())
            {
                return Err(invalid_production(
                    "interface edge incidence is not preserved through K",
                ));
            }
        }
        Ok(())
    }
}

/// Immutable permitted productions indexed by identity.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RewriteGrammar {
    productions: BTreeMap<Arc<str>, RewriteProduction>,
}

impl RewriteGrammar {
    /// Registers a set of permitted productions with distinct identities.
    ///
    /// # Errors
    /// Rejects duplicate production IDs.
    pub fn new(
        productions: impl IntoIterator<Item = RewriteProduction>,
    ) -> Result<Self, RewriteError> {
        let mut registered = BTreeMap::new();
        for production in productions {
            if registered
                .insert(Arc::clone(&production.id), production)
                .is_some()
            {
                return Err(invalid_production("duplicate production ID"));
            }
        }
        Ok(Self {
            productions: registered,
        })
    }

    /// Returns the permitted production identified by `id`.
    #[must_use]
    pub fn production(&self, id: &str) -> Option<&RewriteProduction> {
        self.productions.get(id)
    }

    /// Returns all registered productions.
    #[must_use]
    pub fn productions(&self) -> impl ExactSizeIterator<Item = &RewriteProduction> {
        self.productions.values()
    }
}

/// Injective L-to-host bindings and fresh allocations for R elements outside K.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RewriteMatch {
    nodes: BTreeMap<Arc<str>, Arc<str>>,
    edges: BTreeMap<Arc<str>, Arc<str>>,
    fresh_nodes: BTreeMap<Arc<str>, Arc<str>>,
    fresh_edges: BTreeMap<Arc<str>, Arc<str>>,
}

impl RewriteMatch {
    /// Supplies exact symbol bindings; admission checks coverage, injectivity, and freshness.
    #[must_use]
    pub const fn new(
        nodes: BTreeMap<Arc<str>, Arc<str>>,
        edges: BTreeMap<Arc<str>, Arc<str>>,
        fresh_nodes: BTreeMap<Arc<str>, Arc<str>>,
        fresh_edges: BTreeMap<Arc<str>, Arc<str>>,
    ) -> Self {
        Self {
            nodes,
            edges,
            fresh_nodes,
            fresh_edges,
        }
    }
}

/// Selects one permitted production and its concrete embedding/allocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRequest {
    production_id: Arc<str>,
    matching: RewriteMatch,
}

impl RewriteRequest {
    /// Creates a rewrite request; it cannot supply a retirement set or survivor map.
    #[must_use]
    pub fn new(production_id: impl Into<Arc<str>>, matching: RewriteMatch) -> Self {
        Self {
            production_id: production_id.into(),
            matching,
        }
    }
    /// Returns the requested registered production.
    #[must_use]
    pub fn production_id(&self) -> &str {
        &self.production_id
    }
    /// Returns its proposed embedding and fresh allocations.
    #[must_use]
    pub const fn matching(&self) -> &RewriteMatch {
        &self.matching
    }
}

/// Failure to prepare or install a combined rewrite. Preparation never mutates state.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RewriteError {
    /// The graph/annotations failed ordinary definition admission.
    #[error("invalid rewritten definition: {0}")]
    Definition(#[from] DefinitionError),
    /// The production's interface or local semantics are inconsistent.
    #[error("invalid production: {0}")]
    InvalidProduction(Arc<str>),
    /// The embedding, context, or fresh allocation is invalid.
    #[error("invalid rewrite match: {0}")]
    InvalidMatch(Arc<str>),
    /// The requested production is not in the configured grammar.
    #[error("production is not permitted: {0}")]
    UnknownProduction(Arc<str>),
    /// The predecessor belongs to another definition version.
    #[error("state does not belong to this kernel definition")]
    StateMismatch,
    /// The exact state used for preparation is no longer current.
    #[error("prepared operation is stale")]
    Stale,
    /// Revision arithmetic cannot produce a fresh stamp.
    #[error("state revision exhausted")]
    RevisionExhausted,
    /// Required immutable bytes were not provided.
    #[error("missing payload evidence for package {0}")]
    MissingEvidence(PackageId),
    /// Supplied bytes do not match the package's immutable digest.
    #[error("payload evidence does not match package {0}")]
    EvidenceMismatch(PackageId),
    /// External evidence storage failed while supplying required bytes.
    #[error("payload evidence is unavailable: {0}")]
    EvidenceUnavailable(Arc<str>),
    /// Trusted contract code panicked instead of returning a predicate result.
    #[error("contract validator panicked: {0}")]
    ValidatorPanicked(Arc<str>),
    /// An internal/imported state violates the canonical frontier shape.
    #[error("invalid frontier state: {0}")]
    InvalidState(Arc<str>),
}

/// Failure to admit the single transfer of an outbound package.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum TransferError {
    /// Shared state/evidence admission failed.
    #[error(transparent)]
    Admission(#[from] RewriteError),
    /// The package is absent from the live frontier.
    #[error("package is not live: {0}")]
    NotLive(PackageId),
    /// Only an outbound, never-delivered package may transfer.
    #[error("package is not awaiting transfer: {0}")]
    NotOutbound(PackageId),
    /// The selected edge does not leave the current holder or does not exist.
    #[error("edge does not leave the current package holder: {0}")]
    InvalidEdge(Arc<str>),
    /// The edge's type, authority, or payload predicate rejected the package.
    #[error("edge rejected package {0}")]
    Rejected(PackageId),
}

/// Selected facts from canonical state, held stable through admission and commit.
/// Storage adapters validate their row shape before supplying this observation;
/// accepted provenance establishes that an outbound holder is its producer.
pub(crate) struct TransferObservation<'a> {
    pub(crate) package: Option<&'a Package>,
    pub(crate) position: Option<&'a Position>,
    pub(crate) delivered: bool,
    pub(crate) consumed: bool,
}

fn invalid_production(message: &str) -> RewriteError {
    RewriteError::InvalidProduction(Arc::from(message))
}
fn invalid_match(message: &str) -> RewriteError {
    RewriteError::InvalidMatch(Arc::from(message))
}
fn invalid_state(message: &str) -> RewriteError {
    RewriteError::InvalidState(Arc::from(message))
}

/// A fully admitted graph/frontier replacement bound to its exact predecessor.
#[derive(Clone, Debug)]
pub struct PreparedRewrite {
    base: Box<State>,
    next_kernel: Arc<Kernel>,
    positions: BTreeMap<PackageId, Position>,
    retired: BTreeMap<PackageId, RetirementReason>,
    fresh_node_ids: BTreeSet<Arc<str>>,
    fresh_edge_ids: BTreeSet<Arc<str>>,
}

impl PreparedRewrite {
    /// Returns the complete admitted replacement definition for review.
    #[must_use]
    pub const fn next_kernel(&self) -> &Arc<Kernel> {
        &self.next_kernel
    }
    /// Returns the exact package retirements induced by this rewrite.
    #[must_use]
    pub const fn retirements(&self) -> &BTreeMap<PackageId, RetirementReason> {
        &self.retired
    }
    /// Returns the exact predecessor revision used by preparation.
    #[must_use]
    pub fn base_revision(&self) -> u64 {
        self.base.revision
    }

    /// Consumes the predecessor after its owner has established that it is still current.
    /// The `SQLite` owner uses its exclusive session identity, revision and graph binding;
    /// the public kernel commit checks exact state equality.
    pub(crate) fn into_successor(self) -> Result<(State, Arc<Kernel>), RewriteError> {
        let mut next = *self.base;
        next.positions = self.positions;
        next.definition_fingerprint = *self.next_kernel.fingerprint();
        next.used_node_ids.extend(self.fresh_node_ids);
        next.used_edge_ids.extend(self.fresh_edge_ids);
        next.revision = next
            .revision
            .checked_add(1)
            .ok_or(RewriteError::RevisionExhausted)?;
        Ok((next, self.next_kernel))
    }
}

/// One fully admitted transfer bound to its exact predecessor.
#[derive(Clone, Debug)]
pub struct PreparedTransfer {
    base: Box<State>,
    package_id: PackageId,
    delivery: Delivery,
}

impl PreparedTransfer {
    /// Returns the package that will be delivered.
    #[must_use]
    pub const fn package_id(&self) -> PackageId {
        self.package_id
    }
    /// Returns its admitted delivery evidence.
    #[must_use]
    pub const fn delivery(&self) -> &Delivery {
        &self.delivery
    }
    /// Returns the predecessor revision used by preparation.
    #[must_use]
    pub fn base_revision(&self) -> u64 {
        self.base.revision
    }
}

fn same_local_definition(left: &Kernel, a: &str, right: &Kernel, b: &str) -> bool {
    let (Some(a_def), Some(b_def)) = (left.node_definition(a), right.node_definition(b)) else {
        return false;
    };
    a_def.types() == b_def.types()
        && a_def.result_contract() == b_def.result_contract()
        && a_def.ingress_mode() == b_def.ingress_mode()
        && left.root_ceiling(a) == right.root_ceiling(b)
        && left
            .authority_transitions()
            .iter()
            .filter(|rule| rule.node_id() == a)
            .map(|rule| (rule.from(), rule.to()))
            .eq(right
                .authority_transitions()
                .iter()
                .filter(|rule| rule.node_id() == b)
                .map(|rule| (rule.from(), rule.to())))
}

fn same_edge_definition(a: &EdgeDefinition, b: &EdgeDefinition) -> bool {
    a.types() == b.types()
        && a.source_requirements() == b.source_requirements()
        && a.target_requirements() == b.target_requirements()
        && a.package_contract() == b.package_contract()
        && a.authority_tags() == b.authority_tags()
        && a.authority_match() == b.authority_match()
}

fn exact_bindings(map: &BTreeMap<Arc<str>, Arc<str>>, expected: BTreeSet<Arc<str>>) -> bool {
    map.keys().cloned().collect::<BTreeSet<_>>() == expected
        && map.values().collect::<BTreeSet<_>>().len() == map.len()
        && map.values().all(|value| !value.is_empty())
}

type StructuralResult = (
    Kernel,
    BTreeMap<Arc<str>, Arc<str>>,
    BTreeSet<Arc<str>>,
    BTreeSet<Arc<str>>,
);

impl Kernel {
    pub(crate) fn admit_fragment(
        &self,
        fragment: &RewriteFragment,
    ) -> Result<Self, DefinitionError> {
        fragment.admit(self)
    }

    fn check_rewrite_state(&self, state: &State) -> Result<(), RewriteError> {
        if state.definition_id != *self.id() || state.definition_fingerprint != *self.fingerprint()
        {
            return Err(RewriteError::StateMismatch);
        }
        state
            .revision
            .checked_add(1)
            .ok_or(RewriteError::RevisionExhausted)?;
        Ok(())
    }

    fn structural_rewrite(
        &self,
        state: &State,
        production: &RewriteProduction,
        matching: &RewriteMatch,
    ) -> Result<StructuralResult, RewriteError> {
        let left = production.left.admit(self)?;
        let right = production.right.admit(self)?;
        for symbol in &production.interface_nodes {
            if !same_local_definition(&left, symbol, &right, symbol) {
                return Err(invalid_production(
                    "preserved node changes its local definition",
                ));
            }
        }
        for symbol in &production.interface_edges {
            if left.edge_definition(symbol) != right.edge_definition(symbol) {
                return Err(invalid_production("preserved edge changes annotations"));
            }
        }
        let left_nodes = left.graph().nodes().iter().map(Node::id_arc).collect();
        let left_edges = left.graph().edges().iter().map(Edge::id_arc).collect();
        let new_nodes = right
            .graph()
            .nodes()
            .iter()
            .filter(|node| !production.interface_nodes.contains(node.id()))
            .map(Node::id_arc)
            .collect();
        let new_edges = right
            .graph()
            .edges()
            .iter()
            .filter(|edge| !production.interface_edges.contains(edge.id()))
            .map(Edge::id_arc)
            .collect();
        if !exact_bindings(&matching.nodes, left_nodes)
            || !exact_bindings(&matching.edges, left_edges)
            || !exact_bindings(&matching.fresh_nodes, new_nodes)
            || !exact_bindings(&matching.fresh_edges, new_edges)
        {
            return Err(invalid_match(
                "bindings must cover exactly L and fresh R elements injectively",
            ));
        }
        for (symbol, actual) in &matching.nodes {
            if !same_local_definition(&left, symbol, self, actual) {
                return Err(invalid_match(
                    "node match does not preserve annotations and local policy",
                ));
            }
        }
        for edge in left.graph().edges() {
            let actual = self
                .graph()
                .edge(&matching.edges[edge.id()])
                .ok_or_else(|| invalid_match("matched edge is absent"))?;
            if actual.source() != &*matching.nodes[edge.source()]
                || actual.target() != &*matching.nodes[edge.target()]
                || !same_edge_definition(
                    left.edge_definition(edge.id()).expect("admitted L edge"),
                    self.edge_definition(actual.id())
                        .expect("admitted host edge"),
                )
            {
                return Err(invalid_match(
                    "edge match does not preserve incidence and annotations",
                ));
            }
        }
        if matching
            .fresh_nodes
            .values()
            .any(|id| state.used_node_ids.contains(id))
            || matching
                .fresh_edges
                .values()
                .any(|id| state.used_edge_ids.contains(id))
        {
            return Err(invalid_match(
                "fresh identity has already been used in this workflow",
            ));
        }
        let deleted_nodes: BTreeSet<_> = matching
            .nodes
            .iter()
            .filter(|(symbol, _)| !production.interface_nodes.contains(*symbol))
            .map(|(_, id)| id.clone())
            .collect();
        let deleted_edges: BTreeSet<_> = matching
            .edges
            .iter()
            .filter(|(symbol, _)| !production.interface_edges.contains(*symbol))
            .map(|(_, id)| id.clone())
            .collect();
        if self.graph().edges().iter().any(|edge| {
            (deleted_nodes.contains(edge.source()) || deleted_nodes.contains(edge.target()))
                && !deleted_edges.contains(edge.id())
        }) {
            return Err(invalid_match(
                "deleted node has an unmatched dangling incident edge",
            ));
        }

        let mut manifest = RewriteFragment::from_kernel(self);
        manifest
            .nodes
            .retain(|node| !deleted_nodes.contains(node.id()));
        manifest
            .node_definitions
            .retain(|node| !deleted_nodes.contains(node.node_id()));
        manifest
            .roots
            .retain(|root| !deleted_nodes.contains(root.node_id()));
        manifest
            .authority_transitions
            .retain(|rule| !deleted_nodes.contains(rule.node_id()));
        manifest
            .edges
            .retain(|edge| !deleted_edges.contains(edge.id()));
        manifest
            .edge_definitions
            .retain(|edge| !deleted_edges.contains(edge.edge_id()));
        let right_node = |symbol: &str| -> &Arc<str> {
            if production.interface_nodes.contains(symbol) {
                &matching.nodes[symbol]
            } else {
                &matching.fresh_nodes[symbol]
            }
        };
        for (symbol, actual) in &matching.fresh_nodes {
            let definition = right
                .node_definition(symbol)
                .expect("fresh R node was checked");
            manifest.nodes.push(Node::new(Arc::clone(actual))?);
            manifest.node_definitions.push(
                NodeDefinition::new(
                    Arc::clone(actual),
                    definition.types().iter().cloned(),
                    definition.result_contract(),
                )?
                .with_ingress_mode(definition.ingress_mode()),
            );
            if let Some(ceiling) = right.root_ceiling(symbol) {
                manifest
                    .roots
                    .push(RootRule::new(Arc::clone(actual), ceiling.clone())?);
            }
            for rule in right
                .authority_transitions()
                .iter()
                .filter(|rule| rule.node_id() == &**symbol)
            {
                manifest
                    .authority_transitions
                    .push(AuthorityTransitionRule::new(
                        Arc::clone(actual),
                        rule.from().clone(),
                        rule.to().clone(),
                    )?);
            }
        }
        for (symbol, actual) in &matching.fresh_edges {
            let edge = right
                .graph()
                .edge(symbol)
                .expect("fresh R edge was checked");
            let definition = right
                .edge_definition(symbol)
                .expect("fresh R edge definition was checked");
            manifest.edges.push(Edge::new(
                Arc::clone(actual),
                Arc::clone(right_node(edge.source())),
                Arc::clone(right_node(edge.target())),
            )?);
            manifest.edge_definitions.push(
                EdgeDefinition::new(
                    Arc::clone(actual),
                    definition.types().iter().cloned(),
                    definition.source_requirements().iter().cloned(),
                    definition.target_requirements().iter().cloned(),
                    definition.package_contract(),
                    definition.authority_tags().iter().cloned(),
                )?
                .with_authority_match(definition.authority_match()),
            );
        }
        let next = manifest.admit(self)?;
        let survivors = self
            .graph()
            .nodes()
            .iter()
            .filter(|node| !deleted_nodes.contains(node.id()))
            .map(|node| (node.id_arc(), node.id_arc()))
            .collect();
        let fresh_nodes = matching.fresh_nodes.values().cloned().collect();
        let fresh_edges = matching.fresh_edges.values().cloned().collect();
        Ok((next, survivors, fresh_nodes, fresh_edges))
    }

    fn accepts_package(
        &self,
        edge_id: &str,
        package_id: PackageId,
        package: &Package,
        bytes: impl FnOnce() -> Result<Payload, RewriteError>,
    ) -> Result<bool, RewriteError> {
        let (_, edge, _, contract) = self
            .admitted_edge(edge_id)
            .ok_or_else(|| invalid_state("acceptance edge is absent"))?;
        if package.object_type() != contract.object_type()
            || !edge.matches_authority(package.authority())
        {
            return Ok(false);
        }
        let payload = bytes()?;
        if !package.content_digest().verifies(&payload) {
            return Err(RewriteError::EvidenceMismatch(package_id));
        }
        catch_unwind(AssertUnwindSafe(|| contract.validate(&payload)))
            .map(|result| result.is_ok())
            .map_err(|_| RewriteError::ValidatorPanicked(Arc::from(contract.id())))
    }

    /// Admits structural rewriting and derives its exact frontier cleanup.
    ///
    /// # Errors
    /// Rejects an unregistered/invalid production or match, invalid state, or missing/invalid evidence.
    pub fn prepare_rewrite(
        &self,
        state: &State,
        grammar: &RewriteGrammar,
        request: &RewriteRequest,
        evidence: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<PreparedRewrite, RewriteError> {
        self.prepare_rewrite_with_evidence(state, grammar, request, |package_id, digest| {
            evidence
                .get(&digest)
                .cloned()
                .ok_or(RewriteError::MissingEvidence(package_id))
        })
    }

    /// Admits a rewrite while requesting payload evidence only when needed.
    ///
    /// Removed holders, delivered packages, absent routes, and metadata-rejected
    /// edges never cause a payload read. Supplied bytes are verified by the kernel.
    /// # Errors
    /// Returns structural, state, or required-evidence errors without mutation.
    pub fn prepare_rewrite_with_evidence(
        &self,
        state: &State,
        grammar: &RewriteGrammar,
        request: &RewriteRequest,
        mut payload_for: impl FnMut(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<PreparedRewrite, RewriteError> {
        self.check_rewrite_state(state)?;
        let production = grammar
            .production(&request.production_id)
            .ok_or_else(|| RewriteError::UnknownProduction(Arc::clone(&request.production_id)))?;
        let (next, survivors, fresh_node_ids, fresh_edge_ids) =
            self.structural_rewrite(state, production, &request.matching)?;
        let cleaned = cleanup(
            &state.positions,
            &survivors,
            |holder, package_id| -> Result<bool, RewriteError> {
                let package = state
                    .package(package_id)
                    .ok_or_else(|| invalid_state("frontier names unknown package"))?;
                for edge in next
                    .graph()
                    .edges()
                    .iter()
                    .filter(|edge| edge.source() == holder)
                {
                    if next.accepts_package(edge.id(), package_id, package, || {
                        payload_for(package_id, package.content_digest())
                    })? {
                        return Ok(true);
                    }
                }
                Ok(false)
            },
        )?;
        Ok(PreparedRewrite {
            base: Box::new(state.clone()),
            next_kernel: Arc::new(next),
            positions: cleaned.positions,
            retired: cleaned.retired,
            fresh_node_ids,
            fresh_edge_ids,
        })
    }

    /// Installs the admitted frontier and returns its replacement kernel.
    ///
    /// The owner must install the returned kernel in the same externally serialized operation.
    /// # Errors
    /// Rejects a mismatched kernel or any state change since preparation.
    pub fn commit_rewrite(
        &self,
        state: &mut State,
        prepared: PreparedRewrite,
    ) -> Result<Arc<Kernel>, RewriteError> {
        self.check_rewrite_state(state)?;
        if *state != *prepared.base {
            return Err(RewriteError::Stale);
        }
        let (next, kernel) = prepared.into_successor()?;
        *state = next;
        Ok(kernel)
    }

    /// Admits one explicit Out→In transfer using exact payload evidence.
    ///
    /// # Errors
    /// Rejects non-live/already delivered packages, invalid edges, contract rejection, or invalid evidence.
    pub fn prepare_transfer(
        &self,
        state: &State,
        package_id: PackageId,
        edge_id: &str,
        payload: &[u8],
    ) -> Result<PreparedTransfer, TransferError> {
        self.prepare_transfer_with_evidence(state, package_id, edge_id, |_, _| {
            Ok(Arc::from(payload))
        })
    }

    /// Admits one transfer, requesting exact bytes only after liveness and metadata checks.
    ///
    /// # Errors
    /// Rejects invalid custody/edges, contract rejection, or unavailable/mismatched required evidence.
    pub fn prepare_transfer_with_evidence(
        &self,
        state: &State,
        package_id: PackageId,
        edge_id: &str,
        payload_for: impl FnOnce(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<PreparedTransfer, TransferError> {
        self.check_rewrite_state(state)?;
        let delivery = self.evaluate_transfer(
            package_id,
            edge_id,
            TransferObservation {
                package: state.package(package_id),
                position: state.position(package_id),
                delivered: state.deliveries.contains_key(&package_id),
                consumed: state.package_consumer(package_id).is_some(),
            },
            payload_for,
        )?;
        Ok(PreparedTransfer {
            base: Box::new(state.clone()),
            package_id,
            delivery,
        })
    }

    /// Proves one transfer from selected canonical facts without traversing history.
    /// The caller binds the current graph and revision and keeps the observation
    /// stable until commit. Evidence is requested only after custody and metadata checks.
    pub(crate) fn evaluate_transfer(
        &self,
        package_id: PackageId,
        edge_id: &str,
        observation: TransferObservation<'_>,
        payload_for: impl FnOnce(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<Delivery, TransferError> {
        let position = observation
            .position
            .filter(|_| !observation.consumed)
            .ok_or(TransferError::NotLive(package_id))?;
        if position.phase != Phase::Out || observation.delivered {
            return Err(TransferError::NotOutbound(package_id));
        }
        let package = observation
            .package
            .ok_or_else(|| invalid_state("live package record is absent"))?;
        if self.graph().node(position.holder()).is_none()
            || package.node_id() != position.holder()
            || package.edge_id().is_some()
            || !self.schema().admits_object_type(package.object_type())
            || !self.schema().admits_authority(package.authority())
        {
            return Err(invalid_state("outbound package metadata is inconsistent").into());
        }
        let edge = self
            .graph()
            .edge(edge_id)
            .filter(|edge| edge.source() == position.holder())
            .ok_or_else(|| TransferError::InvalidEdge(Arc::from(edge_id)))?;
        if !self.accepts_package(edge_id, package_id, package, || {
            payload_for(package_id, package.content_digest())
        })? {
            return Err(TransferError::Rejected(package_id));
        }
        Ok(Delivery::new(edge.id(), edge.source(), edge.target()))
    }

    /// Installs a prepared single delivery if its exact predecessor remains current.
    ///
    /// # Errors
    /// Rejects stale state/definition or exhausted revision stamps without mutation.
    pub fn commit_transfer(
        &self,
        state: &mut State,
        prepared: PreparedTransfer,
    ) -> Result<Delivery, TransferError> {
        self.check_rewrite_state(state)?;
        if *state != *prepared.base {
            return Err(RewriteError::Stale.into());
        }
        let mut next = *prepared.base;
        next.positions.insert(
            prepared.package_id,
            Position::new(Arc::clone(&prepared.delivery.receiver), Phase::In),
        );
        next.deliveries
            .insert(prepared.package_id, prepared.delivery.clone());
        let package = next
            .packages
            .get_mut(&prepared.package_id)
            .ok_or_else(|| invalid_state("prepared package is absent"))?;
        package.edge_id = Some(Arc::clone(&prepared.delivery.edge_id));
        package.node_id = Arc::clone(&prepared.delivery.receiver);
        next.revision = next
            .revision
            .checked_add(1)
            .ok_or(RewriteError::RevisionExhausted)?;
        *state = next;
        Ok(prepared.delivery)
    }
}
