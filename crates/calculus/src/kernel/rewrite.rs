//! Admitted interface-preserving rewrites and explicit package transfer.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use thiserror::Error;

use crate::graph::{
    AuthorityTransitionRule, ContentDigest, DefinitionError, Edge, EdgeDefinition, Graph,
    IngressMode, Node, NodeDefinition, Payload, RootRule,
};

use super::definition::Kernel;
use super::frontier::{Delivery, Retirement, RetirementReason, cleanup};
use super::occurrence::{PackageId, PackageRecord, State};
use super::transition::{ApplyError, FrontierView, PackageView, Transition, TransitionKind};

/// One annotated fragment in a production; its identifiers are rule-local symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteFragment {
    pub(crate) nodes: Vec<Node>,
    pub(crate) edges: Vec<Edge>,
    pub(crate) node_definitions: Vec<NodeDefinition>,
    pub(crate) edge_definitions: Vec<EdgeDefinition>,
    pub(crate) authority_transitions: Vec<AuthorityTransitionRule>,
    pub(crate) roots: Vec<RootRule>,
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
    /// Creates a rewrite request; it cannot supply a retirement set.
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

impl From<ApplyError> for RewriteError {
    fn from(error: ApplyError) -> Self {
        match error {
            ApplyError::BindingMismatch => Self::Stale,
            other => Self::InvalidState(Arc::from(other.to_string())),
        }
    }
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

fn invalid_production(message: &str) -> RewriteError {
    RewriteError::InvalidProduction(Arc::from(message))
}
fn invalid_match(message: &str) -> RewriteError {
    RewriteError::InvalidMatch(Arc::from(message))
}
pub(super) fn invalid_state(message: &str) -> RewriteError {
    RewriteError::InvalidState(Arc::from(message))
}

/// A fully admitted graph/frontier replacement bound to its exact predecessor.
#[derive(Clone, Debug)]
pub struct PreparedRewrite {
    transition: Transition,
    next_kernel: Arc<Kernel>,
}

impl PreparedRewrite {
    /// Returns the complete admitted replacement definition for review.
    #[must_use]
    pub const fn next_kernel(&self) -> &Arc<Kernel> {
        &self.next_kernel
    }
    /// Projects the exact package retirements induced by this rewrite.
    #[must_use]
    pub fn retirements(&self) -> BTreeMap<PackageId, RetirementReason> {
        self.transition.retirements()
    }
    /// Returns the evaluated transition, for an adapter to apply.
    #[must_use]
    pub const fn transition(&self) -> &Transition {
        &self.transition
    }
}

/// One fully admitted transfer bound to its exact predecessor.
#[derive(Clone, Debug)]
pub struct PreparedTransfer {
    transition: Transition,
}

impl PreparedTransfer {
    fn parts(&self) -> (PackageId, &Delivery) {
        match &self.transition.kind {
            TransitionKind::Transfer { package, delivery } => (*package, delivery),
            _ => unreachable!("a prepared transfer holds a transfer transition"),
        }
    }
    /// Returns the package that will be delivered.
    #[must_use]
    pub fn package_id(&self) -> PackageId {
        self.parts().0
    }
    /// Returns its admitted delivery.
    #[must_use]
    pub fn delivery(&self) -> &Delivery {
        self.parts().1
    }
    /// Returns the evaluated transition, for an adapter to apply.
    #[must_use]
    pub const fn transition(&self) -> &Transition {
        &self.transition
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

fn outgoing_by_source(graph: &Graph) -> BTreeMap<&str, BTreeSet<&str>> {
    let mut outgoing = graph
        .nodes()
        .iter()
        .map(|node| (node.id(), BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for edge in graph.edges() {
        outgoing.entry(edge.source()).or_default().insert(edge.id());
    }
    outgoing
}

/// Nodes of `before` whose outgoing edge identity set differs in `after`.
///
/// Edge identities fix their annotations for a workflow lifetime, so an
/// unchanged identity set means unchanged acceptance.
fn changed_outgoing_sources<'a>(before: &'a Graph, after: &Graph) -> BTreeSet<&'a str> {
    let after = outgoing_by_source(after);
    outgoing_by_source(before)
        .into_iter()
        .filter(|(source, edges)| after.get(source) != Some(edges))
        .map(|(source, _)| source)
        .collect()
}

fn exact_bindings(map: &BTreeMap<Arc<str>, Arc<str>>, expected: BTreeSet<Arc<str>>) -> bool {
    map.keys().cloned().collect::<BTreeSet<_>>() == expected
        && map.values().collect::<BTreeSet<_>>().len() == map.len()
        && map.values().all(|value| !value.is_empty())
}

/// The admitted successor definition and the identities the rewrite touches.
struct StructuralResult {
    next: Kernel,
    deleted_nodes: BTreeSet<Arc<str>>,
    fresh_node_ids: BTreeSet<Arc<str>>,
    fresh_edge_ids: BTreeSet<Arc<str>>,
}

impl Kernel {
    /// Admits a fragment as a complete definition under this kernel's
    /// identity, schema, and contracts.
    ///
    /// # Errors
    /// Returns the definition error when the fragment is not a valid definition.
    pub fn admit_fragment(&self, fragment: &RewriteFragment) -> Result<Self, DefinitionError> {
        fragment.admit(self)
    }

    fn structural_rewrite(
        &self,
        used_node_ids: &BTreeSet<Arc<str>>,
        used_edge_ids: &BTreeSet<Arc<str>>,
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
            .any(|id| used_node_ids.contains(id))
            || matching
                .fresh_edges
                .values()
                .any(|id| used_edge_ids.contains(id))
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
        Ok(StructuralResult {
            next,
            deleted_nodes,
            fresh_node_ids: matching.fresh_nodes.values().cloned().collect(),
            fresh_edge_ids: matching.fresh_edges.values().cloned().collect(),
        })
    }

    fn accepts_package(
        &self,
        edge_id: &str,
        package_id: PackageId,
        record: &PackageRecord,
        bytes: impl FnOnce() -> Result<Payload, RewriteError>,
    ) -> Result<bool, RewriteError> {
        let (_, edge, _, contract) = self
            .admitted_edge(edge_id)
            .ok_or_else(|| invalid_state("acceptance edge is absent"))?;
        if record.object_type() != contract.object_type()
            || !edge.matches_authority(record.authority())
        {
            return Ok(false);
        }
        let payload = bytes()?;
        if !record.content_digest().verifies(&payload) {
            return Err(RewriteError::EvidenceMismatch(package_id));
        }
        catch_unwind(AssertUnwindSafe(|| contract.validate(&payload)))
            .map(|result| result.is_ok())
            .map_err(|_| RewriteError::ValidatorPanicked(Arc::from(contract.id())))
    }

    /// Evaluates a rewrite over a frontier view without mutating anything.
    ///
    /// Cleanup is local to the rewrite. An `Out` package is rechecked against
    /// every outgoing edge of its holder exactly when the holder's outgoing
    /// edge identity set changed, whether by removal or by addition; an
    /// unchanged holder keeps its packages even if none is routable. An `In`
    /// package is retired only when its holder is an `All` receiver whose
    /// incoming edge set no longer contains the delivery edge. Removed
    /// holders, delivered packages, unchanged holders, absent routes, and
    /// metadata-rejected edges never cause a payload read. Supplied bytes are
    /// verified by the kernel. Only the live frontier and lifetime identities
    /// are read; history is never materialized.
    ///
    /// # Errors
    /// Returns structural, state, or required-evidence errors.
    pub fn evaluate_rewrite(
        &self,
        frontier: &dyn FrontierView,
        grammar: &RewriteGrammar,
        request: &RewriteRequest,
        mut payload_for: impl FnMut(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<(Transition, Arc<Self>), RewriteError> {
        let binding = frontier.binding();
        let successor_revision = self.check_binding(&binding)?;
        let production = grammar
            .production(&request.production_id)
            .ok_or_else(|| RewriteError::UnknownProduction(Arc::clone(&request.production_id)))?;
        let StructuralResult {
            next,
            deleted_nodes,
            fresh_node_ids,
            fresh_edge_ids,
        } = self.structural_rewrite(
            &frontier.used_node_ids(),
            &frontier.used_edge_ids(),
            production,
            &request.matching,
        )?;
        let changed_sources = changed_outgoing_sources(self.graph(), next.graph());
        let live = frontier.live();
        let retired = cleanup(
            live.iter().map(|(id, record)| (*id, record)),
            &deleted_nodes,
            |package_id, record| -> Result<bool, RewriteError> {
                let holder = record.holder();
                if !changed_sources.contains(holder) {
                    return Ok(true);
                }
                for edge in next
                    .graph()
                    .edges()
                    .iter()
                    .filter(|edge| edge.source() == holder)
                {
                    if next.accepts_package(edge.id(), package_id, record, || {
                        payload_for(package_id, record.content_digest())
                    })? {
                        return Ok(true);
                    }
                }
                Ok(false)
            },
            |_, record| -> Result<bool, RewriteError> {
                let delivery = record
                    .delivery()
                    .ok_or_else(|| invalid_state("received package has no delivery"))?;
                let holder = record.holder();
                let node = next
                    .node_definition(holder)
                    .ok_or_else(|| invalid_state("surviving holder is absent from the result"))?;
                Ok(match node.ingress_mode() {
                    IngressMode::Any => true,
                    IngressMode::All => next.incoming_edge_ids(holder).contains(&delivery.edge_id),
                })
            },
        )?;
        let transition = Transition {
            base: binding,
            kind: TransitionKind::Rewrite {
                retirements: retired
                    .iter()
                    .map(|(package, reason)| {
                        (*package, Retirement::new(*reason, successor_revision, None))
                    })
                    .collect(),
                fresh_node_ids,
                fresh_edge_ids,
                next_nodes: next.graph().nodes().iter().map(Node::id_arc).collect(),
                next_fingerprint: *next.fingerprint(),
            },
        };
        Ok((transition, Arc::new(next)))
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
    /// See [`Self::evaluate_rewrite`] for the cleanup rule.
    /// # Errors
    /// Returns structural, state, or required-evidence errors without mutation.
    pub fn prepare_rewrite_with_evidence(
        &self,
        state: &State,
        grammar: &RewriteGrammar,
        request: &RewriteRequest,
        payload_for: impl FnMut(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<PreparedRewrite, RewriteError> {
        let (transition, next_kernel) =
            self.evaluate_rewrite(state, grammar, request, payload_for)?;
        Ok(PreparedRewrite {
            transition,
            next_kernel,
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
    ) -> Result<Arc<Self>, RewriteError> {
        self.check_binding(&state.binding())?;
        state.apply(self, &prepared.transition)?;
        Ok(prepared.next_kernel)
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
        let transition = self.evaluate_transfer(state, package_id, edge_id, payload_for)?;
        Ok(PreparedTransfer { transition })
    }

    /// Evaluates one transfer against a view without mutating anything.
    ///
    /// Evidence is requested only after custody and metadata checks.
    ///
    /// # Errors
    /// Rejects invalid custody/edges, contract rejection, or unavailable/mismatched evidence.
    pub fn evaluate_transfer(
        &self,
        view: &dyn PackageView,
        package_id: PackageId,
        edge_id: &str,
        payload_for: impl FnOnce(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<Transition, TransferError> {
        let binding = view.binding();
        self.check_binding(&binding)?;
        let record = view
            .record(package_id)
            .filter(PackageRecord::is_live)
            .ok_or(TransferError::NotLive(package_id))?;
        if record.delivery.is_some() {
            return Err(TransferError::NotOutbound(package_id));
        }
        let holder = record.producer_node();
        if self.graph().node(holder).is_none()
            || !self.schema().admits_object_type(record.object_type())
            || !self.schema().admits_authority(record.authority())
        {
            return Err(invalid_state("outbound package metadata is inconsistent").into());
        }
        let edge = self
            .graph()
            .edge(edge_id)
            .filter(|edge| edge.source() == holder)
            .ok_or_else(|| TransferError::InvalidEdge(Arc::from(edge_id)))?;
        if !self.accepts_package(edge_id, package_id, &record, || {
            payload_for(package_id, record.content_digest())
        })? {
            return Err(TransferError::Rejected(package_id));
        }
        Ok(Transition {
            base: binding,
            kind: TransitionKind::Transfer {
                package: package_id,
                delivery: Delivery::new(edge.id(), edge.target()),
            },
        })
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
        self.check_binding(&state.binding())?;
        state
            .apply(self, &prepared.transition)
            .map_err(RewriteError::from)?;
        Ok(prepared.delivery().clone())
    }
}
