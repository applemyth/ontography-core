//! Admitted graph edits and explicit package transfer.
//!
//! A rewrite installs an explicit [`GraphEdit`]: existing nodes and edges to
//! remove and a fragment of fresh ones to add. The kernel admits the definition
//! the edit produces and derives its frontier cleanup; a trusted
//! [`EditPolicy`] then decides whether the requesting [`Principal`] may make
//! the edit.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use thiserror::Error;

use crate::graph::{
    AuthorityTransitionRule, ContentDigest, ContractViolation, DefinitionError, Edge,
    EdgeDefinition, Graph, IngressMode, Node, NodeDefinition, Payload, RootRule,
};

use super::definition::Kernel;
use super::frontier::{Delivery, Retirement, RetirementReason, cleanup};
use super::occurrence::{PackageId, PackageRecord, State};
use super::policy::{EditContext, EditPolicy, Principal};
use super::transition::{ApplyError, FrontierView, PackageView, Transition, TransitionKind};

/// An annotated graph fragment: nodes and edges with their definitions, root
/// rules, and authority transitions.
///
/// A fragment is what a [`GraphEdit`] adds, and the form in which adapters
/// encode a whole definition. Its contents are checked only when the
/// definition it belongs to is admitted.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GraphFragment {
    pub(crate) nodes: Vec<Node>,
    pub(crate) edges: Vec<Edge>,
    pub(crate) node_definitions: Vec<NodeDefinition>,
    pub(crate) edge_definitions: Vec<EdgeDefinition>,
    pub(crate) authority_transitions: Vec<AuthorityTransitionRule>,
    pub(crate) roots: Vec<RootRule>,
}

impl GraphFragment {
    /// Collects a fragment; admission checks its topology and annotations.
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

    /// Returns an admitted definition's graph and annotations as a fragment.
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

    /// Returns the nodes.
    #[must_use]
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Returns the edges.
    #[must_use]
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    /// Returns the node definitions.
    #[must_use]
    pub fn node_definitions(&self) -> &[NodeDefinition] {
        &self.node_definitions
    }

    /// Returns the edge definitions.
    #[must_use]
    pub fn edge_definitions(&self) -> &[EdgeDefinition] {
        &self.edge_definitions
    }

    /// Returns the authority transition rules.
    #[must_use]
    pub fn authority_transitions(&self) -> &[AuthorityTransitionRule] {
        &self.authority_transitions
    }

    /// Returns the root rules.
    #[must_use]
    pub fn roots(&self) -> &[RootRule] {
        &self.roots
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
}

/// An explicit change to a workflow graph.
///
/// It removes existing nodes and edges and adds a fragment of new ones, all in
/// one transition. Every edge touching a removed node must itself be removed,
/// so an edit never drops an edge implicitly. Added nodes and edges carry
/// identities never used before in the workflow, and the fragment may define,
/// root, or give authority transitions only to added elements: a surviving
/// node or edge keeps its definition, and changing one means replacing it.
/// Added edges may connect surviving and added nodes. The empty edit is legal
/// and changes nothing but the revision.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GraphEdit {
    remove_nodes: BTreeSet<Arc<str>>,
    remove_edges: BTreeSet<Arc<str>>,
    add: GraphFragment,
}

impl GraphEdit {
    /// Describes an edit; admission checks it against the current state.
    #[must_use]
    pub const fn new(
        remove_nodes: BTreeSet<Arc<str>>,
        remove_edges: BTreeSet<Arc<str>>,
        add: GraphFragment,
    ) -> Self {
        Self {
            remove_nodes,
            remove_edges,
            add,
        }
    }

    /// Returns the nodes to remove.
    #[must_use]
    pub const fn remove_nodes(&self) -> &BTreeSet<Arc<str>> {
        &self.remove_nodes
    }

    /// Returns the edges to remove.
    #[must_use]
    pub const fn remove_edges(&self) -> &BTreeSet<Arc<str>> {
        &self.remove_edges
    }

    /// Returns the fragment to add.
    #[must_use]
    pub const fn add(&self) -> &GraphFragment {
        &self.add
    }
}

/// A principal's request to install one graph edit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteRequest {
    principal: Principal,
    edit: GraphEdit,
}

impl RewriteRequest {
    /// Creates a rewrite request.
    #[must_use]
    pub const fn new(principal: Principal, edit: GraphEdit) -> Self {
        Self { principal, edit }
    }

    /// Returns the principal asking for the edit.
    #[must_use]
    pub const fn principal(&self) -> &Principal {
        &self.principal
    }

    /// Returns the requested edit.
    #[must_use]
    pub const fn edit(&self) -> &GraphEdit {
        &self.edit
    }
}

/// Failure to prepare or install a rewrite. Preparation never mutates state.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RewriteError {
    /// The edited graph/annotations failed ordinary definition admission.
    #[error("invalid rewritten definition: {0}")]
    Definition(#[from] DefinitionError),
    /// The edit does not fit the current graph or its lifetime identities.
    #[error("invalid graph edit: {0}")]
    InvalidEdit(Arc<str>),
    /// The workflow's edit policy refused the edit.
    #[error("edit refused: {0}")]
    Denied(Arc<str>),
    /// The trusted edit policy panicked instead of deciding.
    #[error("edit policy panicked")]
    PolicyPanicked,
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
    /// A prepared rewrite came from a different validator registry.
    #[error("prepared rewrite changes contract {0}")]
    ContractChanged(Arc<str>),
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
    #[error("edge rejected package {package}: {reason}")]
    Rejected {
        /// Rejected package occurrence.
        package: PackageId,
        /// Admission premise the edge did not satisfy.
        reason: TransferRejection,
    },
}

/// Why a selected edge does not accept an otherwise transferable package.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum TransferRejection {
    /// The package object type differs from the edge contract's object type.
    #[error("object type {actual} differs from required {expected}")]
    ObjectType {
        /// Contract object type.
        expected: Arc<str>,
        /// Package object type.
        actual: Arc<str>,
    },
    /// The carried authority does not satisfy the edge's matching mode.
    #[error("carried authority does not match the edge")]
    Authority,
    /// The exact payload predicate rejected the committed bytes.
    #[error("contract {contract} rejected payload: {source}")]
    Contract {
        /// Admitted contract identity.
        contract: Arc<str>,
        /// Predicate's rejection detail.
        source: ContractViolation,
    },
}

fn invalid_edit(message: String) -> RewriteError {
    RewriteError::InvalidEdit(Arc::from(message))
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
            TransitionKind::Transfer {
                package, delivery, ..
            } => (*package, delivery),
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
    pub fn admit_fragment(&self, fragment: &GraphFragment) -> Result<Self, DefinitionError> {
        fragment.admit(self)
    }

    /// Checks an edit against the current graph and lifetime identities, and
    /// admits the definition it produces.
    fn structural_edit(
        &self,
        used_node_ids: &BTreeSet<Arc<str>>,
        used_edge_ids: &BTreeSet<Arc<str>>,
        edit: &GraphEdit,
    ) -> Result<StructuralResult, RewriteError> {
        let graph = self.graph();
        let removed_node = |id: &str| edit.remove_nodes.contains(id);
        let removed_edge = |id: &str| edit.remove_edges.contains(id);
        if let Some(node) = edit.remove_nodes.iter().find(|id| graph.node(id).is_none()) {
            return Err(invalid_edit(format!(
                "removed node {node} is not in the graph"
            )));
        }
        if let Some(edge) = edit.remove_edges.iter().find(|id| graph.edge(id).is_none()) {
            return Err(invalid_edit(format!(
                "removed edge {edge} is not in the graph"
            )));
        }
        if let Some(edge) = graph.edges().iter().find(|edge| {
            (removed_node(edge.source()) || removed_node(edge.target())) && !removed_edge(edge.id())
        }) {
            return Err(invalid_edit(format!(
                "edge {} touches a removed node but is not removed",
                edge.id()
            )));
        }

        let add = &edit.add;
        let fresh_node_ids: BTreeSet<_> = add.nodes.iter().map(Node::id_arc).collect();
        let fresh_edge_ids: BTreeSet<_> = add.edges.iter().map(Edge::id_arc).collect();
        if let Some(node) = fresh_node_ids.iter().find(|id| used_node_ids.contains(*id)) {
            return Err(invalid_edit(format!(
                "added node {node} reuses an identity of this workflow"
            )));
        }
        if let Some(edge) = fresh_edge_ids.iter().find(|id| used_edge_ids.contains(*id)) {
            return Err(invalid_edit(format!(
                "added edge {edge} reuses an identity of this workflow"
            )));
        }
        if let Some(node) = add
            .node_definitions
            .iter()
            .map(NodeDefinition::node_id)
            .chain(add.roots.iter().map(RootRule::node_id))
            .chain(
                add.authority_transitions
                    .iter()
                    .map(AuthorityTransitionRule::node_id),
            )
            .find(|id| !fresh_node_ids.contains(*id))
        {
            return Err(invalid_edit(format!(
                "node {node} is annotated but not added; surviving nodes keep their definitions"
            )));
        }
        if let Some(edge) = add
            .edge_definitions
            .iter()
            .map(EdgeDefinition::edge_id)
            .find(|id| !fresh_edge_ids.contains(*id))
        {
            return Err(invalid_edit(format!(
                "edge {edge} is annotated but not added; surviving edges keep their definitions"
            )));
        }

        let mut next = GraphFragment::from_kernel(self);
        next.nodes.retain(|node| !removed_node(node.id()));
        next.node_definitions
            .retain(|definition| !removed_node(definition.node_id()));
        next.roots.retain(|root| !removed_node(root.node_id()));
        next.authority_transitions
            .retain(|rule| !removed_node(rule.node_id()));
        next.edges.retain(|edge| !removed_edge(edge.id()));
        next.edge_definitions
            .retain(|definition| !removed_edge(definition.edge_id()));
        next.nodes.extend_from_slice(&add.nodes);
        next.edges.extend_from_slice(&add.edges);
        next.node_definitions
            .extend_from_slice(&add.node_definitions);
        next.edge_definitions
            .extend_from_slice(&add.edge_definitions);
        next.authority_transitions
            .extend_from_slice(&add.authority_transitions);
        next.roots.extend_from_slice(&add.roots);
        Ok(StructuralResult {
            next: next.admit(self)?,
            deleted_nodes: edit.remove_nodes.clone(),
            fresh_node_ids,
            fresh_edge_ids,
        })
    }

    fn accepts_package(
        &self,
        edge_id: &str,
        package_id: PackageId,
        record: &PackageRecord,
        bytes: impl FnOnce() -> Result<Payload, RewriteError>,
    ) -> Result<Result<(), TransferRejection>, RewriteError> {
        let (_, edge, _, contract) = self
            .admitted_edge(edge_id)
            .ok_or_else(|| invalid_state("acceptance edge is absent"))?;
        if record.object_type() != contract.object_type() {
            return Ok(Err(TransferRejection::ObjectType {
                expected: Arc::from(contract.object_type()),
                actual: Arc::from(record.object_type()),
            }));
        }
        if !edge.matches_authority(record.authority()) {
            return Ok(Err(TransferRejection::Authority));
        }
        let payload = bytes()?;
        if !record.content_digest().verifies(&payload) {
            return Err(RewriteError::EvidenceMismatch(package_id));
        }
        catch_unwind(AssertUnwindSafe(|| contract.validate(&payload)))
            .map(|result| {
                result.map_err(|source| TransferRejection::Contract {
                    contract: Arc::from(contract.id()),
                    source,
                })
            })
            .map_err(|_| RewriteError::ValidatorPanicked(Arc::from(contract.id())))
    }

    /// Evaluates a rewrite over a frontier view without mutating anything.
    ///
    /// The edit is checked structurally and its definition admitted; then the
    /// frontier cleanup is derived; last, `policy` decides whether the
    /// request's principal may make the edit, seeing the admitted result and
    /// the exact retirements.
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
    /// Returns structural, state, required-evidence, or policy errors.
    pub fn evaluate_rewrite(
        &self,
        frontier: &dyn FrontierView,
        policy: &dyn EditPolicy,
        request: &RewriteRequest,
        mut payload_for: impl FnMut(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<(Transition, Arc<Self>), RewriteError> {
        let binding = frontier.binding();
        let successor_revision = self.check_binding(&binding)?;
        let StructuralResult {
            next,
            deleted_nodes,
            fresh_node_ids,
            fresh_edge_ids,
        } = self.structural_edit(
            &frontier.used_node_ids(),
            &frontier.used_edge_ids(),
            request.edit(),
        )?;
        let changed_sources = changed_outgoing_sources(self.graph(), next.graph());
        let outgoing = outgoing_by_source(next.graph());
        let live = frontier.live();
        let retired = cleanup(
            live.iter().map(|(id, record)| (*id, record)),
            &deleted_nodes,
            |package_id, record| -> Result<bool, RewriteError> {
                let holder = record.holder();
                if !changed_sources.contains(holder) {
                    return Ok(true);
                }
                let mut payload: Option<Payload> = None;
                for edge in outgoing.get(holder).into_iter().flatten() {
                    if next
                        .accepts_package(edge, package_id, record, || {
                            if let Some(bytes) = &payload {
                                return Ok(Arc::clone(bytes));
                            }
                            let bytes = payload_for(package_id, record.content_digest())?;
                            payload = Some(Arc::clone(&bytes));
                            Ok(bytes)
                        })?
                        .is_ok()
                    {
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
        let context = EditContext {
            principal: request.principal(),
            before: self,
            edit: request.edit(),
            after: &next,
            retirements: &retired,
        };
        catch_unwind(AssertUnwindSafe(|| policy.permits(&context)))
            .map_err(|_| RewriteError::PolicyPanicked)?
            .map_err(|denial| RewriteError::Denied(Arc::from(denial.reason())))?;
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
                next_all_routes: next
                    .node_definitions()
                    .iter()
                    .filter(|node| node.ingress_mode() == IngressMode::All)
                    .map(|node| {
                        (
                            Arc::from(node.node_id()),
                            next.incoming_edge_ids(node.node_id()).clone(),
                        )
                    })
                    .collect(),
                next_fingerprint: *next.fingerprint(),
            },
        };
        Ok((transition, Arc::new(next)))
    }

    /// Admits a graph edit under `policy` and derives its exact frontier cleanup.
    ///
    /// # Errors
    /// Rejects an invalid or refused edit, invalid state, or missing/invalid evidence.
    pub fn prepare_rewrite(
        &self,
        state: &State,
        policy: &dyn EditPolicy,
        request: &RewriteRequest,
        evidence: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<PreparedRewrite, RewriteError> {
        self.prepare_rewrite_with_evidence(state, policy, request, |package_id, digest| {
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
    /// Returns structural, state, required-evidence, or policy errors without mutation.
    pub fn prepare_rewrite_with_evidence(
        &self,
        state: &State,
        policy: &dyn EditPolicy,
        request: &RewriteRequest,
        payload_for: impl FnMut(PackageId, ContentDigest) -> Result<Payload, RewriteError>,
    ) -> Result<PreparedRewrite, RewriteError> {
        let (transition, next_kernel) =
            self.evaluate_rewrite(state, policy, request, payload_for)?;
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
        if state.binding() != *prepared.transition.base() {
            return Err(RewriteError::Stale);
        }
        self.check_binding(&state.binding())?;
        for contract in self.contracts() {
            if !prepared
                .next_kernel
                .contract(contract.id())
                .is_some_and(|next| {
                    next.object_type() == contract.object_type()
                        && next.shares_validator_with(contract)
                })
            {
                return Err(RewriteError::ContractChanged(Arc::from(contract.id())));
            }
        }
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
        if let Err(reason) = self.accepts_package(edge_id, package_id, &record, || {
            payload_for(package_id, record.content_digest())
        })? {
            return Err(TransferError::Rejected {
                package: package_id,
                reason,
            });
        }
        Ok(Transition {
            base: binding,
            kind: TransitionKind::Transfer {
                package: package_id,
                source: record,
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
        if state.binding() != *prepared.transition.base() {
            return Err(RewriteError::Stale.into());
        }
        self.check_binding(&state.binding())?;
        state
            .apply(self, &prepared.transition)
            .map_err(RewriteError::from)?;
        Ok(prepared.delivery().clone())
    }
}
