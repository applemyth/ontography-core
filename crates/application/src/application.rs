//! Application-level composition of kernel graph objects and executable components.
//!
//! An application binds reusable behavior to static kernel configuration, admits
//! that configuration through [`ontography_calculus::Kernel`], and launches the retained
//! executables through the proposal runtime and host. It adds no graph law.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::future::Future;
use std::io;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use bytes::Bytes;
use thiserror::Error;

use ontography_calculus::{
    Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, ContentDigest, Contract,
    DefinitionError, DefinitionId, Edge, EdgeDefinition, Graph, IngressMode, Kernel, Node,
    NodeDefinition, PackageId, Payload, RootRule, Schema,
};
use ontography_content::{ContentError, ContentId, ContentMetadata, ContentReader, ContentStore};
use ontography_runtime::{
    ActivityReporter, ExecutableDefinition, ExecutionContext, ExecutionFailure, ExecutionFuture,
    ExecutionHandle, ExecutionHost, ExecutionSignal, ExecutionStop, LaunchError, PendingFrontier,
    ProposalDecision, ProposalRuntime, SessionError, SessionHandle, SessionOpenError,
    SessionSnapshot, SessionStatus, SubmitError,
};

type Text = Arc<str>;

const APPLICATION_STOP_GRACE: Duration = Duration::from_secs(1);

trait ComponentExecutable: Send + Sync + 'static {
    fn launch(&self, context: ApplicationContext) -> ExecutionFuture;
}

struct ClosureExecutable<F>(F);

impl<F, Fut> ComponentExecutable for ClosureExecutable<F>
where
    F: Fn(ApplicationContext) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Result<(), ExecutionFailure>> + Send + 'static,
{
    fn launch(&self, context: ApplicationContext) -> ExecutionFuture {
        Box::pin((self.0)(context))
    }
}

#[derive(Clone)]
pub(crate) struct NodeExecutable(Arc<dyn ComponentExecutable>);

impl NodeExecutable {
    pub(crate) fn new<F, Fut>(executable: F) -> Self
    where
        F: Fn(ApplicationContext) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<(), ExecutionFailure>> + Send + 'static,
    {
        Self(Arc::new(ClosureExecutable(executable)))
    }
}

/// Reusable static kernel configuration for a placed application node.
#[derive(Clone)]
pub struct NodeConfig {
    types: BTreeSet<Text>,
    result_contract: Contract,
    ingress_mode: IngressMode,
    context_policy: ontography_runtime::ContextPolicy,
}

impl fmt::Debug for NodeConfig {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NodeConfig")
            .field("types", &self.types)
            .field("result_contract", &self.result_contract.id())
            .field("ingress_mode", &self.ingress_mode)
            .field("context_policy", &self.context_policy)
            .finish()
    }
}

impl NodeConfig {
    /// Declares the node's semantic types and exact activation-result contract.
    ///
    /// [`ApplicationBuilder`] supplies the placed node identity and the kernel
    /// validates the completed [`NodeDefinition`].
    ///
    /// # Errors
    ///
    /// Returns an error when no semantic type is supplied or a type is empty.
    pub fn new<I, S>(types: I, result_contract: Contract) -> Result<Self, ApplicationError>
    where
        I: IntoIterator<Item = S>,
        S: Into<Text>,
    {
        Ok(Self {
            types: config_identifiers(types, "node type", true)?,
            result_contract,
            ingress_mode: IngressMode::Any,
            context_policy: ontography_runtime::ContextPolicy::default(),
        })
    }

    /// Selects the package-ingress rule for this node.
    #[must_use]
    pub const fn with_ingress_mode(mut self, ingress_mode: IngressMode) -> Self {
        self.ingress_mode = ingress_mode;
        self
    }

    /// Defines the context and optional exploration granted to each invocation.
    #[must_use]
    pub fn with_context_policy(mut self, policy: ontography_runtime::ContextPolicy) -> Self {
        self.context_policy = policy;
        self
    }

    /// Returns every declared semantic node type.
    #[must_use]
    pub const fn types(&self) -> &BTreeSet<Text> {
        &self.types
    }

    /// Returns the exact contract accepted as an activation result.
    #[must_use]
    pub const fn result_contract(&self) -> &Contract {
        &self.result_contract
    }

    /// Returns the package-ingress rule.
    #[must_use]
    pub const fn ingress_mode(&self) -> IngressMode {
        self.ingress_mode
    }
}

/// Reusable static kernel configuration for a placed application edge.
#[derive(Clone)]
pub struct EdgeConfig {
    types: BTreeSet<Text>,
    source_requirements: BTreeSet<Text>,
    target_requirements: BTreeSet<Text>,
    package_contract: Contract,
    authority_tags: BTreeSet<AuthorityTag>,
    authority_match: AuthorityMatch,
}

impl fmt::Debug for EdgeConfig {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EdgeConfig")
            .field("types", &self.types)
            .field("source_requirements", &self.source_requirements)
            .field("target_requirements", &self.target_requirements)
            .field("package_contract", &self.package_contract.id())
            .field("authority_tags", &self.authority_tags)
            .field("authority_match", &self.authority_match)
            .finish()
    }
}

impl EdgeConfig {
    /// Declares an edge's types, endpoint requirements, package contract, and
    /// authority tags.
    ///
    /// [`ApplicationBuilder`] supplies the concrete identity and endpoints and
    /// the kernel validates the completed [`EdgeDefinition`].
    ///
    /// # Errors
    ///
    /// Returns an error when no edge type or authority tag is supplied, or a
    /// semantic type is empty.
    pub fn new<ET, ETS, SR, SRS, TR, TRS, AT>(
        types: ET,
        source_requirements: SR,
        target_requirements: TR,
        package_contract: Contract,
        authority_tags: AT,
    ) -> Result<Self, ApplicationError>
    where
        ET: IntoIterator<Item = ETS>,
        ETS: Into<Text>,
        SR: IntoIterator<Item = SRS>,
        SRS: Into<Text>,
        TR: IntoIterator<Item = TRS>,
        TRS: Into<Text>,
        AT: IntoIterator<Item = AuthorityTag>,
    {
        let authority_tags = authority_tags.into_iter().collect::<BTreeSet<_>>();
        if authority_tags.is_empty() {
            return Err(ApplicationError::MissingAuthorityTags);
        }
        Ok(Self {
            types: config_identifiers(types, "edge type", true)?,
            source_requirements: config_identifiers(
                source_requirements,
                "edge source requirement",
                false,
            )?,
            target_requirements: config_identifiers(
                target_requirements,
                "edge target requirement",
                false,
            )?,
            package_contract,
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

    /// Returns every declared semantic edge type.
    #[must_use]
    pub const fn types(&self) -> &BTreeSet<Text> {
        &self.types
    }

    /// Returns the semantic types required at the source node.
    #[must_use]
    pub const fn source_requirements(&self) -> &BTreeSet<Text> {
        &self.source_requirements
    }

    /// Returns the semantic types required at the target node.
    #[must_use]
    pub const fn target_requirements(&self) -> &BTreeSet<Text> {
        &self.target_requirements
    }

    /// Returns the exact package contract.
    #[must_use]
    pub const fn package_contract(&self) -> &Contract {
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
}

fn config_identifiers<I, S>(
    values: I,
    kind: &'static str,
    require_one: bool,
) -> Result<BTreeSet<Text>, ApplicationError>
where
    I: IntoIterator<Item = S>,
    S: Into<Text>,
{
    let values = values
        .into_iter()
        .map(Into::into)
        .map(|value: Text| {
            if value.trim().is_empty() {
                Err(ApplicationError::InvalidName { kind, value })
            } else {
                Ok(value)
            }
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    if require_one && values.is_empty() {
        return Err(ApplicationError::MissingSemanticTypes(kind));
    }
    Ok(values)
}

/// Reusable node semantics together with the behavior launched for each placed
/// instance.
#[derive(Clone)]
pub struct NodeComponent {
    config: NodeConfig,
    executable: Arc<dyn ComponentExecutable>,
    root_authority: Option<Authority>,
    authority_transitions: BTreeSet<(Authority, Authority)>,
}

impl fmt::Debug for NodeComponent {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NodeComponent")
            .field("config", &self.config)
            .field("root_authority", &self.root_authority)
            .field("authority_transitions", &self.authority_transitions)
            .finish_non_exhaustive()
    }
}

impl NodeComponent {
    /// Couples reusable kernel node configuration to its launch behavior.
    #[must_use]
    pub fn new<F, Fut>(config: NodeConfig, executable: F) -> Self
    where
        F: Fn(ApplicationContext) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<(), ExecutionFailure>> + Send + 'static,
    {
        Self::from_executable(config, NodeExecutable::new(executable))
    }

    pub(crate) fn from_executable(config: NodeConfig, executable: NodeExecutable) -> Self {
        Self {
            config,
            executable: executable.0,
            root_authority: None,
            authority_transitions: BTreeSet::new(),
        }
    }

    /// Makes this component rootable with exactly the supplied authority
    /// ceiling when it is placed as an application entry; any other placement
    /// leaves the node unrootable.
    #[must_use]
    pub fn with_root_authority(mut self, ceiling: Authority) -> Self {
        self.root_authority = Some(ceiling);
        self
    }

    /// Adds one exact authority transition owned by this component.
    #[must_use]
    pub fn with_authority_transition(mut self, from: Authority, to: Authority) -> Self {
        self.authority_transitions.insert((from, to));
        self
    }

    /// Returns the reusable kernel configuration carried by this component.
    #[must_use]
    pub const fn config(&self) -> &NodeConfig {
        &self.config
    }

    /// Returns the root ceiling installed when this component is the entry.
    #[must_use]
    pub const fn root_authority(&self) -> Option<&Authority> {
        self.root_authority.as_ref()
    }

    /// Returns the exact authority transitions installed at each placement.
    #[must_use]
    pub fn authority_transitions(&self) -> impl ExactSizeIterator<Item = (&Authority, &Authority)> {
        self.authority_transitions
            .iter()
            .map(|(from, to)| (from, to))
    }
}

/// Whether components are launching for a newly created or resumed run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ApplicationRunMode {
    /// A newly created run whose entry receives the initial input.
    Fresh,
    /// An existing run relaunched without a new entry input, with every
    /// current graph node bound to an executable.
    Resume,
    /// An existing run relaunched through [`Application::resume_partial`]:
    /// bindings whose nodes a rewrite removed are skipped, and nodes a rewrite
    /// added run without an executable.
    PartialResume,
}

/// Read and import access to the run's content store for one placed node.
///
/// Components import bytes and read verified content. Store lifecycle
/// operations such as garbage collection stay with the launcher, which holds
/// the full [`ContentStore`] through [`RunningApplication::session`].
#[derive(Clone, Debug)]
pub struct ContentAccess(ContentStore);

impl ContentAccess {
    /// Imports owned bytes, retaining the result across restarts.
    ///
    /// # Errors
    /// Reports storage failures.
    pub async fn import_bytes(&self, bytes: impl Into<Bytes>) -> Result<ContentId, ContentError> {
        self.0.import_bytes(bytes).await
    }

    /// Reads a verified byte range of one complete content item.
    ///
    /// # Errors
    /// Reports invalid bounds, unavailable content, or verification failure.
    pub async fn read_range(
        &self,
        id: ContentId,
        range: Range<u64>,
    ) -> Result<Bytes, ContentError> {
        self.0.read_range(id, range).await
    }

    /// Resolves a SHA-256 commitment and returns a verified byte range.
    ///
    /// # Errors
    /// Reports invalid bounds, unavailable content, or verification failure.
    pub async fn read_digest_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Bytes>, ContentError> {
        self.0.read_digest_range(digest, range).await
    }

    /// Returns a committed payload's size without reading it.
    ///
    /// # Errors
    /// Reports storage failures or inconsistent metadata.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>, ContentError> {
        self.0.content_size(digest).await
    }

    /// Resolves a SHA-256 commitment and opens a verified seekable reader.
    ///
    /// # Errors
    /// Reports unavailable content or verification failure.
    pub async fn digest_reader(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<ContentReader>, ContentError> {
        self.0.digest_reader(digest).await
    }

    /// Inspects availability and checks the identity against the stored size.
    ///
    /// # Errors
    /// Reports storage failures or an inconsistent identity.
    pub async fn metadata(&self, id: ContentId) -> Result<ContentMetadata, ContentError> {
        self.0.metadata(id).await
    }
}

/// Facilities supplied to one launched application node.
///
/// On a fresh run the entry node receives the application input and its
/// compiled root authority. On resume no component receives either. Every node
/// can inspect its concrete outgoing edges or resolve them by authority tag.
pub struct ApplicationContext {
    execution: ExecutionContext,
    run_mode: ApplicationRunMode,
    node_state_dir: Option<PathBuf>,
    initial_input: Option<Payload>,
    root_authority: Option<Authority>,
    context_policy: ontography_runtime::ContextPolicy,
}

impl fmt::Debug for ApplicationContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ApplicationContext")
            .field("execution", &self.execution)
            .field("run_mode", &self.run_mode)
            .field("node_state_dir", &self.node_state_dir)
            .field("has_initial_input", &self.initial_input.is_some())
            .field("root_authority", &self.root_authority)
            .field("context_policy", &self.context_policy)
            .finish()
    }
}

impl ApplicationContext {
    /// Returns the rule enforced for invocations of this placed node.
    #[must_use]
    pub const fn context_policy(&self) -> &ontography_runtime::ContextPolicy {
        &self.context_policy
    }

    /// Starts a durable, scoped invocation bound to this node and its trigger.
    ///
    /// # Errors
    /// Rejects invalid triggers, unavailable context, or revoked execution custody.
    pub async fn begin_invocation(
        &self,
        trigger: ontography_runtime::InvocationTrigger,
    ) -> Result<ontography_runtime::InvocationHandle, ontography_runtime::ContextError> {
        self.execution
            .begin_invocation(trigger, self.context_policy.clone())
            .await
    }

    /// Starts a trusted root invocation with explicitly retained content dependencies.
    ///
    /// # Errors
    /// Rejects unavailable content, invalid scope, or revoked execution custody.
    pub async fn begin_invocation_with_content(
        &self,
        trigger: ontography_runtime::InvocationTrigger,
        contents: Vec<ContentId>,
    ) -> Result<ontography_runtime::InvocationHandle, ontography_runtime::ContextError> {
        self.execution
            .begin_invocation_with_content(trigger, self.context_policy.clone(), contents)
            .await
    }
    /// Enables optional activity reporting for this placed executable instance.
    ///
    /// Reports are ephemeral telemetry, not package reservations or admitted
    /// activations. Graph and activity observations are not atomic together.
    #[must_use]
    pub fn activity_reporter(&self) -> ActivityReporter {
        self.execution.activity_reporter()
    }

    /// Reports whether this component is launching for a new or resumed run.
    #[must_use]
    pub const fn run_mode(&self) -> ApplicationRunMode {
        self.run_mode
    }

    /// Returns the graph-local node identity for this placed component.
    #[must_use]
    pub fn node_id(&self) -> &str {
        self.execution.node_id()
    }

    /// Returns the run-owned persistent state directory for this placed node.
    ///
    /// Persistent application runs allocate one isolated directory below the
    /// run's `nodes` directory for every placed node. Resuming a run supplies
    /// the same directory. Ephemeral runs return `None`.
    #[must_use]
    pub fn node_state_dir(&self) -> Option<&Path> {
        self.node_state_dir.as_deref()
    }

    /// Returns the initial application input for the entry component.
    #[must_use]
    pub const fn initial_input(&self) -> Option<&Payload> {
        self.initial_input.as_ref()
    }

    /// Returns the compiled root authority for the entry component.
    #[must_use]
    pub const fn root_authority(&self) -> Option<&Authority> {
        self.root_authority.as_ref()
    }

    /// Returns current outgoing edge identities declaring `authority_tag`.
    ///
    /// # Errors
    /// Returns an error if the node was removed or session state cannot be read.
    pub async fn outgoing(&self, authority_tag: &str) -> Result<Vec<Text>, SessionError> {
        let kernel = self.kernel().await?;
        if kernel.graph().node(self.node_id()).is_none() {
            return Err(SessionError::UnknownNode(Arc::from(self.node_id())));
        }
        Ok(kernel
            .graph()
            .edges()
            .iter()
            .filter(|edge| {
                edge.source() == self.node_id()
                    && kernel.edge_definition(edge.id()).is_some_and(|definition| {
                        definition
                            .authority_tags()
                            .iter()
                            .any(|tag| tag.id() == authority_tag)
                    })
            })
            .map(Edge::id_arc)
            .collect())
    }

    /// Returns the current concrete outgoing edges from this placed node.
    ///
    /// # Errors
    /// Returns an error if the node was removed or session state cannot be read.
    pub async fn outgoing_edges(&self) -> Result<Vec<Edge>, SessionError> {
        let kernel = self.kernel().await?;
        if kernel.graph().node(self.node_id()).is_none() {
            return Err(SessionError::UnknownNode(Arc::from(self.node_id())));
        }
        Ok(kernel
            .graph()
            .edges()
            .iter()
            .filter(|edge| edge.source() == self.node_id())
            .cloned()
            .collect())
    }

    /// Returns a snapshot of the kernel currently governing this run.
    ///
    /// # Errors
    /// Returns an error when session state cannot be read.
    pub async fn kernel(&self) -> Result<Arc<Kernel>, SessionError> {
        self.execution.kernel().await
    }

    /// Returns currently pending packages at this component's graph position.
    ///
    /// # Errors
    ///
    /// Returns an error if the placed node is absent from the current kernel
    /// or persistent state cannot be read.
    pub async fn pending(&self) -> Result<PendingFrontier, SessionError> {
        self.execution.pending().await
    }

    /// Returns one bounded page of pending packages at this component.
    ///
    /// If the state revision changes between pages, restart pagination to
    /// obtain a coherent traversal.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero limit or unreadable persistent state.
    pub async fn pending_page(
        &self,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingFrontier, SessionError> {
        self.execution.pending_page(after, limit).await
    }

    /// Returns the next complete package trigger at this component.
    ///
    /// The projection is bounded by the node's ingress mode and in-degree. It is
    /// not a reservation; the kernel revalidates package custody on submission.
    ///
    /// # Errors
    ///
    /// Returns an error if the compiled position is absent or persistent state
    /// cannot be read.
    pub async fn next_trigger(&self) -> Result<PendingFrontier, SessionError> {
        self.execution.next_trigger().await
    }

    /// Returns the least pending package on one incoming edge at this component.
    ///
    /// The projection contains zero or one package and is not a reservation.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or non-incoming edge, or unreadable
    /// persistent state.
    pub async fn next_pending_on_edge(
        &self,
        edge_id: impl Into<Arc<str>>,
    ) -> Result<PendingFrontier, SessionError> {
        self.execution.next_pending_on_edge(edge_id).await
    }

    /// Resolves exact bytes in the proposal session's object pool by digest.
    ///
    /// # Errors
    ///
    /// Returns an error when durable content is unreadable or fails its digest.
    pub async fn content(&self, digest: ContentDigest) -> Result<Option<Payload>, SessionError> {
        self.execution.content(digest).await
    }

    /// Returns read and import access to this run's content store.
    /// # Errors
    /// Reports unreadable session state.
    pub async fn content_store(&self) -> Result<ContentAccess, SessionError> {
        self.execution.content_store().await.map(ContentAccess)
    }

    /// Returns payload size without allocating the complete content.
    /// # Errors
    /// Reports unreadable storage or inconsistent metadata.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>, SessionError> {
        self.execution.content_size(digest).await
    }

    /// Reads an exact verified byte range without holding the session lock.
    /// # Errors
    /// Reports invalid offsets, storage failures, or corrupt content.
    pub async fn content_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Payload>, SessionError> {
        self.execution.content_range(digest, range).await
    }

    /// Opens a verified, seekable reader for one complete content commitment.
    /// # Errors
    /// Reports unreadable storage or corrupt content.
    pub async fn content_reader(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<ContentReader>, SessionError> {
        self.execution.content_reader(digest).await
    }

    /// Returns artifact dependencies retained with the specified activation.
    /// # Errors
    /// Reports unreadable or inconsistent retained state.
    pub async fn activation_content(
        &self,
        activation_id: ontography_calculus::ActivationId,
    ) -> Result<Vec<ContentId>, SessionError> {
        self.execution.activation_content(activation_id).await
    }

    /// Reads accepted package metadata and its producer's inputs without payloads.
    /// # Errors
    /// Reports unreadable or inconsistent session state.
    pub async fn package_history(
        &self,
        id: PackageId,
    ) -> Result<Option<ontography_runtime::PackageHistory>, SessionError> {
        self.execution.package_history(id).await
    }

    /// Submits one proposal through the execution host's custody boundary.
    ///
    /// # Errors
    ///
    /// Returns an operational error when proposal admission has ended or this
    /// executable no longer owns submission custody.
    pub async fn submit(
        &self,
        proposal: ontography_calculus::ActivationProposal,
    ) -> Result<ProposalDecision, SubmitError> {
        self.execution.submit(proposal).await
    }

    /// Submits a proposal and retains its explicit artifact dependencies.
    ///
    /// Submission uses this executable's custody boundary. Dependencies must be
    /// complete in the session's content store before admission.
    /// # Errors
    /// Reports closed or faulted admission, unavailable content, or revoked custody.
    pub async fn submit_with_content(
        &self,
        proposal: ontography_calculus::ActivationProposal,
        contents: Vec<ContentId>,
    ) -> Result<ProposalDecision, SubmitError> {
        self.execution.submit_with_content(proposal, contents).await
    }

    /// Returns a cooperative stop handle for this executable.
    #[must_use]
    pub fn stop(&self) -> ExecutionStop {
        self.execution.stop()
    }

    /// Waits for a relevant frontier, stop, or session-lifecycle change.
    pub async fn next_signal(&mut self) -> ExecutionSignal {
        self.execution.next_signal().await
    }
}

/// Failure while declaring or compiling an application.
#[derive(Debug, Error)]
pub enum ApplicationError {
    /// An application configuration identifier is empty.
    #[error("invalid {kind} {value:?}")]
    InvalidName {
        /// Kind of identifier being validated.
        kind: &'static str,
        /// Rejected identifier.
        value: Text,
    },
    /// A node or edge configuration has no semantic types.
    #[error("{0} requires at least one semantic type")]
    MissingSemanticTypes(&'static str),
    /// An edge configuration has no authority tags.
    #[error("edge configuration requires at least one authority tag")]
    MissingAuthorityTags,
    /// The application definition identity is invalid.
    #[error(transparent)]
    Definition(#[from] DefinitionError),
    /// One contract ID was reused for different object types.
    #[error(
        "contract {contract_id} has conflicting object types {first_object_type} and {second_object_type}"
    )]
    ContractConflict {
        /// Reused contract identity.
        contract_id: Text,
        /// First object type.
        first_object_type: Text,
        /// Conflicting object type.
        second_object_type: Text,
    },
    /// One contract ID was backed by different validator identities.
    #[error("contract {0} has conflicting validator implementations")]
    ContractSemanticConflict(Text),
    /// No entry component was declared.
    #[error("application requires one entry node")]
    MissingEntry,
    /// The entry component declared no root-authority policy.
    #[error("application entry component requires a root-authority policy, which may be empty")]
    MissingRootAuthority,
    /// More than one entry component was declared.
    #[error("application already has entry node {0}")]
    DuplicateEntry(Text),
}

/// Failure while opening and launching an application run.
#[derive(Debug, Error)]
pub enum ApplicationStartError {
    /// The process working directory could not be resolved for local state.
    #[error("could not resolve the application working directory: {0}")]
    WorkingDirectory(#[source] io::Error),
    /// A local run directory could not be created.
    #[error("could not prepare application state at {}: {source}", path.display())]
    StateDirectory {
        /// Directory that could not be prepared.
        path: PathBuf,
        /// Underlying filesystem failure.
        #[source]
        source: io::Error,
    },
    /// The proposal runtime could not open a fresh session.
    #[error(transparent)]
    Session(#[from] SessionOpenError),
    /// The opened session's state could not be read while launching.
    #[error("could not read the application session while launching: {0}")]
    SessionRead(#[from] SessionError),
    /// Only an open persistent run can be resumed.
    #[error("application run is {0:?} and cannot be resumed")]
    NotResumable(SessionStatus),
    /// Retained bindings no longer match the run's rewritten graph.
    #[error(
        "application bindings drift from the run graph: removed nodes {removed:?}, unbound nodes {unbound:?}"
    )]
    BindingDrift {
        /// Bound nodes a rewrite removed from the graph.
        removed: Vec<Text>,
        /// Current graph nodes with no retained binding.
        unbound: Vec<Text>,
    },
    /// One retained component could not be launched at its compiled node.
    #[error("failed to launch application node {node_id}: {source}")]
    Launch {
        /// Graph-local node identity whose launch failed.
        node_id: Text,
        /// Existing execution-host launch failure.
        #[source]
        source: LaunchError,
    },
}

#[derive(Clone)]
struct PlacedNode {
    node: Node,
    definition: NodeDefinition,
    component: NodeComponent,
}

#[derive(Clone)]
struct PlacedEdge {
    edge: Edge,
    definition: EdgeDefinition,
}

/// Mutable application declaration over reusable nodes and edges.
pub struct ApplicationBuilder {
    definition_id: DefinitionId,
    nodes: BTreeMap<Text, PlacedNode>,
    edges: BTreeMap<Text, PlacedEdge>,
    contracts: BTreeMap<Text, Contract>,
    root: Option<RootRule>,
}

impl fmt::Debug for ApplicationBuilder {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ApplicationBuilder")
            .field("definition_id", &self.definition_id)
            .field("nodes", &self.nodes.len())
            .field("edges", &self.edges.len())
            .field("entry", &self.root.as_ref().map(RootRule::node_id))
            .finish_non_exhaustive()
    }
}

impl ApplicationBuilder {
    /// Creates an empty application declaration.
    ///
    /// # Errors
    ///
    /// Returns an error when the immutable definition identity is invalid.
    pub fn new(id: impl Into<Text>) -> Result<Self, ApplicationError> {
        Ok(Self {
            definition_id: DefinitionId::new(id)?,
            nodes: BTreeMap::new(),
            edges: BTreeMap::new(),
            contracts: BTreeMap::new(),
            root: None,
        })
    }

    /// Places the application's single entry component.
    ///
    /// # Errors
    ///
    /// Returns an error for a second entry, a component with no root policy, or
    /// invalid node configuration.
    pub fn entry(
        &mut self,
        name: impl Into<Text>,
        component: NodeComponent,
    ) -> Result<Text, ApplicationError> {
        if let Some(root) = &self.root {
            return Err(ApplicationError::DuplicateEntry(Arc::from(root.node_id())));
        }
        let name = name.into();
        let ceiling = component
            .root_authority
            .clone()
            .ok_or(ApplicationError::MissingRootAuthority)?;
        let root = RootRule::new(Arc::clone(&name), ceiling)?;
        let node_id = self.node(name, component)?;
        self.root = Some(root);
        Ok(node_id)
    }

    /// Places one reusable node component under a graph-local identity.
    ///
    /// Only [`Self::entry`] installs a root rule; a rootable component placed
    /// here is unrootable at this node.
    ///
    /// # Errors
    ///
    /// Returns a definition error for an invalid or duplicate identity or an
    /// inconsistent contract binding.
    pub fn node(
        &mut self,
        name: impl Into<Text>,
        component: NodeComponent,
    ) -> Result<Text, ApplicationError> {
        let name = name.into();
        if self.nodes.contains_key(&name) {
            return Err(DefinitionError::DuplicateNode(name).into());
        }
        let node = Node::new(Arc::clone(&name))?;
        let definition = NodeDefinition::new(
            Arc::clone(&name),
            component.config.types().iter().cloned(),
            component.config.result_contract().id(),
        )?
        .with_ingress_mode(component.config.ingress_mode());
        register_contract(&mut self.contracts, component.config.result_contract())?;
        self.nodes.insert(
            Arc::clone(&name),
            PlacedNode {
                node,
                definition,
                component,
            },
        );
        Ok(name)
    }

    /// Places one reusable edge configuration between two declared nodes.
    ///
    /// # Errors
    ///
    /// Returns a definition error for invalid identities, endpoints, or edge
    /// configuration, or an inconsistent contract binding.
    pub fn connect(
        &mut self,
        name: impl Into<Text>,
        source: &str,
        config: EdgeConfig,
        target: &str,
    ) -> Result<Text, ApplicationError> {
        if !self.nodes.contains_key(source) {
            return Err(DefinitionError::UnknownEndpoint(Arc::from(source)).into());
        }
        if !self.nodes.contains_key(target) {
            return Err(DefinitionError::UnknownEndpoint(Arc::from(target)).into());
        }
        let name = name.into();
        if self.edges.contains_key(&name) {
            return Err(DefinitionError::DuplicateEdge(name).into());
        }
        let edge = Edge::new(Arc::clone(&name), source, target)?;
        let definition = EdgeDefinition::new(
            Arc::clone(&name),
            config.types().iter().cloned(),
            config.source_requirements().iter().cloned(),
            config.target_requirements().iter().cloned(),
            config.package_contract().id(),
            config.authority_tags().iter().cloned(),
        )?
        .with_authority_match(config.authority_match());
        register_contract(&mut self.contracts, config.package_contract())?;
        self.edges
            .insert(Arc::clone(&name), PlacedEdge { edge, definition });
        Ok(name)
    }

    /// Compiles the semantic graph and retained executable bindings.
    ///
    /// Root and transition policy comes only from the placed node components;
    /// application topology does not imply authority.
    ///
    /// # Errors
    ///
    /// Returns an error when no entry exists or native graph admission rejects
    /// the declaration.
    pub fn build(self) -> Result<Application, ApplicationError> {
        let root = self.root.ok_or(ApplicationError::MissingEntry)?;

        let mut node_types = BTreeSet::new();
        let mut nodes = Vec::with_capacity(self.nodes.len());
        let mut node_definitions = Vec::with_capacity(self.nodes.len());
        let mut transitions = Vec::new();
        let mut bindings = Vec::with_capacity(self.nodes.len());
        for (node_id, placed) in self.nodes {
            node_types.extend(placed.definition.types().iter().cloned());
            for (from, to) in placed.component.authority_transitions {
                transitions.push(AuthorityTransitionRule::new(
                    Arc::clone(&node_id),
                    from,
                    to,
                )?);
            }
            nodes.push(placed.node);
            node_definitions.push(placed.definition);
            bindings.push(LaunchBinding {
                node_id,
                executable: placed.component.executable,
                context_policy: placed.component.config.context_policy,
            });
        }

        let mut authority_tags = BTreeSet::new();
        let mut edges = Vec::with_capacity(self.edges.len());
        let mut edge_definitions = Vec::with_capacity(self.edges.len());
        for placed in self.edges.into_values() {
            authority_tags.extend(placed.definition.authority_tags().iter().cloned());
            edges.push(placed.edge);
            edge_definitions.push(placed.definition);
        }
        let object_types = self
            .contracts
            .values()
            .map(|contract| Arc::from(contract.object_type()))
            .collect::<BTreeSet<_>>();
        let schema = Schema::new(node_types, object_types, authority_tags)?;
        let kernel = Kernel::admit(
            self.definition_id,
            schema,
            Graph::new(nodes, edges)?,
            self.contracts.into_values(),
            node_definitions,
            edge_definitions,
            transitions,
            [root.clone()],
        )?;
        Ok(Application {
            kernel: Arc::new(kernel),
            grammar: ontography_calculus::RewriteGrammar::default(),
            root,
            bindings,
        })
    }
}

fn register_contract(
    contracts: &mut BTreeMap<Text, Contract>,
    contract: &Contract,
) -> Result<(), ApplicationError> {
    if let Some(existing) = contracts.get(contract.id()) {
        if existing.object_type() != contract.object_type() {
            return Err(ApplicationError::ContractConflict {
                contract_id: Arc::from(contract.id()),
                first_object_type: Arc::from(existing.object_type()),
                second_object_type: Arc::from(contract.object_type()),
            });
        }
        if !existing.shares_validator_with(contract) {
            return Err(ApplicationError::ContractSemanticConflict(Arc::from(
                contract.id(),
            )));
        }
        return Ok(());
    }
    contracts.insert(Arc::from(contract.id()), contract.clone());
    Ok(())
}

struct LaunchBinding {
    node_id: Text,
    executable: Arc<dyn ComponentExecutable>,
    context_policy: ontography_runtime::ContextPolicy,
}

struct BoundExecutable {
    executable: Arc<dyn ComponentExecutable>,
    run_mode: ApplicationRunMode,
    node_state_dir: Option<PathBuf>,
    initial_input: Option<Payload>,
    root_authority: Option<Authority>,
    context_policy: ontography_runtime::ContextPolicy,
}

impl ExecutableDefinition for BoundExecutable {
    fn launch(&self, execution: ExecutionContext) -> ExecutionFuture {
        self.executable.launch(ApplicationContext {
            execution,
            run_mode: self.run_mode,
            node_state_dir: self.node_state_dir.clone(),
            initial_input: self.initial_input.clone(),
            root_authority: self.root_authority.clone(),
            context_policy: self.context_policy.clone(),
        })
    }
}

/// Immutable compiled application plus its retained node launch behavior.
pub struct Application {
    kernel: Arc<Kernel>,
    grammar: ontography_calculus::RewriteGrammar,
    root: RootRule,
    bindings: Vec<LaunchBinding>,
}

impl fmt::Debug for Application {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Application")
            .field("definition_id", &self.kernel.id())
            .field("grammar", &self.grammar)
            .field("entry", &self.root.node_id())
            .field("bindings", &self.bindings.len())
            .finish()
    }
}

impl Application {
    /// Configures the graph productions permitted in this application's sessions.
    #[must_use]
    pub fn with_grammar(mut self, grammar: ontography_calculus::RewriteGrammar) -> Self {
        self.grammar = grammar;
        self
    }

    /// Reconstructs this application's binding with an extended vocabulary.
    ///
    /// Existing contracts must share their validators with this application;
    /// graph structure, annotations, authority rules, and root rules must stay
    /// identical. Retained executables and the configured grammar are preserved.
    /// This changes construction/resumption configuration, not any live session.
    /// Use [`SessionHandle::extend`] to extend a running session, persist the
    /// additions in the caller, and reconstruct this binding before resuming it.
    ///
    /// # Errors
    ///
    /// Returns an extension rejection if `next` is not a strict vocabulary
    /// extension of this application's admitted starting definition.
    pub fn with_vocabulary_extension(
        mut self,
        next: Arc<Kernel>,
    ) -> Result<Self, ontography_calculus::ExtensionError> {
        self.kernel.evaluate_extension(&next)?;
        self.kernel = next;
        Ok(self)
    }

    /// Returns the admitted starting graph for new application runs.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Creates a new persistent run under `.ontography/runs` in the process
    /// working directory and launches every declared node.
    ///
    /// Non-entry components launch before the entry component so consumers can
    /// observe packages emitted immediately by entry launch. The entry component
    /// alone receives `input` and its compiled root authority.
    ///
    /// # Errors
    ///
    /// Returns an error when local state cannot be created, the session cannot
    /// open, or any retained executable cannot launch. Every failure after the
    /// run is created stops already launched executables and closes the new
    /// run, so it cannot be resumed; external effects cannot be rolled back by
    /// this operation.
    pub async fn start(&self, input: Payload) -> Result<RunningApplication, ApplicationStartError> {
        let working_directory =
            std::env::current_dir().map_err(ApplicationStartError::WorkingDirectory)?;
        self.start_in(working_directory.join(".ontography"), input)
            .await
    }

    /// Creates a new persistent run below `state_root` and launches every node.
    ///
    /// The resulting ledger and object store are placed below
    /// `<state_root>/runs/<run-id>`. Every invocation creates a distinct run
    /// and never resumes or overwrites an existing one.
    ///
    /// # Errors
    ///
    /// Returns an error when the run directory or persistent session cannot be
    /// created, or when an executable cannot launch. A run that fails after
    /// creation is closed, as for [`Self::start`].
    pub async fn start_in(
        &self,
        state_root: impl AsRef<Path>,
        input: Payload,
    ) -> Result<RunningApplication, ApplicationStartError> {
        let state_root = absolute_path(state_root.as_ref())?;
        let run_path = reserve_run_path(&state_root)?;
        let runtime = ProposalRuntime::with_grammar(Arc::clone(&self.kernel), self.grammar.clone());
        let session = runtime.create_persistent(&run_path)?;
        self.launch(
            runtime,
            session,
            ApplicationRunMode::Fresh,
            Some(input),
            Some(run_path),
        )
        .await
    }

    /// Opens a new in-memory `SQLite` run without creating persistent files.
    ///
    /// # Errors
    ///
    /// Returns an error when the session cannot open or an executable cannot
    /// launch.
    pub async fn start_ephemeral(
        &self,
        input: Payload,
    ) -> Result<RunningApplication, ApplicationStartError> {
        let runtime = ProposalRuntime::with_grammar(Arc::clone(&self.kernel), self.grammar.clone());
        let session = runtime.open()?;
        self.launch(
            runtime,
            session,
            ApplicationRunMode::Fresh,
            Some(input),
            None,
        )
        .await
    }

    /// Explicitly resumes one existing persistent run without injecting a new
    /// entry input or root authority.
    ///
    /// The selected run must still be open. Closed and faulted runs remain
    /// inspectable through the lower-level proposal runtime but are not
    /// executable application continuations. Retained bindings must match the
    /// run's current graph exactly: a rewrite that removed a bound node or
    /// added a node without a binding fails closed with
    /// [`ApplicationStartError::BindingDrift`]; [`Self::resume_partial`]
    /// accepts that drift explicitly. A failure releases the run without
    /// closing it, so it remains resumable.
    ///
    /// Resumption does not check which application created the run. The run
    /// binds a definition identity, schema, and contracts, so an application
    /// with a differing initial graph under the same identity, schema, and
    /// contracts opens it, and is stopped only by
    /// [`ApplicationStartError::BindingDrift`] when its bindings do not match
    /// the run's current graph.
    ///
    /// # Errors
    ///
    /// Returns an error when the run is absent, incompatible, not open, drifted
    /// from the retained bindings, or an executable cannot launch.
    pub async fn resume(
        &self,
        run_path: impl AsRef<Path>,
    ) -> Result<RunningApplication, ApplicationStartError> {
        self.resume_as(run_path.as_ref(), ApplicationRunMode::Resume)
            .await
    }

    /// Resumes one existing persistent run, launching only the bindings whose
    /// nodes still exist in the run's current graph.
    ///
    /// This is the explicit opt-in for runs whose rewrites removed bound nodes
    /// or added nodes this application has no executable for. Components
    /// observe [`ApplicationRunMode::PartialResume`]. Unbound nodes run no
    /// executable, so packages arriving at them are consumed by nobody.
    ///
    /// # Errors
    ///
    /// Returns an error when the run is absent, incompatible, not open, or an
    /// executable cannot launch.
    pub async fn resume_partial(
        &self,
        run_path: impl AsRef<Path>,
    ) -> Result<RunningApplication, ApplicationStartError> {
        self.resume_as(run_path.as_ref(), ApplicationRunMode::PartialResume)
            .await
    }

    async fn resume_as(
        &self,
        run_path: &Path,
        run_mode: ApplicationRunMode,
    ) -> Result<RunningApplication, ApplicationStartError> {
        let run_path = absolute_path(run_path)?;
        let runtime = ProposalRuntime::with_grammar(Arc::clone(&self.kernel), self.grammar.clone());
        let session = runtime.open_persistent(&run_path)?;
        if session.status() != SessionStatus::Open {
            return Err(ApplicationStartError::NotResumable(session.status()));
        }
        self.launch(runtime, session, run_mode, None, Some(run_path))
            .await
    }

    async fn launch(
        &self,
        runtime: ProposalRuntime,
        session: SessionHandle,
        run_mode: ApplicationRunMode,
        initial_input: Option<Payload>,
        run_path: Option<PathBuf>,
    ) -> Result<RunningApplication, ApplicationStartError> {
        let host = ExecutionHost::new(session.clone());
        let launched = self
            .launch_bindings(
                &host,
                &session,
                run_mode,
                initial_input,
                run_path.as_deref(),
            )
            .await;
        match launched {
            Ok(executions) => Ok(RunningApplication {
                runtime,
                session,
                host,
                executions,
                run_path,
            }),
            Err(error) => {
                host.shutdown().await;
                // A fresh run that never launched is closed so it cannot be
                // resumed as an open run; a resumed run is released as it was.
                if run_mode == ApplicationRunMode::Fresh {
                    runtime.shutdown().await;
                }
                Err(error)
            }
        }
    }

    async fn launch_bindings(
        &self,
        host: &ExecutionHost,
        session: &SessionHandle,
        run_mode: ApplicationRunMode,
        initial_input: Option<Payload>,
        run_path: Option<&Path>,
    ) -> Result<Vec<ExecutionHandle>, ApplicationStartError> {
        let current = session.kernel().await?;
        let bindings = self.launchable(current.graph(), run_mode)?;
        let node_state_root = prepare_node_state(
            run_path,
            bindings.iter().map(|binding| binding.node_id.as_ref()),
        )?;
        let fresh = run_mode == ApplicationRunMode::Fresh;
        let mut executions = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let is_entry = binding.node_id.as_ref() == self.root.node_id();
            let executable = BoundExecutable {
                executable: Arc::clone(&binding.executable),
                run_mode,
                node_state_dir: node_state_root
                    .as_ref()
                    .map(|root| root.join(node_state_directory_name(&binding.node_id))),
                initial_input: initial_input.clone().filter(|_| is_entry),
                root_authority: (is_entry && fresh).then(|| self.root.ceiling().clone()),
                context_policy: binding.context_policy.clone(),
            };
            let execution = host
                .launch(Arc::clone(&binding.node_id), executable)
                .await
                .map_err(|source| ApplicationStartError::Launch {
                    node_id: Arc::clone(&binding.node_id),
                    source,
                })?;
            executions.push(execution);
        }
        Ok(executions)
    }

    /// Selects the bindings launched against `graph`, non-entry components
    /// first so consumers can observe packages emitted by entry launch.
    fn launchable(
        &self,
        graph: &Graph,
        run_mode: ApplicationRunMode,
    ) -> Result<Vec<&LaunchBinding>, ApplicationStartError> {
        let present = |binding: &&LaunchBinding| graph.node(&binding.node_id).is_some();
        let removed = self
            .bindings
            .iter()
            .filter(|binding| !present(binding))
            .map(|binding| Arc::clone(&binding.node_id))
            .collect::<Vec<_>>();
        let unbound = graph
            .nodes()
            .iter()
            .filter(|node| {
                !self
                    .bindings
                    .iter()
                    .any(|binding| binding.node_id.as_ref() == node.id())
            })
            .map(|node| Arc::from(node.id()))
            .collect::<Vec<_>>();
        if run_mode != ApplicationRunMode::PartialResume
            && !(removed.is_empty() && unbound.is_empty())
        {
            return Err(ApplicationStartError::BindingDrift { removed, unbound });
        }
        let (entry, others): (Vec<_>, Vec<_>) = self
            .bindings
            .iter()
            .filter(present)
            .partition(|binding| binding.node_id.as_ref() == self.root.node_id());
        Ok(others.into_iter().chain(entry).collect())
    }
}

fn prepare_node_state<'a>(
    run_path: Option<&Path>,
    node_ids: impl Iterator<Item = &'a str>,
) -> Result<Option<PathBuf>, ApplicationStartError> {
    let Some(run_path) = run_path else {
        return Ok(None);
    };
    let nodes = run_path.join("nodes");
    create_state_directory(&nodes)?;
    for node_id in node_ids {
        create_state_directory(&nodes.join(node_state_directory_name(node_id)))?;
    }
    Ok(Some(nodes))
}

fn absolute_path(path: &Path) -> Result<PathBuf, ApplicationStartError> {
    if path.is_absolute() {
        return Ok(path.to_path_buf());
    }
    Ok(std::env::current_dir()
        .map_err(ApplicationStartError::WorkingDirectory)?
        .join(path))
}

fn reserve_run_path(state_root: &Path) -> Result<PathBuf, ApplicationStartError> {
    let runs = state_root.join("runs");
    std::fs::create_dir_all(&runs).map_err(|source| ApplicationStartError::StateDirectory {
        path: runs.clone(),
        source,
    })?;
    loop {
        let run = runs.join(uuid::Uuid::new_v4().to_string());
        if !run.exists() {
            return Ok(run);
        }
    }
}

fn create_state_directory(path: &Path) -> Result<(), ApplicationStartError> {
    std::fs::create_dir_all(path).map_err(|source| ApplicationStartError::StateDirectory {
        path: path.to_path_buf(),
        source,
    })
}

fn node_state_directory_name(node_id: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut name = String::with_capacity(5 + node_id.len() * 2);
    name.push_str("node-");
    for byte in node_id.bytes() {
        name.push(char::from(HEX[usize::from(byte >> 4)]));
        name.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    name
}

/// Operational ownership of one live application occurrence session.
pub struct RunningApplication {
    runtime: ProposalRuntime,
    session: SessionHandle,
    host: ExecutionHost,
    executions: Vec<ExecutionHandle>,
    run_path: Option<PathBuf>,
}

impl fmt::Debug for RunningApplication {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RunningApplication")
            .field("runtime", &self.runtime)
            .field("session", &self.session)
            .field("host", &self.host)
            .field("executions", &self.executions)
            .field("run_path", &self.run_path)
            .finish()
    }
}

impl RunningApplication {
    /// Returns the persistent run directory used to resume this run, when any.
    #[must_use]
    pub fn run_path(&self) -> Option<&Path> {
        self.run_path.as_deref()
    }

    /// Returns the proposal session containing canonical application state.
    #[must_use]
    pub const fn session(&self) -> &SessionHandle {
        &self.session
    }

    /// Returns every node execution launched for this run.
    #[must_use]
    pub fn executions(&self) -> &[ExecutionHandle] {
        &self.executions
    }

    /// Returns an exact point-in-time snapshot of canonical occurrence state.
    pub async fn snapshot(&self) -> SessionSnapshot {
        self.session.snapshot().await
    }

    /// Waits until no launched node executable remains live.
    pub async fn wait_idle(&self) {
        self.host.wait_idle().await;
    }

    /// Stops executables while leaving persistent proposal admission open.
    ///
    /// This consumes the running application, releases the `SQLite` owner, and
    /// returns the path that can be supplied to [`Application::resume`]. An
    /// ephemeral run returns `None`.
    pub async fn suspend(self) -> Option<PathBuf> {
        self.stop_executions().await;
        self.run_path.clone()
    }

    /// Stops hosted executables cooperatively, then forcibly aborts any that do
    /// not exit within the bounded application grace period before closing
    /// proposal admission.
    pub async fn shutdown(&self) {
        self.stop_executions().await;
        self.runtime.shutdown().await;
    }

    async fn stop_executions(&self) {
        self.host.stop_accepting();
        self.host.request_stop();
        if tokio::time::timeout(APPLICATION_STOP_GRACE, self.host.wait_idle())
            .await
            .is_err()
        {
            self.host.abort_all();
            self.host.wait_idle().await;
        }
    }
}
