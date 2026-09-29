//! Durable SQLite-backed logical state ownership.
//!
//! One `package_outputs` row is one kernel package record: immutable birth
//! facts, the single delivery, and an exclusive status whose CHECK constraints
//! encode the live/consumed/retired partition. Every mutation is a kernel
//! [`Transition`] evaluated over a view of the rows and applied by
//! [`apply_transition`]; this module derives no graph law of its own.
//! `pending_heads` and `ready_triggers` are derived readiness indexes over
//! live delivered rows.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::Arc;

use rusqlite::{
    Connection, OpenFlags, OptionalExtension, Transaction, TransactionBehavior, params,
};
use thiserror::Error;

use super::object_store::{ObjectStore, ObjectStoreError};
use super::panic_message;
use super::session::{FrontierCounts, PackageHistory, SessionStatus};
use ontography_calculus::storage::{
    Activation, ActivationId, Binding, Checkpoint, Delivery, FragmentData, FrontierView,
    GraphFragment, Output, PackageId, PackageRecord, PackageStatus, PackageView, Retirement,
    RetirementReason, Transition, TransitionKind, Trigger,
};
use ontography_calculus::{
    ActivationProposal, Authority, AuthorityTag, ContentDigest, DefinitionFingerprint,
    DefinitionId, EditPolicy, ExtensionError, IngressMode, Kernel, Payload, Phase, Reject,
    RetireError, RewriteError, RewriteRequest, State, TransferError,
};
use ontography_content::content::ContentId;

pub(crate) mod context;

/// Version of the graph store: every table this module owns. The context
/// store carries its own version; see [`context`] for the compatibility rule.
const SCHEMA_VERSION: i64 = 11;

/// The columns that decode into one package record, in [`decode_record`] order.
const RECORD_COLUMNS: &str =
    "producer_activation, output_id, object_type, authority, content_digest,
            producer_node, delivery_edge, delivery_receiver, status, consumer_activation,
            retire_reason, retire_revision, retire_evidence";

const LIVE_DELIVERED: &str = "status = 0 AND delivery_edge IS NOT NULL";
const LIVE_OUTBOUND: &str = "status = 0 AND delivery_edge IS NULL";

// Artifact references supplement activation facts without changing the kernel's
// exact-byte payload predicates.
const ACTIVATION_CONTENT_SCHEMA: &str = "CREATE TABLE activation_content (
    activation_id BLOB NOT NULL CHECK(length(activation_id) = 16),
    ordinal INTEGER NOT NULL CHECK(ordinal >= 0),
    content BLOB NOT NULL,
    PRIMARY KEY(activation_id, ordinal),
    FOREIGN KEY(activation_id) REFERENCES activations(activation_id)
);";

// Indexed lookup of the retained inputs consumed by an activation.
const PACKAGE_HISTORY_INDEX: &str = "CREATE INDEX package_outputs_consumer
         ON package_outputs(consumer_activation, producer_activation, output_id)
         WHERE consumer_activation IS NOT NULL;";

const RUNTIME_INDEXES: &str = "CREATE INDEX package_outputs_live
         ON package_outputs(producer_activation, output_id)
         WHERE status = 0;
     CREATE INDEX package_outputs_pending
         ON package_outputs(producer_activation, output_id)
         WHERE status = 0 AND delivery_edge IS NOT NULL;
     CREATE INDEX package_outputs_target_pending
         ON package_outputs(delivery_receiver, producer_activation, output_id)
         WHERE status = 0 AND delivery_edge IS NOT NULL;
     CREATE INDEX package_outputs_group_pending
         ON package_outputs(
             delivery_receiver, authority, delivery_edge, producer_activation, output_id
         )
         WHERE status = 0 AND delivery_edge IS NOT NULL;
     CREATE INDEX package_outputs_outbound
         ON package_outputs(producer_activation, output_id)
         WHERE status = 0 AND delivery_edge IS NULL;
     CREATE INDEX package_outputs_holder_outbound
         ON package_outputs(producer_node, producer_activation, output_id)
         WHERE status = 0 AND delivery_edge IS NULL;
     CREATE INDEX pending_heads_edge
         ON pending_heads(holder_node, edge_id, producer_activation, output_id);
     CREATE INDEX ready_triggers_by_package
         ON ready_triggers(holder_node, first_package);";

type ReadyTriggerMap = BTreeMap<(String, Vec<u8>), Vec<u8>>;

/// Failure inside the storage adapter.
///
/// Every variant except [`Self::Content`], [`Self::Evidence`], and
/// [`Self::Panicked`] may arise after a write has begun, so the session
/// faults on it. Those three are produced only before any write of the
/// operation, by construction: the caller's content references are checked
/// and the evaluator, which reads its evidence, runs before the first row or
/// object is written.
#[derive(Debug, Error)]
pub(super) enum SqliteStateError {
    #[error("SQLite operation failed: {}", describe_database_error(.0))]
    Database(#[from] rusqlite::Error),
    #[error("persistent session already exists")]
    AlreadyExists,
    #[error("persistent session has not been initialized")]
    NotInitialized,
    #[error("unsupported persistent schema version {0}")]
    SchemaVersion(i64),
    #[error("unsupported context schema version {0}")]
    ContextSchemaVersion(i64),
    #[error("SQLite session state is invalid: {0}")]
    Invalid(Arc<str>),
    #[error(transparent)]
    Object(#[from] ObjectStoreError),
    #[error("invalid proposed content dependency: {0}")]
    Content(ObjectStoreError),
    /// A package row names payload bytes the object store could not supply:
    /// an integrity failure of this store, never a lawful refusal.
    #[error("payload evidence could not be read: {0}")]
    Evidence(ObjectStoreError),
    #[error("trusted evaluation panicked before writing: {0}")]
    Panicked(Arc<str>),
}

impl SqliteStateError {
    fn invalid(message: impl Into<Arc<str>>) -> Self {
        Self::Invalid(message.into())
    }

    /// Reports whether this error is one that, by construction, can only have
    /// arisen before the operation wrote anything.
    pub(super) const fn before_any_write(&self) -> bool {
        matches!(
            self,
            Self::Content(_) | Self::Evidence(_) | Self::Panicked(_)
        )
    }
}

/// Renders a `rusqlite` error with its `SQLite` result code, which the
/// library's own `Display` omits whenever `SQLite` supplied a message.
fn describe_database_error(error: &rusqlite::Error) -> String {
    match error.sqlite_error() {
        Some(code) => format!("{error} (sqlite code {code})", code = code.extended_code),
        None => error.to_string(),
    }
}

/// Runs one evaluator, turning a panic into [`SqliteStateError::Panicked`].
///
/// Evaluators are pure and run before any write, so a panic leaves nothing to
/// undo; the enclosing transaction is dropped unchanged.
fn evaluate<T>(evaluator: impl FnOnce() -> T) -> Result<T, SqliteStateError> {
    catch_unwind(AssertUnwindSafe(evaluator))
        .map_err(|panic| SqliteStateError::Panicked(panic_message(panic)))
}

/// The payload resolver an evaluator reads through.
///
/// A package that has a row must have its bytes; an object-store failure is
/// therefore an integrity failure of this store, not a lawful refusal. The
/// failure is retained here and surfaced as [`SqliteStateError::Evidence`]
/// once the evaluator returns, so the session never reports it as
/// [`RewriteError::EvidenceUnavailable`], which the direct kernel API keeps
/// for a caller-supplied resolver.
struct Evidence<'a> {
    objects: &'a ObjectStore,
    failure: Option<ObjectStoreError>,
}

impl<'a> Evidence<'a> {
    const fn new(objects: &'a ObjectStore) -> Self {
        Self {
            objects,
            failure: None,
        }
    }

    fn resolve(&mut self, digest: ContentDigest) -> Result<Payload, RewriteError> {
        self.objects.require(digest).map_err(|error| {
            let message = Arc::from(error.to_string());
            self.failure = Some(error);
            RewriteError::EvidenceUnavailable(message)
        })
    }

    /// Reclassifies an evaluation whose evidence read failed.
    fn checked<T>(self, evaluated: T) -> Result<T, SqliteStateError> {
        match self.failure {
            Some(error) => Err(SqliteStateError::Evidence(error)),
            None => Ok(evaluated),
        }
    }
}

pub(super) struct SqliteSession {
    connection: Connection,
}

pub(super) struct OpenedSqliteSession {
    pub(super) session: SqliteSession,
    pub(super) status: SessionStatus,
    pub(super) current_kernel: Arc<Kernel>,
    pub(super) revision: u64,
    pub(super) fault: Option<Arc<str>>,
}

/// One committed transition's value and the revision it produced.
pub(super) struct Committed<T> {
    pub(super) value: T,
    pub(super) revision: u64,
}

pub(super) struct PendingRead {
    pub(super) revision: u64,
    pub(super) packages: Vec<(PackageId, PackageRecord)>,
}

/// The write a caller links to one submission inside its transaction.
///
/// It receives the accepted activation identity, or the kernel's rejection,
/// after the graph rows are written and before the transaction commits; a
/// linked write that fails discards the whole submission.
pub(super) trait LinkedWrite:
    FnOnce(&Transaction<'_>, Result<ActivationId, &Reject>) -> Result<(), SqliteStateError>
{
}

impl<F> LinkedWrite for F where
    F: FnOnce(&Transaction<'_>, Result<ActivationId, &Reject>) -> Result<(), SqliteStateError>
{
}

/// The linked write of an unlinked submission.
#[allow(
    clippy::unnecessary_wraps,
    reason = "the signature is the LinkedWrite contract"
)]
pub(super) fn unlinked(
    _: &Transaction<'_>,
    _: Result<ActivationId, &Reject>,
) -> Result<(), SqliteStateError> {
    Ok(())
}

/// Rows pre-fetched for one evaluation, so the kernel's view is infallible.
///
/// The binding carries a constant nonce: the store is exclusively owned and
/// [`apply_transition`] fences on the revision inside the same transaction.
struct SqliteView {
    binding: Binding,
    records: BTreeMap<PackageId, PackageRecord>,
    activations: BTreeSet<ActivationId>,
    live: Vec<(PackageId, PackageRecord)>,
    used_node_ids: BTreeSet<Arc<str>>,
    used_edge_ids: BTreeSet<Arc<str>>,
}

impl PackageView for SqliteView {
    fn record(&self, package: PackageId) -> Option<PackageRecord> {
        self.records.get(&package).cloned()
    }

    fn activation_known(&self, activation: ActivationId) -> bool {
        self.activations.contains(&activation)
    }

    fn binding(&self) -> Binding {
        self.binding.clone()
    }
}

impl FrontierView for SqliteView {
    fn live(&self) -> Vec<(PackageId, PackageRecord)> {
        self.live.clone()
    }

    fn used_node_ids(&self) -> BTreeSet<Arc<str>> {
        self.used_node_ids.clone()
    }

    fn used_edge_ids(&self) -> BTreeSet<Arc<str>> {
        self.used_edge_ids.clone()
    }
}

impl SqliteSession {
    pub(super) fn reconcile_objects(&self, objects: &ObjectStore) -> Result<(), SqliteStateError> {
        let (payloads, contents) = self.content_references()?;
        objects.reconcile(payloads, contents)?;
        Ok(())
    }

    fn content_references(&self) -> Result<(Vec<ContentDigest>, Vec<ContentId>), SqliteStateError> {
        let mut statement = self.connection.prepare("SELECT result_digest FROM activations UNION SELECT content_digest FROM package_outputs")?;
        let mut rows = statement.query([])?;
        let mut payloads = Vec::new();
        while let Some(row) = rows.next()? {
            payloads.push(decode_digest(row.get(0)?)?);
        }
        let mut statement = self
            .connection
            .prepare("SELECT content FROM activation_content")?;
        let mut rows = statement.query([])?;
        let mut contents = Vec::new();
        while let Some(row) = rows.next()? {
            contents.push(decode_content_id(row.get(0)?)?);
        }
        self.context_references(&mut payloads, &mut contents)?;
        Ok((payloads, contents))
    }

    /// Resolve an uncertain commit through the authoritative ledger before
    /// reopening admission. Corruption leaves the durable fault intact.
    pub(super) fn recover_fault(
        &mut self,
        kernel: &Kernel,
        objects: &ObjectStore,
    ) -> Result<(), SqliteStateError> {
        self.snapshot(kernel, objects)?;
        self.verify_context_objects(objects)?;
        let (payloads, contents) = self.content_references()?;
        for digest in payloads.into_iter().collect::<BTreeSet<_>>() {
            objects.require(digest)?;
        }
        objects.verify_content(&contents)?;
        self.reconcile_objects(objects)?;
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Exclusive)?;
        transaction.execute(
            "UPDATE session_meta SET status = 0, fault = NULL WHERE singleton = 1 AND status = 2",
            [],
        )?;
        transaction.commit()?;
        Ok(())
    }
    pub(super) fn create(
        path: &Path,
        kernel: &Kernel,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let connection = open_locked_connection(path, true)?;
        configure_durability(&connection)?;
        Self::initialize(connection, kernel)
    }

    pub(super) fn create_in_memory(
        kernel: &Kernel,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let connection = Connection::open_in_memory()?;
        configure_connection(&connection)?;
        Self::initialize(connection, kernel)
    }

    pub(super) fn restore_in_memory(
        kernel: &Kernel,
        state: &State,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let mut opened = Self::create_in_memory(kernel)?;
        opened.session.import_state(kernel, state)?;
        let opened = Self::read_opened(opened.session.connection, kernel)?;
        validate_readiness(&opened.session.connection, &opened.current_kernel)?;
        Ok(opened)
    }

    fn initialize(
        mut connection: Connection,
        kernel: &Kernel,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let transaction = connection.transaction_with_behavior(TransactionBehavior::Immediate)?;
        let version =
            transaction.query_row("PRAGMA user_version", [], |row| row.get::<_, i64>(0))?;
        let existing = transaction.query_row(
            "SELECT EXISTS(SELECT 1 FROM sqlite_schema WHERE name NOT LIKE 'sqlite_%')",
            [],
            |row| row.get::<_, bool>(0),
        )?;
        if version != 0 || existing {
            return Err(SqliteStateError::AlreadyExists);
        }
        create_schema(&transaction)?;
        let state = kernel.empty_state();
        transaction.execute(
            "INSERT INTO session_meta (singleton, definition_id, definition_fingerprint,
                current_graph, used_node_ids, used_edge_ids, status, state_revision, fault)
             VALUES (1, ?1, ?2, ?3, ?4, ?5, 0, 0, NULL)",
            params![
                kernel.id().as_str(),
                kernel.fingerprint().as_bytes().as_slice(),
                encode_fragment(kernel)?,
                encode_ids(state.used_node_ids())?,
                encode_ids(state.used_edge_ids())?
            ],
        )?;
        transaction.commit()?;
        Self::read_opened(connection, kernel)
    }

    fn import_state(&mut self, kernel: &Kernel, state: &State) -> Result<(), SqliteStateError> {
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let existing = transaction.query_row("SELECT COUNT(*) FROM activations", [], |row| {
            row.get::<_, i64>(0)
        })?;
        if existing != 0 {
            return Err(SqliteStateError::invalid(
                "restored state requires an empty SQLite session",
            ));
        }
        for (activation_id, activation) in state.activations() {
            insert_activation_record(&transaction, *activation_id, activation)?;
        }
        for activation in state.activations().values() {
            for (package_id, output) in activation.package_outputs() {
                let record = state.package(*package_id).ok_or_else(|| {
                    SqliteStateError::invalid("restored output has no package record")
                })?;
                insert_package_record(&transaction, *package_id, record, output.edge_id())?;
            }
        }
        write_current_definition(&transaction, kernel, state)?;
        rebuild_readiness(&transaction, kernel)?;
        transaction.commit()?;
        Ok(())
    }

    pub(super) fn open(
        path: &Path,
        kernel: &Kernel,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let mut connection = open_locked_connection(path, false)?;
        let version =
            connection.query_row("PRAGMA user_version", [], |row| row.get::<_, i64>(0))?;
        match version {
            0 => return Err(SqliteStateError::NotInitialized),
            SCHEMA_VERSION => {}
            version => return Err(SqliteStateError::SchemaVersion(version)),
        }
        context::verify_schema(&connection)?;
        let _ = read_current_kernel(&connection, kernel)?;
        configure_durability(&connection)?;
        let transaction = connection.transaction_with_behavior(TransactionBehavior::Exclusive)?;
        context::interrupt_open(&transaction, "runtime restarted before completion")?;
        transaction.commit()?;
        let opened = Self::read_opened(connection, kernel)?;
        // The derived readiness indexes are checked against the canonical
        // rows on every open; the check is O(frontier).
        validate_readiness(&opened.session.connection, &opened.current_kernel)?;
        Ok(opened)
    }

    pub(super) fn verify_opened(
        opened: OpenedSqliteSession,
        kernel: &Kernel,
        objects: &ObjectStore,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        validate_definition_binding(&opened.session.connection, kernel)?;
        let state = opened.session.snapshot(&opened.current_kernel, objects)?;
        let parts = state.to_parts().map_err(|_| {
            SqliteStateError::invalid(
                "historical reachability verification is unavailable after rewrites, \
                 transfers, retirements, or extensions",
            )
        })?;
        let evidence = state
            .packages()
            .values()
            .map(|record| {
                let digest = record.content_digest();
                objects.require(digest).map(|payload| (digest, payload))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let replayed = kernel
            .restore_state(parts, &evidence)
            .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
        if replayed != state {
            return Err(SqliteStateError::invalid(
                "stored frontier or historical projections disagree with fixed-graph replay",
            ));
        }
        let mut statement = opened
            .session
            .connection
            .prepare("SELECT content FROM activation_content ORDER BY activation_id, ordinal")?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            let content = decode_content_id(row.get(0)?)?;
            objects.verify_content(&[content])?;
        }
        drop(rows);
        drop(statement);
        opened.session.verify_context_objects(objects)?;
        Ok(opened)
    }

    fn read_opened(
        connection: Connection,
        kernel: &Kernel,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        let current_kernel = read_current_kernel(&connection, kernel)?;
        let (status, revision, fault) = connection.query_row(
            "SELECT status, state_revision, fault FROM session_meta WHERE singleton = 1",
            [],
            |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, Option<String>>(2)?,
                ))
            },
        )?;
        let status = decode_status(status)?;
        let revision = decode_u64(revision, "state revision")?;
        let fault = fault.map(Arc::from);
        if (status == SessionStatus::Faulted) != fault.is_some() {
            return Err(SqliteStateError::invalid(
                "session lifecycle status and fault record disagree",
            ));
        }
        Ok(OpenedSqliteSession {
            session: Self { connection },
            current_kernel,
            status,
            revision,
            fault,
        })
    }

    /// Evaluates and commits one activation proposal in a single transaction.
    ///
    /// `link` is the caller's activation-linked write; it runs inside the
    /// transaction after the graph rows and before the commit, on acceptance
    /// and on kernel rejection alike, so a caller's own record of the decision
    /// is atomic with the decision. The order of writes is fixed: content
    /// references are protected, the evaluator runs, objects are published,
    /// and only then are rows written. [`SqliteStateError::Content`] and
    /// [`SqliteStateError::Panicked`] therefore precede every write.
    pub(super) fn submit(
        &mut self,
        kernel: &Kernel,
        objects: &mut ObjectStore,
        proposal: ActivationProposal,
        contents: &[ContentId],
        link: impl LinkedWrite,
    ) -> Result<Result<Committed<ActivationId>, Reject>, SqliteStateError> {
        let package_ids = proposal
            .package_ids()
            .map(|ids| ids.iter().copied().collect::<Vec<_>>())
            .unwrap_or_default();
        let emitted_payloads = proposal.emission_payloads().cloned().collect::<Vec<_>>();
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let durable_status = transaction.query_row(
            "SELECT status FROM session_meta WHERE singleton = 1",
            [],
            |row| row.get::<_, i64>(0),
        )?;
        if durable_status != 0 {
            return Err(SqliteStateError::invalid("proposal session is not open"));
        }
        // Caller-supplied references are checked before publication. A foreign
        // or malformed reference rejects this operation without faulting an
        // otherwise healthy session.
        let _content_protection = objects
            .protect_content(contents)
            .map_err(SqliteStateError::Content)?;
        let activation_id = fresh_activation_id(&transaction)?;
        let view = read_view(&transaction, &package_ids, &[], false)?;
        let transition =
            match evaluate(|| kernel.evaluate_activation(&view, activation_id, proposal))? {
                Ok(transition) => transition,
                Err(reject) => {
                    link(&transaction, Err(&reject))?;
                    transaction.commit()?;
                    return Ok(Err(reject));
                }
            };
        let batch = object_batch(&transition, &emitted_payloads)?;
        objects.put_all(&batch)?;
        // The synchronous object-store boundary is also the durability fence
        // for imported files and collection members. No cancellation point may
        // separate protecting their bytes from publishing the activation.
        objects.retain_content(contents)?;
        let revision = apply_transition(&transaction, &transition, kernel, None)?;
        for (ordinal, content) in contents.iter().enumerate() {
            let ordinal = i64::try_from(ordinal)
                .map_err(|_| SqliteStateError::invalid("too many activation content references"))?;
            transaction.execute(
                "INSERT INTO activation_content (activation_id, ordinal, content)
                 VALUES (?1, ?2, ?3)",
                params![
                    activation_blob(activation_id).as_slice(),
                    ordinal,
                    encode_json(content)?
                ],
            )?;
        }
        link(&transaction, Ok(activation_id))?;
        transaction.commit()?;
        Ok(Ok(Committed {
            value: activation_id,
            revision,
        }))
    }

    pub(super) fn activation_content(
        &self,
        activation_id: ActivationId,
    ) -> Result<Vec<ContentId>, SqliteStateError> {
        let mut statement = self.connection.prepare(
            "SELECT content FROM activation_content WHERE activation_id = ?1 ORDER BY ordinal",
        )?;
        let mut rows = statement.query([activation_blob(activation_id).as_slice()])?;
        let mut contents = Vec::new();
        while let Some(row) = rows.next()? {
            contents.push(decode_content_id(row.get(0)?)?);
        }
        Ok(contents)
    }

    pub(super) fn all_activation_content(
        &self,
    ) -> Result<BTreeMap<ActivationId, Vec<ContentId>>, SqliteStateError> {
        let mut statement = self.connection.prepare(
            "SELECT activation_id, content FROM activation_content ORDER BY activation_id, ordinal",
        )?;
        let mut rows = statement.query([])?;
        let mut contents = BTreeMap::<ActivationId, Vec<ContentId>>::new();
        while let Some(row) = rows.next()? {
            contents
                .entry(decode_activation(row.get(0)?)?)
                .or_default()
                .push(decode_content_id(row.get(1)?)?);
        }
        Ok(contents)
    }

    pub(super) fn close(&mut self) -> Result<(), SqliteStateError> {
        let transaction = self.connection.transaction()?;
        context::interrupt_open(&transaction, "session closed")?;
        transaction.execute(
            "UPDATE session_meta SET status = 1 WHERE singleton = 1 AND status = 0",
            [],
        )?;
        transaction.commit()?;
        Ok(())
    }

    pub(super) fn fault(&mut self, fault: &str) -> Result<(), SqliteStateError> {
        let transaction = self.connection.transaction()?;
        context::interrupt_open(&transaction, "session faulted")?;
        transaction.execute(
            "UPDATE session_meta SET status = 2, fault = ?1 WHERE singleton = 1",
            [fault],
        )?;
        transaction.commit()?;
        Ok(())
    }

    pub(super) fn frontier_counts(
        &self,
    ) -> Result<BTreeMap<Arc<str>, FrontierCounts>, SqliteStateError> {
        let mut counts = BTreeMap::<Arc<str>, FrontierCounts>::new();
        // Partial indexes exclude consumed/retired history and cover each count.
        for (phase, holder, index, predicate) in [
            (
                Phase::In,
                "delivery_receiver",
                "package_outputs_target_pending",
                LIVE_DELIVERED,
            ),
            (
                Phase::Out,
                "producer_node",
                "package_outputs_holder_outbound",
                LIVE_OUTBOUND,
            ),
        ] {
            let sql = format!(
                "SELECT {holder}, COUNT(*) FROM package_outputs INDEXED BY {index}
                 WHERE {predicate} GROUP BY {holder}"
            );
            let mut statement = self.connection.prepare(&sql)?;
            let mut rows = statement.query([])?;
            while let Some(row) = rows.next()? {
                let node: String = row.get(0)?;
                let count = usize::try_from(row.get::<_, i64>(1)?)
                    .map_err(|_| SqliteStateError::invalid("live package count is out of range"))?;
                let entry = counts.entry(Arc::from(node)).or_default();
                match phase {
                    Phase::In => entry.received = count,
                    Phase::Out => entry.outbound = count,
                }
            }
        }
        Ok(counts)
    }

    pub(super) fn frontier_page(
        &self,
        phase: Phase,
        node_id: Option<&str>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingRead, SqliteStateError> {
        if limit == 0 {
            return Err(SqliteStateError::invalid(
                "frontier page limit must be greater than zero",
            ));
        }
        let revision = read_revision(&self.connection)?;
        let (index, predicate, holder) = match (phase, node_id.is_some()) {
            (Phase::In, false) => (
                "package_outputs_pending",
                LIVE_DELIVERED,
                "delivery_receiver",
            ),
            (Phase::In, true) => (
                "package_outputs_target_pending",
                LIVE_DELIVERED,
                "delivery_receiver",
            ),
            (Phase::Out, false) => ("package_outputs_outbound", LIVE_OUTBOUND, "producer_node"),
            (Phase::Out, true) => (
                "package_outputs_holder_outbound",
                LIVE_OUTBOUND,
                "producer_node",
            ),
        };
        let mut sql = format!(
            "SELECT {RECORD_COLUMNS} FROM package_outputs INDEXED BY {index} WHERE {predicate}"
        );
        let mut parameters = Vec::<rusqlite::types::Value>::new();
        if let Some(node) = node_id {
            parameters.push(node.to_owned().into());
            let _ = write!(sql, " AND {holder} = ?{}", parameters.len());
        }
        if let Some(after) = after {
            parameters.push(activation_blob(after.producer()).to_vec().into());
            parameters.push(u128_blob(after.output()).to_vec().into());
            let _ = write!(
                sql,
                " AND (producer_activation, output_id) > (?{}, ?{})",
                parameters.len() - 1,
                parameters.len()
            );
        }
        parameters.push(i64::try_from(limit).unwrap_or(i64::MAX).into());
        let _ = write!(
            sql,
            " ORDER BY producer_activation, output_id LIMIT ?{}",
            parameters.len()
        );
        let packages = query_records(
            &self.connection,
            &sql,
            rusqlite::params_from_iter(parameters),
        )?;
        Ok(PendingRead { revision, packages })
    }

    pub(super) fn next_trigger(
        &self,
        node_id: &str,
        ingress_mode: IngressMode,
        incoming_edges: &BTreeSet<Arc<str>>,
    ) -> Result<PendingRead, SqliteStateError> {
        match ingress_mode {
            IngressMode::Any => self.frontier_page(Phase::In, Some(node_id), None, 1),
            IngressMode::All => Ok(PendingRead {
                revision: read_revision(&self.connection)?,
                packages: query_all_trigger(&self.connection, node_id, incoming_edges)?,
            }),
        }
    }

    pub(super) fn next_pending_on_edge(
        &self,
        node_id: &str,
        edge_id: &str,
    ) -> Result<PendingRead, SqliteStateError> {
        let sql = format!(
            "SELECT {} FROM pending_heads h INDEXED BY pending_heads_edge
             JOIN package_outputs o
               ON o.producer_activation = h.producer_activation
              AND o.output_id = h.output_id
              AND o.status = 0
              AND o.delivery_receiver = h.holder_node
              AND o.authority = h.authority
              AND o.delivery_edge = h.edge_id
             WHERE h.holder_node = ?1 AND h.edge_id = ?2
             ORDER BY h.producer_activation, h.output_id
             LIMIT 1",
            qualified_record_columns("o")
        );
        let packages = query_records(&self.connection, &sql, params![node_id, edge_id])?;
        Ok(PendingRead {
            revision: read_revision(&self.connection)?,
            packages,
        })
    }

    pub(super) fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SqliteStateError> {
        let Some((_, record)) = read_record(&self.connection, package_id)? else {
            return Ok(None);
        };
        let producer = activation_blob(package_id.producer());
        let mut statement = self.connection.prepare(
            "SELECT producer_activation, output_id
             FROM package_outputs
             WHERE consumer_activation = ?1
             ORDER BY producer_activation, output_id",
        )?;
        let mut rows = statement.query([producer.as_slice()])?;
        let mut inputs = Vec::new();
        while let Some(row) = rows.next()? {
            inputs.push(PackageId::from_parts(
                decode_activation(row.get(0)?)?,
                decode_u128(row.get(1)?, "package output identity")?,
            ));
        }
        Ok(Some(PackageHistory::new(record, inputs)))
    }

    pub(super) fn snapshot(
        &self,
        kernel: &Kernel,
        objects: &ObjectStore,
    ) -> Result<State, SqliteStateError> {
        validate_definition_binding(&self.connection, kernel)?;
        // An exact-state export also proves the derived readiness indexes
        // agree with the rows it exports.
        validate_readiness(&self.connection, kernel)?;
        let (definition_id, fingerprint, revision, used_nodes, used_edges, definition_changes) =
            self.connection.query_row(
                "SELECT definition_id, definition_fingerprint, state_revision,
                        used_node_ids, used_edge_ids, definition_changes
                 FROM session_meta WHERE singleton = 1",
                [],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, Vec<u8>>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, Vec<u8>>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                        row.get::<_, i64>(5)?,
                    ))
                },
            )?;
        let mut records = BTreeMap::<
            ActivationId,
            (Arc<str>, Trigger, Payload, BTreeMap<PackageId, Output>),
        >::new();
        let mut cache = BTreeMap::new();
        let mut statement = self.connection.prepare(
            "SELECT activation_id, trigger_kind, root_node, root_authority, result_digest, execution_node
             FROM activations ORDER BY activation_id",
        )?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            let id = decode_activation(row.get(0)?)?;
            let trigger = match row.get::<_, i64>(1)? {
                0 => Trigger::Orig {
                    node_id: Arc::from(row.get::<_, String>(2)?),
                    authority: decode_authority(&row.get::<_, Vec<u8>>(3)?)?,
                },
                1 => Trigger::Pkgs {
                    package_ids: BTreeSet::new(),
                },
                _ => return Err(SqliteStateError::invalid("unknown trigger kind")),
            };
            records.insert(
                id,
                (
                    Arc::from(row.get::<_, String>(5)?),
                    trigger,
                    cached_object(objects, &mut cache, decode_digest(row.get(4)?)?)?,
                    BTreeMap::new(),
                ),
            );
        }
        let mut packages = BTreeMap::new();
        let sql = format!(
            "SELECT {RECORD_COLUMNS}, birth_edge_id FROM package_outputs
             ORDER BY producer_activation, output_id"
        );
        let mut statement = self.connection.prepare(&sql)?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            let (id, record) = decode_record(row)?;
            let birth_edge = row.get::<_, Option<String>>(13)?;
            let output = match birth_edge {
                Some(edge) => Output::new(
                    edge,
                    record.object_type(),
                    record.authority().clone(),
                    record.content_digest(),
                ),
                None => Output::outbound(
                    record.object_type(),
                    record.authority().clone(),
                    record.content_digest(),
                ),
            };
            let (_, _, _, outputs) = records
                .get_mut(&id.producer())
                .ok_or_else(|| SqliteStateError::invalid("output producer is absent"))?;
            outputs.insert(id, output);
            if let PackageStatus::Consumed(consumer) = record.status() {
                let (_, trigger, _, _) = records
                    .get_mut(consumer)
                    .ok_or_else(|| SqliteStateError::invalid("output consumer is absent"))?;
                let Trigger::Pkgs { package_ids } = trigger else {
                    return Err(SqliteStateError::invalid(
                        "root activation has package inputs",
                    ));
                };
                package_ids.insert(id);
            }
            packages.insert(id, record);
        }
        let activations = records
            .into_iter()
            .map(|(id, (node, trigger, result, outputs))| {
                (id, Activation::new(node, trigger, result, outputs))
            })
            .collect();
        kernel
            .restore_checkpoint(Checkpoint {
                definition_changes: decode_u64(definition_changes, "definition changes")?,
                definition_id: DefinitionId::new(definition_id)
                    .map_err(|error| SqliteStateError::invalid(error.to_string()))?,
                definition_fingerprint: decode_fingerprint(fingerprint)?,
                activations,
                packages,
                used_node_ids: decode_ids(&used_nodes)?,
                used_edge_ids: decode_ids(&used_edges)?,
                revision: decode_u64(revision, "state revision")?,
            })
            .map_err(|error| SqliteStateError::invalid(error.to_string()))
    }

    pub(super) fn prepare_rewrite(
        &mut self,
        kernel: &Kernel,
        objects: &ObjectStore,
        policy: &dyn EditPolicy,
        request: &RewriteRequest,
    ) -> Result<Result<(Transition, Arc<Kernel>), RewriteError>, SqliteStateError> {
        // Rewrite preparation reads the live frontier and lifetime identities
        // only, in one transaction like every other evaluation; activation
        // history and result payloads are never materialized. Nothing is
        // written, so dropping the transaction ends the read.
        let transaction = self.connection.transaction()?;
        let view = read_view(&transaction, &[], &[], true)?;
        let mut evidence = Evidence::new(objects);
        let evaluated = evaluate(|| {
            kernel.evaluate_rewrite(&view, policy, request, |_, digest| evidence.resolve(digest))
        })?;
        drop(transaction);
        evidence.checked(evaluated)
    }

    /// Applies a prepared rewrite if the stored revision is still its base.
    ///
    /// A moved revision is the kernel's own [`RewriteError::Stale`], exactly as
    /// [`Kernel::commit_rewrite`] reports a binding mismatch.
    pub(super) fn commit_rewrite(
        &mut self,
        kernel: &Kernel,
        transition: &Transition,
        next: &Kernel,
    ) -> Result<Result<Committed<()>, RewriteError>, SqliteStateError> {
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        if read_revision(&transaction)? != transition.base().revision() {
            return Ok(Err(RewriteError::Stale));
        }
        let revision = apply_transition(&transaction, transition, kernel, Some(next))?;
        transaction.commit()?;
        Ok(Ok(Committed {
            value: (),
            revision,
        }))
    }

    pub(super) fn transfer(
        &mut self,
        kernel: &Kernel,
        objects: &ObjectStore,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Result<Committed<Delivery>, TransferError>, SqliteStateError> {
        // The selected facts, kernel proof, and update share one transaction
        // under the session lock; no full-state snapshot or stale plan is needed.
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let view = read_view(&transaction, &[package_id], &[], false)?;
        let mut evidence = Evidence::new(objects);
        let evaluated = evaluate(|| {
            kernel.evaluate_transfer(&view, package_id, edge_id, |_, digest| {
                evidence.resolve(digest)
            })
        })?;
        let transition = match evidence.checked(evaluated)? {
            Ok(transition) => transition,
            Err(TransferError::Admission(RewriteError::InvalidState(message))) => {
                return Err(SqliteStateError::invalid(message));
            }
            Err(error) => return Ok(Err(error)),
        };
        let TransitionKind::Transfer { delivery, .. } = transition.kind() else {
            return Err(SqliteStateError::invalid(
                "transfer transition does not deliver",
            ));
        };
        let delivery = delivery.clone();
        let revision = apply_transition(&transaction, &transition, kernel, None)?;
        transaction.commit()?;
        Ok(Ok(Committed {
            value: delivery,
            revision,
        }))
    }

    pub(super) fn retire(
        &mut self,
        kernel: &Kernel,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Result<Committed<Retirement>, RetireError>, SqliteStateError> {
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let cited = evidence.map(|id| vec![id]).unwrap_or_default();
        let view = read_view(&transaction, &[package_id], &cited, false)?;
        let transition = match evaluate(|| kernel.evaluate_retire(&view, package_id, evidence))? {
            Ok(transition) => transition,
            Err(RetireError::Admission(RewriteError::InvalidState(message))) => {
                return Err(SqliteStateError::invalid(message));
            }
            Err(error) => return Ok(Err(error)),
        };
        let TransitionKind::Retire { retirement, .. } = transition.kind() else {
            return Err(SqliteStateError::invalid(
                "retire transition does not retire",
            ));
        };
        let retirement = retirement.clone();
        let revision = apply_transition(&transaction, &transition, kernel, None)?;
        transaction.commit()?;
        Ok(Ok(Committed {
            value: retirement,
            revision,
        }))
    }

    pub(super) fn extend(
        &mut self,
        kernel: &Kernel,
        next: &Kernel,
    ) -> Result<Result<Committed<()>, ExtensionError>, SqliteStateError> {
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let view = read_view(&transaction, &[], &[], false)?;
        let transition = match evaluate(|| kernel.evaluate_extension_transition(&view, next))? {
            Ok(transition) => transition,
            Err(error) => return Ok(Err(error)),
        };
        let revision = apply_transition(&transaction, &transition, kernel, Some(next))?;
        transaction.commit()?;
        Ok(Ok(Committed {
            value: (),
            revision,
        }))
    }
}

/// Checks the derived readiness indexes against the canonical package rows.
///
/// `pending_heads` must hold exactly the least live delivered package of every
/// (receiver, authority, edge) group, and `ready_triggers` must equal the
/// bundles recomputed from those heads. The cost is O(frontier).
fn validate_readiness(connection: &Connection, kernel: &Kernel) -> Result<(), SqliteStateError> {
    {
        let invalid_head = connection.query_row(
            "SELECT EXISTS (
                SELECT 1
                FROM pending_heads h
                LEFT JOIN package_outputs o
                  ON o.producer_activation = h.producer_activation
                 AND o.output_id = h.output_id
                WHERE o.producer_activation IS NULL
                   OR NOT (o.status = 0 AND o.delivery_edge IS NOT NULL)
                   OR o.delivery_receiver != h.holder_node
                   OR o.authority != h.authority
                   OR o.delivery_edge != h.edge_id
                   OR EXISTS (
                       SELECT 1
                       FROM package_outputs earlier
                       WHERE earlier.status = 0 AND earlier.delivery_edge IS NOT NULL
                         AND earlier.delivery_receiver = h.holder_node
                         AND earlier.authority = h.authority
                         AND earlier.delivery_edge = h.edge_id
                         AND (earlier.producer_activation, earlier.output_id)
                             < (h.producer_activation, h.output_id)
                   )
                UNION ALL
                SELECT 1
                FROM package_outputs o
                WHERE o.status = 0 AND o.delivery_edge IS NOT NULL
                  AND NOT EXISTS (
                      SELECT 1
                      FROM pending_heads h
                      WHERE h.holder_node = o.delivery_receiver
                        AND h.authority = o.authority
                        AND h.edge_id = o.delivery_edge
                  )
             )",
            [],
            |row| row.get::<_, bool>(0),
        )?;
        if invalid_head {
            return Err(SqliteStateError::invalid(
                "pending trigger-head projection disagrees with canonical packages",
            ));
        }
    }
    let expected = expected_ready_triggers(connection, kernel)?;
    let actual = {
        let mut statement = connection.prepare(
            "SELECT holder_node, authority, first_package
             FROM ready_triggers
             ORDER BY holder_node, authority",
        )?;
        let rows = statement.query_map([], |row| {
            Ok((
                (row.get::<_, String>(0)?, row.get::<_, Vec<u8>>(1)?),
                row.get::<_, Vec<u8>>(2)?,
            ))
        })?;
        rows.collect::<Result<BTreeMap<_, _>, _>>()?
    };
    if actual != expected {
        return Err(SqliteStateError::invalid(
            "ready-trigger projection disagrees with pending heads",
        ));
    }
    Ok(())
}

/// Applies one evaluated transition as row writes, fencing on the stored revision.
///
/// The transition is re-verified with [`Transition::verify`] over this
/// transaction's own rows before anything is written, so the `SQLite` applier
/// rejects exactly what the in-memory applier rejects. Each write additionally
/// guards its precondition in its `WHERE` clause; a write that changes no row
/// is an integrity failure. Readiness indexes are maintained incrementally for
/// the affected groups and rebuilt when the graph changes.
fn apply_transition(
    transaction: &Transaction<'_>,
    transition: &Transition,
    current: &Kernel,
    next: Option<&Kernel>,
) -> Result<u64, SqliteStateError> {
    let stored = read_revision(transaction)?;
    if transition.base().revision() != stored {
        return Err(SqliteStateError::invalid(
            "transition base revision is not current",
        ));
    }
    validate_definition_binding(transaction, current)?;
    let (packages, activations, frontier) = touched(transition);
    let view = read_view(transaction, &packages, &activations, frontier)?;
    transition.verify(current, &view).map_err(|error| {
        SqliteStateError::invalid(format!("transition failed verification: {error}"))
    })?;
    let successor = stored
        .checked_add(1)
        .ok_or_else(|| SqliteStateError::invalid("state revision exhausted"))?;
    let mut changed_groups = BTreeSet::<(Arc<str>, Vec<u8>)>::new();
    match transition.kind() {
        TransitionKind::Activation {
            id,
            activation,
            outputs,
            ..
        } => {
            // The activation row first: consumed inputs reference it.
            insert_activation_record(transaction, *id, activation)?;
            for package in activation.inputs().into_iter().flatten() {
                let group = read_delivered_group(transaction, *package)?;
                let changed = transaction.execute(
                    "UPDATE package_outputs SET status = 1, consumer_activation = ?1
                     WHERE producer_activation = ?2 AND output_id = ?3
                       AND status = 0 AND delivery_edge IS NOT NULL",
                    params![
                        activation_blob(*id).as_slice(),
                        activation_blob(package.producer()).as_slice(),
                        u128_blob(package.output()).as_slice()
                    ],
                )?;
                if changed != 1 {
                    return Err(SqliteStateError::invalid(format!(
                        "consumed package {package} is not live and delivered"
                    )));
                }
                retire_head(transaction, group, *package, &mut changed_groups)?;
            }
            for (package, record) in outputs {
                let birth_edge = activation
                    .package_outputs()
                    .get(package)
                    .and_then(Output::edge_id);
                insert_package_record(transaction, *package, record, birth_edge)?;
                if let Some(delivery) = record.delivery() {
                    let authority = encode_authority(record.authority())?;
                    if insert_pending_head(
                        transaction,
                        delivery.receiver(),
                        &authority,
                        delivery.edge_id(),
                        *package,
                    )? {
                        changed_groups.insert((Arc::from(delivery.receiver()), authority));
                    }
                }
            }
        }
        TransitionKind::Transfer {
            package, delivery, ..
        } => {
            let changed = transaction.execute(
                "UPDATE package_outputs SET delivery_edge = ?1, delivery_receiver = ?2
                 WHERE producer_activation = ?3 AND output_id = ?4
                   AND status = 0 AND delivery_edge IS NULL",
                params![
                    delivery.edge_id(),
                    delivery.receiver(),
                    activation_blob(package.producer()).as_slice(),
                    u128_blob(package.output()).as_slice()
                ],
            )?;
            if changed != 1 {
                return Err(SqliteStateError::invalid(format!(
                    "delivered package {package} is not live and outbound"
                )));
            }
            let group = read_delivered_group(transaction, *package)?;
            if insert_pending_head(
                transaction,
                &group.receiver,
                &group.authority,
                &group.edge,
                *package,
            )? {
                changed_groups.insert((group.receiver, group.authority));
            }
        }
        TransitionKind::Retire {
            package,
            retirement,
        } => retire_package(transaction, *package, retirement, &mut changed_groups)?,
        TransitionKind::Rewrite {
            retirements,
            fresh_node_ids,
            fresh_edge_ids,
            ..
        } => {
            for (package, retirement) in retirements {
                retire_package(transaction, *package, retirement, &mut changed_groups)?;
            }
            let (mut nodes, mut edges) = read_used_ids(transaction)?;
            nodes.extend(fresh_node_ids.iter().cloned());
            edges.extend(fresh_edge_ids.iter().cloned());
            transaction.execute(
                "UPDATE session_meta SET used_node_ids = ?1, used_edge_ids = ?2
                 WHERE singleton = 1",
                params![encode_ids(&nodes)?, encode_ids(&edges)?],
            )?;
        }
        TransitionKind::Extension { .. } => {}
    }
    let installed = match transition.next_fingerprint() {
        Some(fingerprint) => {
            let next = next.ok_or_else(|| {
                SqliteStateError::invalid("transition installs a definition without its kernel")
            })?;
            if next.fingerprint() != fingerprint {
                return Err(SqliteStateError::invalid(
                    "installed kernel does not match the transition",
                ));
            }
            transaction.execute(
                "UPDATE session_meta SET definition_fingerprint = ?1, current_graph = ?2
                 WHERE singleton = 1",
                params![
                    next.fingerprint().as_bytes().as_slice(),
                    encode_fragment(next)?
                ],
            )?;
            next
        }
        None => current,
    };
    transaction.execute(
        "UPDATE session_meta SET state_revision = ?1, definition_changes = definition_changes + ?2 WHERE singleton = 1",
        params![encode_u64(successor)?, i64::from(transition.next_fingerprint().is_some())],
    )?;
    let touched_readiness = !changed_groups.is_empty();
    if installed.graph() == current.graph() {
        for (node_id, authority) in changed_groups {
            refresh_ready_trigger(transaction, installed, &node_id, &authority)?;
        }
    } else {
        rebuild_readiness(transaction, installed)?;
    }
    // Debug builds recompute the readiness projection after every transition
    // that maintained it, so an incremental update that drifts from the
    // rebuilt indexes fails the transaction instead of a later trigger read.
    #[cfg(debug_assertions)]
    if touched_readiness || installed.graph() != current.graph() {
        validate_readiness(transaction, installed)?;
    }
    #[cfg(not(debug_assertions))]
    let _ = touched_readiness;
    Ok(successor)
}

/// The rows a transition's verification reads: packages, activations, and
/// whether the whole live frontier is needed.
fn touched(transition: &Transition) -> (Vec<PackageId>, Vec<ActivationId>, bool) {
    match transition.kind() {
        TransitionKind::Activation {
            id,
            activation,
            outputs,
            ..
        } => {
            let mut packages: Vec<PackageId> = outputs.iter().map(|(id, _)| *id).collect();
            packages.extend(activation.inputs().into_iter().flatten().copied());
            (packages, vec![*id], false)
        }
        TransitionKind::Transfer { package, .. } => (vec![*package], Vec::new(), false),
        TransitionKind::Retire {
            package,
            retirement,
        } => (
            vec![*package],
            retirement.evidence().into_iter().collect(),
            false,
        ),
        TransitionKind::Rewrite { retirements, .. } => (
            retirements.iter().map(|(id, _)| *id).collect(),
            Vec::new(),
            true,
        ),
        TransitionKind::Extension { .. } => (Vec::new(), Vec::new(), false),
    }
}

/// Retires one live package and advances its readiness head if it was delivered.
fn retire_package(
    transaction: &Transaction<'_>,
    package: PackageId,
    retirement: &Retirement,
    changed_groups: &mut BTreeSet<(Arc<str>, Vec<u8>)>,
) -> Result<(), SqliteStateError> {
    // An undelivered package has no readiness group; a database failure is
    // an error, never read as "not delivered".
    let group = read_delivered_group_if_delivered(transaction, package)?;
    let evidence = retirement.evidence().map(activation_blob);
    let changed = transaction.execute(
        "UPDATE package_outputs
         SET status = 2, retire_reason = ?1, retire_revision = ?2, retire_evidence = ?3
         WHERE producer_activation = ?4 AND output_id = ?5 AND status = 0",
        params![
            encode_reason(retirement.reason()),
            encode_u64(retirement.revision())?,
            evidence.as_ref().map(<[u8; 16]>::as_slice),
            activation_blob(package.producer()).as_slice(),
            u128_blob(package.output()).as_slice()
        ],
    )?;
    if changed != 1 {
        return Err(SqliteStateError::invalid(format!(
            "retired package {package} is not live"
        )));
    }
    if let Some(group) = group {
        retire_head(transaction, group, package, changed_groups)?;
    }
    Ok(())
}

/// The readiness group of one live delivered package.
struct DeliveredGroup {
    receiver: Arc<str>,
    authority: Vec<u8>,
    edge: Arc<str>,
}

fn read_delivered_group(
    transaction: &Transaction<'_>,
    package: PackageId,
) -> Result<DeliveredGroup, SqliteStateError> {
    read_delivered_group_if_delivered(transaction, package)?.ok_or_else(|| {
        SqliteStateError::invalid(format!("package {package} is not live and delivered"))
    })
}

/// The readiness group of a live package, or `None` when it is undelivered.
fn read_delivered_group_if_delivered(
    transaction: &Transaction<'_>,
    package: PackageId,
) -> Result<Option<DeliveredGroup>, SqliteStateError> {
    transaction
        .query_row(
            "SELECT delivery_receiver, authority, delivery_edge FROM package_outputs
             WHERE producer_activation = ?1 AND output_id = ?2
               AND status = 0 AND delivery_edge IS NOT NULL",
            params![
                activation_blob(package.producer()).as_slice(),
                u128_blob(package.output()).as_slice()
            ],
            |row| {
                Ok(DeliveredGroup {
                    receiver: Arc::from(row.get::<_, String>(0)?),
                    authority: row.get(1)?,
                    edge: Arc::from(row.get::<_, String>(2)?),
                })
            },
        )
        .optional()
        .map_err(SqliteStateError::from)
}

fn retire_head(
    transaction: &Transaction<'_>,
    group: DeliveredGroup,
    package: PackageId,
    changed_groups: &mut BTreeSet<(Arc<str>, Vec<u8>)>,
) -> Result<(), SqliteStateError> {
    if advance_pending_head(
        transaction,
        &group.receiver,
        &group.authority,
        &group.edge,
        package,
    )? {
        changed_groups.insert((group.receiver, group.authority));
    }
    Ok(())
}

/// Lifetime node and edge identities.
type UsedIds = (BTreeSet<Arc<str>>, BTreeSet<Arc<str>>);

fn read_used_ids(connection: &Connection) -> Result<UsedIds, SqliteStateError> {
    let (nodes, edges) = connection.query_row(
        "SELECT used_node_ids, used_edge_ids FROM session_meta WHERE singleton = 1",
        [],
        |row| Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, Vec<u8>>(1)?)),
    )?;
    Ok((decode_ids(&nodes)?, decode_ids(&edges)?))
}

fn read_binding(connection: &Connection) -> Result<Binding, SqliteStateError> {
    let (id, fingerprint, revision) = connection
        .query_row(
            "SELECT definition_id, definition_fingerprint, state_revision
             FROM session_meta WHERE singleton = 1",
            [],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, Vec<u8>>(1)?,
                    row.get::<_, i64>(2)?,
                ))
            },
        )
        .optional()?
        .ok_or(SqliteStateError::NotInitialized)?;
    Ok(Binding::new(
        DefinitionId::new(id).map_err(|error| SqliteStateError::invalid(error.to_string()))?,
        decode_fingerprint(fingerprint)?,
        decode_u64(revision, "state revision")?,
        0,
    ))
}

/// Pre-fetches everything one evaluation may read.
fn read_view(
    connection: &Connection,
    packages: &[PackageId],
    activations: &[ActivationId],
    frontier: bool,
) -> Result<SqliteView, SqliteStateError> {
    let binding = read_binding(connection)?;
    let mut records = BTreeMap::new();
    for package in packages {
        if let Some((id, record)) = read_record(connection, *package)? {
            records.insert(id, record);
        }
    }
    let mut known = BTreeSet::new();
    for activation in activations {
        let exists = connection.query_row(
            "SELECT EXISTS(SELECT 1 FROM activations WHERE activation_id = ?1)",
            [activation_blob(*activation).as_slice()],
            |row| row.get::<_, bool>(0),
        )?;
        if exists {
            known.insert(*activation);
        }
    }
    let (live, used_node_ids, used_edge_ids) = if frontier {
        let sql = format!(
            "SELECT {RECORD_COLUMNS} FROM package_outputs INDEXED BY package_outputs_live
             WHERE status = 0 ORDER BY producer_activation, output_id"
        );
        let live = query_records(connection, &sql, [])?;
        let (nodes, edges) = read_used_ids(connection)?;
        (live, nodes, edges)
    } else {
        (Vec::new(), BTreeSet::new(), BTreeSet::new())
    };
    Ok(SqliteView {
        binding,
        records,
        activations: known,
        live,
        used_node_ids,
        used_edge_ids,
    })
}

fn read_record(
    connection: &Connection,
    package: PackageId,
) -> Result<Option<(PackageId, PackageRecord)>, SqliteStateError> {
    let sql = format!(
        "SELECT {RECORD_COLUMNS} FROM package_outputs
         WHERE producer_activation = ?1 AND output_id = ?2"
    );
    let mut statement = connection.prepare(&sql)?;
    let mut rows = statement.query(params![
        activation_blob(package.producer()).as_slice(),
        u128_blob(package.output()).as_slice()
    ])?;
    rows.next()?.map(decode_record).transpose()
}

fn qualified_record_columns(alias: &str) -> String {
    RECORD_COLUMNS
        .split(',')
        .map(|column| format!("{alias}.{}", column.trim()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Decodes one row selected with [`RECORD_COLUMNS`] into its package record.
fn decode_record(row: &rusqlite::Row<'_>) -> Result<(PackageId, PackageRecord), SqliteStateError> {
    let id = PackageId::from_parts(
        decode_activation(row.get(0)?)?,
        decode_u128(row.get(1)?, "package output identity")?,
    );
    let object_type = row.get::<_, String>(2)?;
    let authority = decode_authority(&row.get::<_, Vec<u8>>(3)?)?;
    let content_digest = decode_digest(row.get(4)?)?;
    let producer_node = row.get::<_, String>(5)?;
    let delivery = match (
        row.get::<_, Option<String>>(6)?,
        row.get::<_, Option<String>>(7)?,
    ) {
        (Some(edge), Some(receiver)) => Some(Delivery::new(edge, receiver)),
        (None, None) => None,
        _ => {
            return Err(SqliteStateError::invalid(
                "package delivery is half recorded",
            ));
        }
    };
    let status = match (
        row.get::<_, i64>(8)?,
        row.get::<_, Option<Vec<u8>>>(9)?,
        row.get::<_, Option<i64>>(10)?,
        row.get::<_, Option<i64>>(11)?,
        row.get::<_, Option<Vec<u8>>>(12)?,
    ) {
        (0, None, None, None, None) => PackageStatus::Live,
        (1, Some(consumer), None, None, None) => {
            PackageStatus::Consumed(decode_activation(consumer)?)
        }
        (2, None, Some(reason), Some(revision), evidence) => {
            PackageStatus::Retired(Retirement::new(
                decode_reason(reason)?,
                decode_u64(revision, "retirement revision")?,
                evidence.map(decode_activation).transpose()?,
            ))
        }
        _ => return Err(SqliteStateError::invalid("package status columns disagree")),
    };
    Ok((
        id,
        PackageRecord::new(
            object_type,
            authority,
            content_digest,
            producer_node,
            delivery,
            status,
        ),
    ))
}

fn query_records<P>(
    connection: &Connection,
    sql: &str,
    parameters: P,
) -> Result<Vec<(PackageId, PackageRecord)>, SqliteStateError>
where
    P: rusqlite::Params,
{
    let mut statement = connection.prepare(sql)?;
    let mut rows = statement.query(parameters)?;
    let mut packages = Vec::new();
    while let Some(row) = rows.next()? {
        packages.push(decode_record(row)?);
    }
    Ok(packages)
}

fn cached_object(
    objects: &ObjectStore,
    cache: &mut BTreeMap<ContentDigest, Payload>,
    digest: ContentDigest,
) -> Result<Payload, ObjectStoreError> {
    if let Some(payload) = cache.get(&digest) {
        return Ok(payload.clone());
    }
    let payload = objects.require(digest)?;
    cache.insert(digest, payload.clone());
    Ok(payload)
}

fn encode_json(value: &impl serde::Serialize) -> Result<Vec<u8>, SqliteStateError> {
    serde_json::to_vec(value).map_err(|error| SqliteStateError::invalid(error.to_string()))
}

fn encode_fragment(kernel: &Kernel) -> Result<Vec<u8>, SqliteStateError> {
    encode_json(&FragmentData::from(&GraphFragment::from_kernel(kernel)))
}

fn decode_content_id(bytes: Vec<u8>) -> Result<ContentId, SqliteStateError> {
    serde_json::from_slice(&bytes)
        .map_err(|error| SqliteStateError::invalid(format!("invalid content reference: {error}")))
}

fn encode_ids(ids: &BTreeSet<Arc<str>>) -> Result<Vec<u8>, SqliteStateError> {
    encode_json(&ids.iter().map(AsRef::as_ref).collect::<Vec<&str>>())
}

fn decode_ids(bytes: &[u8]) -> Result<BTreeSet<Arc<str>>, SqliteStateError> {
    serde_json::from_slice::<Vec<String>>(bytes)
        .map(|ids| ids.into_iter().map(Arc::from).collect())
        .map_err(|error| SqliteStateError::invalid(error.to_string()))
}

const fn encode_reason(reason: RetirementReason) -> i64 {
    match reason {
        RetirementReason::HolderRemoved => 0,
        RetirementReason::NoAcceptingEdge => 1,
        RetirementReason::RouteRemoved => 2,
        RetirementReason::Explicit => 3,
    }
}
fn decode_reason(reason: i64) -> Result<RetirementReason, SqliteStateError> {
    match reason {
        0 => Ok(RetirementReason::HolderRemoved),
        1 => Ok(RetirementReason::NoAcceptingEdge),
        2 => Ok(RetirementReason::RouteRemoved),
        3 => Ok(RetirementReason::Explicit),
        _ => Err(SqliteStateError::invalid("invalid retirement reason")),
    }
}

fn read_revision(connection: &Connection) -> Result<u64, SqliteStateError> {
    let revision = connection.query_row(
        "SELECT state_revision FROM session_meta WHERE singleton = 1",
        [],
        |row| row.get::<_, i64>(0),
    )?;
    decode_u64(revision, "state revision")
}

fn read_current_kernel(
    connection: &Connection,
    binding: &Kernel,
) -> Result<Arc<Kernel>, SqliteStateError> {
    let graph = connection.query_row(
        "SELECT current_graph FROM session_meta WHERE singleton = 1",
        [],
        |row| row.get::<_, Vec<u8>>(0),
    )?;
    let data: FragmentData = serde_json::from_slice(&graph)
        .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
    let fragment = GraphFragment::try_from(data)
        .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
    let kernel = Arc::new(
        binding
            .admit_fragment(&fragment)
            .map_err(|error| SqliteStateError::invalid(error.to_string()))?,
    );
    validate_definition_binding(connection, &kernel)?;
    Ok(kernel)
}

fn write_current_definition(
    connection: &Connection,
    kernel: &Kernel,
    state: &State,
) -> Result<(), SqliteStateError> {
    if state.definition_id() != kernel.id()
        || state.definition_fingerprint() != kernel.fingerprint()
    {
        return Err(SqliteStateError::invalid("graph and state disagree"));
    }
    connection.execute(
        "UPDATE session_meta SET definition_fingerprint = ?1, current_graph = ?2,
             used_node_ids = ?3, used_edge_ids = ?4, state_revision = ?5, definition_changes = ?6 WHERE singleton = 1",
        params![
            kernel.fingerprint().as_bytes().as_slice(),
            encode_fragment(kernel)?,
            encode_ids(state.used_node_ids())?,
            encode_ids(state.used_edge_ids())?,
            encode_u64(state.revision())?,
            encode_u64(state.definition_changes())?,
        ],
    )?;
    Ok(())
}

fn rebuild_readiness(connection: &Connection, kernel: &Kernel) -> Result<(), SqliteStateError> {
    connection.execute("DELETE FROM pending_heads", [])?;
    connection.execute("DELETE FROM ready_triggers", [])?;
    connection.execute(
        "INSERT INTO pending_heads (
            holder_node, authority, edge_id, producer_activation, output_id
         )
         SELECT o.delivery_receiver, o.authority, o.delivery_edge,
                o.producer_activation, o.output_id
         FROM package_outputs o
         WHERE o.status = 0 AND o.delivery_edge IS NOT NULL AND NOT EXISTS (
             SELECT 1 FROM package_outputs earlier
             WHERE earlier.status = 0 AND earlier.delivery_edge IS NOT NULL
               AND earlier.delivery_receiver = o.delivery_receiver
               AND earlier.authority = o.authority
               AND earlier.delivery_edge = o.delivery_edge
               AND (earlier.producer_activation, earlier.output_id)
                   < (o.producer_activation, o.output_id))",
        [],
    )?;
    for ((node, authority), first) in expected_ready_triggers(connection, kernel)? {
        connection.execute(
            "INSERT INTO ready_triggers(holder_node, authority, first_package) VALUES (?1, ?2, ?3)",
            params![node, authority, first],
        )?;
    }
    Ok(())
}

fn validate_definition_binding(
    connection: &Connection,
    kernel: &Kernel,
) -> Result<(), SqliteStateError> {
    let stored = connection
        .query_row(
            "SELECT definition_id, definition_fingerprint
             FROM session_meta WHERE singleton = 1",
            [],
            |row| Ok((row.get::<_, String>(0)?, row.get::<_, Vec<u8>>(1)?)),
        )
        .optional()?
        .ok_or(SqliteStateError::NotInitialized)?;
    let definition_id = DefinitionId::new(stored.0)
        .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
    let fingerprint = decode_fingerprint(stored.1)?;
    if &definition_id != kernel.id() || &fingerprint != kernel.fingerprint() {
        return Err(SqliteStateError::invalid(format!(
            "definition {definition_id}@{fingerprint} does not match kernel {}@{}",
            kernel.id(),
            kernel.fingerprint()
        )));
    }
    Ok(())
}

fn open_locked_connection(path: &Path, create: bool) -> Result<Connection, SqliteStateError> {
    let flags = if create {
        OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
    } else {
        OpenFlags::SQLITE_OPEN_READ_WRITE
    };
    let connection = Connection::open_with_flags(path, flags)?;
    configure_connection(&connection)?;
    connection.execute_batch("PRAGMA locking_mode = EXCLUSIVE;")?;
    Ok(connection)
}

fn configure_connection(connection: &Connection) -> Result<(), SqliteStateError> {
    connection.execute_batch(
        "PRAGMA foreign_keys = ON;
         PRAGMA busy_timeout = 250;
         PRAGMA cell_size_check = ON;",
    )?;
    Ok(())
}

fn configure_durability(connection: &Connection) -> Result<(), SqliteStateError> {
    // EXTRA also syncs the directory after deleting the rollback journal,
    // making journal removal durable when the storage honors sync requests.
    connection.execute_batch(
        "PRAGMA journal_mode = DELETE;
         PRAGMA synchronous = EXTRA;",
    )?;
    Ok(())
}

fn create_schema(connection: &Connection) -> Result<(), SqliteStateError> {
    connection.execute_batch(
        "CREATE TABLE session_meta (
            singleton INTEGER PRIMARY KEY CHECK(singleton = 1),
            definition_id TEXT NOT NULL,
            definition_fingerprint BLOB NOT NULL CHECK(length(definition_fingerprint) = 32),
            current_graph BLOB NOT NULL,
            used_node_ids BLOB NOT NULL,
            used_edge_ids BLOB NOT NULL,
            status INTEGER NOT NULL CHECK(status IN (0, 1, 2)),
            state_revision INTEGER NOT NULL CHECK(state_revision >= 0),
            definition_changes INTEGER NOT NULL DEFAULT 0 CHECK(definition_changes >= 0),
            fault TEXT,
            CHECK((status = 2 AND fault IS NOT NULL) OR (status IN (0, 1) AND fault IS NULL))
         );
         CREATE TABLE activations (
            activation_id BLOB PRIMARY KEY CHECK(length(activation_id) = 16),
            trigger_kind INTEGER NOT NULL CHECK(trigger_kind IN (0, 1)),
            execution_node TEXT NOT NULL,
            root_node TEXT,
            root_authority BLOB,
            result_digest BLOB NOT NULL CHECK(length(result_digest) = 32),
            CHECK((trigger_kind = 0 AND root_node IS NOT NULL AND root_authority IS NOT NULL)
               OR (trigger_kind = 1 AND root_node IS NULL AND root_authority IS NULL))
         );
         CREATE TABLE package_outputs (
            producer_activation BLOB NOT NULL CHECK(length(producer_activation) = 16),
            output_id BLOB NOT NULL CHECK(length(output_id) = 16),
            birth_edge_id TEXT,
            object_type TEXT NOT NULL,
            authority BLOB NOT NULL,
            content_digest BLOB NOT NULL CHECK(length(content_digest) = 32),
            producer_node TEXT NOT NULL,
            delivery_edge TEXT,
            delivery_receiver TEXT,
            status INTEGER NOT NULL CHECK(status IN (0, 1, 2)),
            consumer_activation BLOB
                CHECK(consumer_activation IS NULL OR length(consumer_activation) = 16),
            retire_reason INTEGER CHECK(retire_reason IS NULL OR retire_reason IN (0, 1, 2, 3)),
            retire_revision INTEGER CHECK(retire_revision IS NULL OR retire_revision >= 1),
            retire_evidence BLOB CHECK(retire_evidence IS NULL OR length(retire_evidence) = 16),
            PRIMARY KEY(producer_activation, output_id),
            FOREIGN KEY(producer_activation) REFERENCES activations(activation_id),
            FOREIGN KEY(consumer_activation) REFERENCES activations(activation_id),
            FOREIGN KEY(retire_evidence) REFERENCES activations(activation_id),
            CHECK((delivery_edge IS NULL) = (delivery_receiver IS NULL)),
            CHECK(birth_edge_id IS NULL OR birth_edge_id = delivery_edge),
            CHECK((status = 1) = (consumer_activation IS NOT NULL)),
            CHECK(status != 1 OR delivery_edge IS NOT NULL),
            CHECK((status = 2) = (retire_reason IS NOT NULL)),
            CHECK((status = 2) = (retire_revision IS NOT NULL)),
            CHECK(retire_evidence IS NULL OR retire_reason = 3),
            CHECK(retire_reason IS NOT 1 OR delivery_edge IS NULL),
            CHECK(retire_reason IS NOT 2 OR delivery_edge IS NOT NULL)
         );
         CREATE TABLE pending_heads (
            holder_node TEXT NOT NULL,
            authority BLOB NOT NULL,
            edge_id TEXT NOT NULL,
            producer_activation BLOB NOT NULL CHECK(length(producer_activation) = 16),
            output_id BLOB NOT NULL CHECK(length(output_id) = 16),
            PRIMARY KEY(holder_node, authority, edge_id),
            UNIQUE(producer_activation, output_id),
            FOREIGN KEY(producer_activation, output_id)
                REFERENCES package_outputs(producer_activation, output_id)
         );
         CREATE TABLE ready_triggers (
            holder_node TEXT NOT NULL,
            authority BLOB NOT NULL,
            first_package BLOB NOT NULL CHECK(length(first_package) = 32),
            PRIMARY KEY(holder_node, authority)
         );",
    )?;
    connection.execute_batch(RUNTIME_INDEXES)?;
    connection.execute_batch(PACKAGE_HISTORY_INDEX)?;
    connection.execute_batch(ACTIVATION_CONTENT_SCHEMA)?;
    context::create_schema(connection)?;
    connection.pragma_update(None, "user_version", SCHEMA_VERSION)?;
    Ok(())
}

fn fresh_activation_id(transaction: &Transaction<'_>) -> Result<ActivationId, SqliteStateError> {
    loop {
        let candidate = ActivationId::fresh();
        let blob = activation_blob(candidate);
        let exists = transaction.query_row(
            "SELECT EXISTS(SELECT 1 FROM activations WHERE activation_id = ?1)",
            [blob.as_slice()],
            |row| row.get::<_, bool>(0),
        )?;
        if !exists {
            return Ok(candidate);
        }
    }
}

/// The payloads a transition publishes: the activation result and one payload
/// per emitted output, checked against the accepted digests.
fn object_batch(
    transition: &Transition,
    emitted_payloads: &[Payload],
) -> Result<BTreeMap<ContentDigest, Payload>, SqliteStateError> {
    let TransitionKind::Activation {
        activation,
        outputs,
        ..
    } = transition.kind()
    else {
        return Err(SqliteStateError::invalid(
            "activation transition does not insert an activation",
        ));
    };
    if emitted_payloads.len() != outputs.len() {
        return Err(SqliteStateError::invalid(
            "accepted output and proposal payload counts differ",
        ));
    }
    let result_digest = ContentDigest::compute(activation.result());
    let mut objects = BTreeMap::from([(result_digest, activation.result().clone())]);
    for ((_, record), payload) in outputs.iter().zip(emitted_payloads) {
        let computed = ContentDigest::compute(payload);
        if computed != record.content_digest() {
            return Err(SqliteStateError::invalid(
                "accepted output digest does not match proposal payload",
            ));
        }
        if let Some(existing) = objects.insert(computed, payload.clone())
            && existing.as_ref() != payload.as_ref()
        {
            return Err(SqliteStateError::invalid(format!(
                "object {computed} names different bytes"
            )));
        }
    }
    Ok(objects)
}

fn insert_activation_record(
    transaction: &Transaction<'_>,
    activation_id: ActivationId,
    activation: &Activation,
) -> Result<(), SqliteStateError> {
    let activation_id = activation_blob(activation_id);
    let (trigger_kind, root_node, root_authority) = match activation.trigger() {
        Trigger::Orig { node_id, authority } => (
            0_i64,
            Some(node_id.as_ref()),
            Some(encode_authority(authority)?),
        ),
        Trigger::Pkgs { .. } => (1_i64, None, None),
    };
    let result_digest = ContentDigest::compute(activation.result());
    transaction.execute(
        "INSERT INTO activations (
            activation_id, trigger_kind, root_node, root_authority, result_digest, execution_node
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
        params![
            activation_id.as_slice(),
            trigger_kind,
            root_node,
            root_authority,
            result_digest.as_bytes().as_slice(),
            activation.node_id(),
        ],
    )?;
    Ok(())
}

fn insert_package_record(
    transaction: &Transaction<'_>,
    package_id: PackageId,
    record: &PackageRecord,
    birth_edge: Option<&str>,
) -> Result<(), SqliteStateError> {
    let producer = activation_blob(package_id.producer());
    let output_id = u128_blob(package_id.output());
    let authority = encode_authority(record.authority())?;
    let (status, consumer, reason, retire_revision, evidence) = match record.status() {
        PackageStatus::Live => (0_i64, None, None, None, None),
        PackageStatus::Consumed(consumer) => {
            (1_i64, Some(activation_blob(*consumer)), None, None, None)
        }
        PackageStatus::Retired(retirement) => (
            2_i64,
            None,
            Some(encode_reason(retirement.reason())),
            Some(encode_u64(retirement.revision())?),
            retirement.evidence().map(activation_blob),
        ),
    };
    transaction.execute(
        "INSERT INTO package_outputs (
            producer_activation, output_id, birth_edge_id, object_type, authority,
            content_digest, producer_node, delivery_edge, delivery_receiver, status,
            consumer_activation, retire_reason, retire_revision, retire_evidence
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14)",
        params![
            producer.as_slice(),
            output_id.as_slice(),
            birth_edge,
            record.object_type(),
            authority.as_slice(),
            record.content_digest().as_bytes().as_slice(),
            record.producer_node(),
            record.delivery().map(Delivery::edge_id),
            record.delivery().map(Delivery::receiver),
            status,
            consumer.as_ref().map(<[u8; 16]>::as_slice),
            reason,
            retire_revision,
            evidence.as_ref().map(<[u8; 16]>::as_slice)
        ],
    )?;
    Ok(())
}

fn advance_pending_head(
    transaction: &Transaction<'_>,
    node_id: &str,
    authority: &[u8],
    edge_id: &str,
    consumed: PackageId,
) -> Result<bool, SqliteStateError> {
    let producer = activation_blob(consumed.producer());
    let output = u128_blob(consumed.output());
    let changed = transaction.execute(
        "DELETE FROM pending_heads
         WHERE holder_node = ?1 AND authority = ?2 AND edge_id = ?3
           AND producer_activation = ?4 AND output_id = ?5",
        params![
            node_id,
            authority,
            edge_id,
            producer.as_slice(),
            output.as_slice()
        ],
    )?;
    if changed == 0 {
        return Ok(false);
    }
    transaction.execute(
        "INSERT INTO pending_heads (
            holder_node, authority, edge_id, producer_activation, output_id
         )
         SELECT delivery_receiver, authority, delivery_edge, producer_activation, output_id
         FROM package_outputs INDEXED BY package_outputs_group_pending
         WHERE status = 0 AND delivery_edge IS NOT NULL
           AND delivery_receiver = ?1 AND authority = ?2 AND delivery_edge = ?3
         ORDER BY producer_activation, output_id
         LIMIT 1",
        params![node_id, authority, edge_id],
    )?;
    Ok(true)
}

fn insert_pending_head(
    transaction: &Transaction<'_>,
    node_id: &str,
    authority: &[u8],
    edge_id: &str,
    package_id: PackageId,
) -> Result<bool, SqliteStateError> {
    let producer = activation_blob(package_id.producer());
    let output = u128_blob(package_id.output());
    let changed = transaction.execute(
        "INSERT INTO pending_heads (
            holder_node, authority, edge_id, producer_activation, output_id
         ) VALUES (?1, ?2, ?3, ?4, ?5)
         ON CONFLICT(holder_node, authority, edge_id) DO UPDATE SET
            producer_activation = excluded.producer_activation,
            output_id = excluded.output_id
         WHERE (excluded.producer_activation, excluded.output_id)
             < (pending_heads.producer_activation, pending_heads.output_id)",
        params![
            node_id,
            authority,
            edge_id,
            producer.as_slice(),
            output.as_slice()
        ],
    )?;
    Ok(changed == 1)
}

fn refresh_ready_trigger(
    connection: &Connection,
    kernel: &Kernel,
    node_id: &str,
    authority: &[u8],
) -> Result<(), SqliteStateError> {
    let definition = kernel.node_definition(node_id).ok_or_else(|| {
        SqliteStateError::invalid(format!("pending package targets unknown node {node_id}"))
    })?;
    if definition.ingress_mode() != IngressMode::All {
        return Ok(());
    }
    connection.execute(
        "DELETE FROM ready_triggers WHERE holder_node = ?1 AND authority = ?2",
        params![node_id, authority],
    )?;
    if let Some(package_id) = ready_package(connection, kernel, node_id, authority)? {
        connection.execute(
            "INSERT INTO ready_triggers (holder_node, authority, first_package)
             VALUES (?1, ?2, ?3)",
            params![node_id, authority, package_key(package_id)],
        )?;
    }
    Ok(())
}

fn read_authority_heads(
    connection: &Connection,
    node_id: &str,
    authority: &[u8],
) -> Result<BTreeMap<Arc<str>, PackageId>, SqliteStateError> {
    let mut statement = connection.prepare(
        "SELECT edge_id, producer_activation, output_id
         FROM pending_heads
         WHERE holder_node = ?1 AND authority = ?2
         ORDER BY edge_id",
    )?;
    let mut rows = statement.query(params![node_id, authority])?;
    let mut heads = BTreeMap::new();
    while let Some(row) = rows.next()? {
        heads.insert(
            Arc::from(row.get::<_, String>(0)?),
            PackageId::from_parts(
                decode_activation(row.get(1)?)?,
                decode_u128(row.get(2)?, "package output identity")?,
            ),
        );
    }
    Ok(heads)
}

fn package_key(package_id: PackageId) -> Vec<u8> {
    // Authority bundles are disjoint, so their least IDs cannot tie and alone
    // determine the lexicographic order of the sorted package-ID vectors.
    let mut key = Vec::with_capacity(32);
    key.extend_from_slice(&activation_blob(package_id.producer()));
    key.extend_from_slice(&u128_blob(package_id.output()));
    key
}

fn ready_package(
    connection: &Connection,
    kernel: &Kernel,
    node_id: &str,
    authority: &[u8],
) -> Result<Option<PackageId>, SqliteStateError> {
    let incoming_edges = kernel
        .graph()
        .incoming_edge_ids(node_id)
        .expect("admitted node has an incoming-edge index");
    if incoming_edges.is_empty() {
        return Ok(None);
    }
    let heads = read_authority_heads(connection, node_id, authority)?;
    let current = incoming_edges
        .iter()
        .map(|edge| heads.get(edge).copied())
        .collect::<Option<Vec<_>>>();
    Ok(current.and_then(|packages| packages.into_iter().min()))
}

fn expected_ready_triggers(
    connection: &Connection,
    kernel: &Kernel,
) -> Result<ReadyTriggerMap, SqliteStateError> {
    let groups = {
        let mut statement = connection.prepare(
            "SELECT DISTINCT holder_node, authority
             FROM pending_heads
             ORDER BY holder_node, authority",
        )?;
        let rows = statement.query_map([], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, Vec<u8>>(1)?))
        })?;
        rows.collect::<Result<Vec<_>, _>>()?
    };
    let mut ready = BTreeMap::new();
    for (node_id, authority) in groups {
        let definition = kernel.node_definition(&node_id).ok_or_else(|| {
            SqliteStateError::invalid(format!("pending package targets unknown node {node_id}"))
        })?;
        if definition.ingress_mode() != IngressMode::All {
            continue;
        }
        if let Some(package_id) = ready_package(connection, kernel, &node_id, &authority)? {
            ready.insert((node_id, authority), package_key(package_id));
        }
    }
    Ok(ready)
}

fn query_all_trigger(
    connection: &Connection,
    node_id: &str,
    incoming_edges: &BTreeSet<Arc<str>>,
) -> Result<Vec<(PackageId, PackageRecord)>, SqliteStateError> {
    if incoming_edges.is_empty() {
        return Ok(Vec::new());
    }
    let authority = connection
        .query_row(
            "SELECT authority
             FROM ready_triggers INDEXED BY ready_triggers_by_package
             WHERE holder_node = ?1
             ORDER BY first_package
             LIMIT 1",
            [node_id],
            |row| row.get::<_, Vec<u8>>(0),
        )
        .optional()?;
    let Some(authority) = authority else {
        return Ok(Vec::new());
    };
    let sql = format!(
        "SELECT {} FROM pending_heads h JOIN package_outputs o
           ON o.producer_activation = h.producer_activation AND o.output_id = h.output_id
          AND o.delivery_receiver = h.holder_node AND o.authority = h.authority
          AND o.delivery_edge = h.edge_id
         WHERE h.holder_node = ?1 AND h.authority = ?2 AND h.edge_id = ?3 AND o.status = 0",
        qualified_record_columns("o")
    );
    let mut packages = Vec::with_capacity(incoming_edges.len());
    for edge in incoming_edges {
        let mut selected = query_records(
            connection,
            &sql,
            params![node_id, &authority, edge.as_ref()],
        )?;
        if selected.len() != 1 {
            return Err(SqliteStateError::invalid(
                "ready trigger has an incomplete current-edge bundle",
            ));
        }
        packages.append(&mut selected);
    }
    packages.sort_unstable_by_key(|(id, _)| *id);
    Ok(packages)
}

fn encode_authority(authority: &Authority) -> Result<Vec<u8>, SqliteStateError> {
    let tags = authority.tags().collect::<Vec<_>>();
    let mut encoded = Vec::new();
    encoded.extend_from_slice(
        &u32::try_from(tags.len())
            .map_err(|_| SqliteStateError::invalid("authority has too many tags"))?
            .to_be_bytes(),
    );
    for tag in tags {
        let bytes = tag.id().as_bytes();
        encoded.extend_from_slice(
            &u32::try_from(bytes.len())
                .map_err(|_| SqliteStateError::invalid("authority tag is too long"))?
                .to_be_bytes(),
        );
        encoded.extend_from_slice(bytes);
    }
    Ok(encoded)
}

fn decode_authority(encoded: &[u8]) -> Result<Authority, SqliteStateError> {
    let mut offset = 0_usize;
    let count = read_u32(encoded, &mut offset)?;
    let mut tags = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let length = read_u32(encoded, &mut offset)? as usize;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| SqliteStateError::invalid("authority encoding overflows"))?;
        let bytes = encoded
            .get(offset..end)
            .ok_or_else(|| SqliteStateError::invalid("truncated authority encoding"))?;
        let id = std::str::from_utf8(bytes)
            .map_err(|_| SqliteStateError::invalid("authority tag is not UTF-8"))?;
        tags.push(
            AuthorityTag::new(id).map_err(|error| SqliteStateError::invalid(error.to_string()))?,
        );
        offset = end;
    }
    if offset != encoded.len() {
        return Err(SqliteStateError::invalid(
            "authority encoding has trailing bytes",
        ));
    }
    Ok(Authority::new(tags))
}

fn read_u32(encoded: &[u8], offset: &mut usize) -> Result<u32, SqliteStateError> {
    let end = offset
        .checked_add(4)
        .ok_or_else(|| SqliteStateError::invalid("authority encoding overflows"))?;
    let bytes: [u8; 4] = encoded
        .get(*offset..end)
        .ok_or_else(|| SqliteStateError::invalid("truncated authority encoding"))?
        .try_into()
        .map_err(|_| SqliteStateError::invalid("invalid authority integer"))?;
    *offset = end;
    Ok(u32::from_be_bytes(bytes))
}

fn activation_blob(id: ActivationId) -> [u8; 16] {
    id.as_u128().to_be_bytes()
}

const fn u128_blob(value: u128) -> [u8; 16] {
    value.to_be_bytes()
}

fn decode_activation(bytes: Vec<u8>) -> Result<ActivationId, SqliteStateError> {
    decode_u128(bytes, "activation identity").map(ActivationId::from_u128)
}

fn decode_u128(bytes: Vec<u8>, kind: &str) -> Result<u128, SqliteStateError> {
    let bytes: [u8; 16] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid(format!("invalid {kind} encoding")))?;
    Ok(u128::from_be_bytes(bytes))
}

fn decode_digest(bytes: Vec<u8>) -> Result<ContentDigest, SqliteStateError> {
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid("invalid content digest encoding"))?;
    Ok(ContentDigest::from_bytes(bytes))
}

fn decode_fingerprint(bytes: Vec<u8>) -> Result<DefinitionFingerprint, SqliteStateError> {
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid("invalid definition fingerprint encoding"))?;
    Ok(DefinitionFingerprint::from_bytes(bytes))
}

fn decode_u64(value: i64, kind: &str) -> Result<u64, SqliteStateError> {
    u64::try_from(value).map_err(|_| SqliteStateError::invalid(format!("negative {kind}")))
}

fn encode_u64(value: u64) -> Result<i64, SqliteStateError> {
    i64::try_from(value)
        .map_err(|_| SqliteStateError::invalid("value exceeds SQLite integer range"))
}

fn decode_status(value: i64) -> Result<SessionStatus, SqliteStateError> {
    match value {
        0 => Ok(SessionStatus::Open),
        1 => Ok(SessionStatus::Closed),
        2 => Ok(SessionStatus::Faulted),
        _ => Err(SqliteStateError::invalid("unknown session status")),
    }
}
