//! Durable SQLite-backed logical state ownership.
//!
//! A non-null package phase records live frontier membership. Clearing it retires
//! a package without changing its output or delivery facts; consumption additionally
//! records a consumer. The stored holder remains available for historical views.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use rusqlite::{
    Connection, OpenFlags, OptionalExtension, Transaction, TransactionBehavior, params,
};
use thiserror::Error;

use super::object_store::{ObjectStore, ObjectStoreError};
use super::session::{FrontierCounts, PackageHistory, SessionStatus};
use crate::content::ContentId;
use crate::kernel::{
    AdmissionDelta, AdmissionView, Checkpoint, PackageObservation, PendingInput,
    TransferObservation,
};
use crate::{
    Activation, ActivationId, ActivationProposal, Authority, AuthorityTag, ContentDigest,
    DefinitionFingerprint, DefinitionId, Delivery, IngressMode, Kernel, Output, Package, PackageId,
    Payload, Phase, Position, PreparedRewrite, Reject, RetirementReason, RewriteError,
    RewriteFragment, RewriteGrammar, RewriteRequest, State, TransferError, Trigger,
};

pub(crate) mod context;

const SCHEMA_VERSION: i64 = 8;

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

const RUNTIME_INDEXES: &str = "CREATE INDEX package_outputs_pending
         ON package_outputs(producer_activation, output_id)
         WHERE phase = 1;
     CREATE INDEX package_outputs_target_pending
         ON package_outputs(holder_node, producer_activation, output_id)
         WHERE phase = 1;
     CREATE INDEX package_outputs_group_pending
         ON package_outputs(holder_node, authority, edge_id, producer_activation, output_id)
         WHERE phase = 1;
     CREATE INDEX package_outputs_outbound
         ON package_outputs(producer_activation, output_id) WHERE phase = 0;
     CREATE INDEX package_outputs_holder_outbound
         ON package_outputs(holder_node, producer_activation, output_id) WHERE phase = 0;
     CREATE INDEX pending_heads_edge
         ON pending_heads(holder_node, edge_id, producer_activation, output_id);
     CREATE INDEX ready_triggers_by_package
         ON ready_triggers(holder_node, first_package);";

type ReadyTriggerMap = BTreeMap<(String, Vec<u8>), Vec<u8>>;

#[derive(Debug, Error)]
pub(super) enum SqliteStateError {
    #[error("SQLite operation failed: {0}")]
    Database(#[from] rusqlite::Error),
    #[error("persistent session already exists")]
    AlreadyExists,
    #[error("persistent session has not been initialized")]
    NotInitialized,
    #[error("unsupported persistent schema version {0}")]
    SchemaVersion(i64),
    #[error("SQLite session state is invalid: {0}")]
    Invalid(Arc<str>),
    #[error(transparent)]
    Object(#[from] ObjectStoreError),
    #[error("invalid proposed content dependency: {0}")]
    Content(ObjectStoreError),
}

impl SqliteStateError {
    fn invalid(message: impl Into<Arc<str>>) -> Self {
        Self::Invalid(message.into())
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

pub(super) struct SqliteCommit {
    pub(super) activation_id: ActivationId,
    pub(super) revision: u64,
}

pub(super) struct PendingRead {
    pub(super) revision: u64,
    pub(super) packages: Vec<(PackageId, Package)>,
}

pub(super) struct SqlitePreparedRewrite {
    prepared: PreparedRewrite,
}

impl SqlitePreparedRewrite {
    pub(super) fn retirements(&self) -> &BTreeMap<PackageId, RetirementReason> {
        self.prepared.retirements()
    }
    pub(super) fn next_kernel(&self) -> &Arc<Kernel> {
        self.prepared.next_kernel()
    }
    pub(super) fn revision(&self) -> u64 {
        self.prepared.base_revision()
    }
}

pub(super) struct SqliteRewriteCommit {
    pub(super) current_kernel: Arc<Kernel>,
    pub(super) revision: u64,
}

pub(super) struct SqliteTransferCommit {
    pub(super) delivery: Delivery,
    pub(super) revision: u64,
}

enum SqlitePackageFact {
    Pending {
        edge_id: Arc<str>,
        node_id: Arc<str>,
        authority: Authority,
    },
    Consumed(ActivationId),
    Retired,
    Outbound,
}

struct SqliteAdmissionView {
    packages: BTreeMap<PackageId, SqlitePackageFact>,
}

struct SqliteTransferFact {
    package: Package,
    position: Option<Position>,
    consumed: bool,
}

impl AdmissionView for SqliteAdmissionView {
    fn package(&self, package_id: PackageId) -> PackageObservation<'_> {
        match self.packages.get(&package_id) {
            Some(SqlitePackageFact::Pending {
                edge_id,
                node_id,
                authority,
            }) => PackageObservation::Pending(PendingInput {
                edge_id,
                node_id,
                authority,
            }),
            Some(SqlitePackageFact::Consumed(consumer)) => PackageObservation::Consumed(*consumer),
            Some(SqlitePackageFact::Retired) => PackageObservation::Retired,
            Some(SqlitePackageFact::Outbound) => PackageObservation::Outbound,
            None => PackageObservation::Missing,
        }
    }
}

impl SqliteSession {
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
        Self::read_opened(opened.session.connection, kernel)
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
                encode_json(&RewriteFragment::from_kernel(kernel))?,
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
            insert_activation_record(
                &transaction,
                *activation_id,
                activation,
                ContentDigest::compute(activation.result()),
            )?;
        }
        for activation in state.activations().values() {
            for (package_id, output) in activation.package_outputs() {
                let package = state.package(*package_id).ok_or_else(|| {
                    SqliteStateError::invalid("restored output has no package projection")
                })?;
                insert_package_output(
                    &transaction,
                    *package_id,
                    output,
                    package.node_id(),
                    state.package_consumer(*package_id),
                    state.position(*package_id).map(Position::phase),
                    state.deliveries().get(package_id),
                )?;
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
        let connection = open_locked_connection(path, false)?;
        let version =
            connection.query_row("PRAGMA user_version", [], |row| row.get::<_, i64>(0))?;
        match version {
            0 => return Err(SqliteStateError::NotInitialized),
            SCHEMA_VERSION => {}
            version => return Err(SqliteStateError::SchemaVersion(version)),
        }
        let _ = read_current_kernel(&connection, kernel)?;
        configure_durability(&connection)?;
        connection.execute_batch("BEGIN EXCLUSIVE; UPDATE context_invocations SET status='interrupted',detail='runtime restarted before completion' WHERE status='open'; COMMIT;")?;
        Self::read_opened(connection, kernel)
    }

    pub(super) fn verify_opened(
        opened: OpenedSqliteSession,
        kernel: &Kernel,
        objects: &ObjectStore,
    ) -> Result<OpenedSqliteSession, SqliteStateError> {
        validate_definition_binding(&opened.session.connection, kernel)?;
        let state = opened.session.snapshot(&opened.current_kernel, objects)?;
        let parts = state.to_parts().map_err(|_| SqliteStateError::invalid(
            "historical reachability verification is unavailable after rewrites or explicit transfers"))?;
        let evidence = state
            .packages()
            .values()
            .map(|package| {
                let digest = package.content_digest();
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
        opened
            .session
            .validate_trigger_projection(&opened.current_kernel)?;
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

    pub(super) fn submit_with_content(
        &mut self,
        kernel: &Kernel,
        objects: &mut ObjectStore,
        proposal: ActivationProposal,
        contents: &[ContentId],
    ) -> Result<Result<SqliteCommit, Reject>, SqliteStateError> {
        self.submit_linked(kernel, objects, proposal, contents, None)
    }

    pub(crate) fn submit_with_invocation(
        &mut self,
        kernel: &Kernel,
        objects: &mut ObjectStore,
        proposal: ActivationProposal,
        contents: &[ContentId],
        id: crate::context::InvocationId,
        digest: ContentDigest,
    ) -> Result<Result<SqliteCommit, Reject>, SqliteStateError> {
        self.submit_linked(kernel, objects, proposal, contents, Some((id, digest)))
    }

    fn submit_linked(
        &mut self,
        kernel: &Kernel,
        objects: &mut ObjectStore,
        proposal: ActivationProposal,
        contents: &[ContentId],
        invocation: Option<(crate::context::InvocationId, ContentDigest)>,
    ) -> Result<Result<SqliteCommit, Reject>, SqliteStateError> {
        let package_ids = proposal.package_ids().cloned();
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
        let activation_id = fresh_activation_id(&transaction)?;
        let view = read_admission_view(&transaction, package_ids.as_ref())?;
        let delta = match kernel.evaluate(&view, activation_id, proposal) {
            Ok(delta) => delta,
            Err(reject) => {
                if let Some((id, digest)) = invocation {
                    transaction.execute("UPDATE context_invocations SET status='rejected',detail=?2,submission_digest=?3 WHERE invocation_id=?1 AND status='open'",params![id.to_string(),format!("{reject:?}"),digest.as_bytes().as_slice()])?;
                    transaction.commit()?;
                }
                return Ok(Err(reject));
            }
        };
        // Caller-supplied references are checked before publication. A foreign
        // or malformed reference rejects this operation without faulting an
        // otherwise healthy session.
        let _content_protection = objects
            .protect_content(contents)
            .map_err(SqliteStateError::Content)?;
        let (result_digest, batch) = object_batch(&delta, &emitted_payloads)?;
        objects.put_all(&batch)?;
        // The synchronous object-store boundary is also the durability fence
        // for imported files and collection members. No cancellation point may
        // separate protecting their bytes from publishing the activation.
        objects.retain_content(contents)?;
        insert_delta(&transaction, kernel, &view, &delta, result_digest)?;
        for (ordinal, content) in contents.iter().enumerate() {
            let ordinal = i64::try_from(ordinal)
                .map_err(|_| SqliteStateError::invalid("too many activation content references"))?;
            transaction.execute(
                "INSERT INTO activation_content (activation_id, ordinal, content) VALUES (?1, ?2, ?3)",
                params![activation_blob(delta.id).as_slice(), ordinal, encode_json(content)?],
            )?;
        }
        let revision = advance_revision(&transaction)?;
        if let Some((id, digest)) = invocation {
            let changed=transaction.execute("UPDATE context_invocations SET status='accepted',activation_id=?2,submission_digest=?3 WHERE invocation_id=?1 AND status='open'",params![id.to_string(),activation_blob(delta.id).as_slice(),digest.as_bytes().as_slice()])?;
            if changed != 1 {
                return Err(SqliteStateError::invalid("invocation is no longer active"));
            }
        }
        transaction.commit()?;
        Ok(Ok(SqliteCommit {
            activation_id: delta.id,
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
        transaction.execute("UPDATE context_invocations SET status='interrupted',detail='session closed' WHERE status='open'", [])?;
        transaction.execute(
            "UPDATE session_meta SET status = 1 WHERE singleton = 1 AND status = 0",
            [],
        )?;
        transaction.commit()?;
        Ok(())
    }

    pub(super) fn fault(&mut self, fault: &str) -> Result<(), SqliteStateError> {
        let transaction = self.connection.transaction()?;
        transaction.execute("UPDATE context_invocations SET status='interrupted',detail='session faulted' WHERE status='open'", [])?;
        transaction.execute(
            "UPDATE session_meta SET status = 2, fault = ?1 WHERE singleton = 1",
            [fault],
        )?;
        transaction.commit()?;
        Ok(())
    }

    pub(super) fn pending(
        &self,
        kernel: &Kernel,
        node_id: Option<&str>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingRead, SqliteStateError> {
        self.frontier_page(kernel, Phase::In, node_id, after, limit)
    }

    pub(super) fn frontier_counts(
        &self,
    ) -> Result<BTreeMap<Arc<str>, FrontierCounts>, SqliteStateError> {
        let mut counts = BTreeMap::<Arc<str>, FrontierCounts>::new();
        // Partial indexes exclude consumed/retired history and cover each count.
        for (phase, index) in [
            (Phase::In, "package_outputs_target_pending"),
            (Phase::Out, "package_outputs_holder_outbound"),
        ] {
            let sql = format!(
                "SELECT holder_node, COUNT(*) FROM package_outputs INDEXED BY {index} WHERE phase = {} GROUP BY holder_node",
                encode_phase(phase)
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

    pub(super) fn outbound(
        &self,
        kernel: &Kernel,
        node_id: Option<&str>,
        after: Option<PackageId>,
        limit: usize,
    ) -> Result<PendingRead, SqliteStateError> {
        self.frontier_page(kernel, Phase::Out, node_id, after, limit)
    }

    fn frontier_page(
        &self,
        kernel: &Kernel,
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
        let index = match (phase, node_id.is_some()) {
            (Phase::In, false) => "package_outputs_pending",
            (Phase::In, true) => "package_outputs_target_pending",
            (Phase::Out, false) => "package_outputs_outbound",
            (Phase::Out, true) => "package_outputs_holder_outbound",
        };
        let mut sql = format!("SELECT producer_activation, output_id, edge_id, authority,
            content_digest, holder_node, object_type FROM package_outputs INDEXED BY {index} WHERE phase = {}", encode_phase(phase));
        let mut parameters = Vec::<rusqlite::types::Value>::new();
        if let Some(node) = node_id {
            parameters.push(node.to_owned().into());
            let _ = write!(sql, " AND holder_node = ?{}", parameters.len());
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
        let packages = query_pending(
            &self.connection,
            kernel,
            &sql,
            rusqlite::params_from_iter(parameters),
        )?;
        Ok(PendingRead { revision, packages })
    }

    pub(super) fn next_trigger(
        &self,
        kernel: &Kernel,
        node_id: &str,
        ingress_mode: IngressMode,
        incoming_edges: &BTreeSet<Arc<str>>,
    ) -> Result<PendingRead, SqliteStateError> {
        match ingress_mode {
            IngressMode::Any => self.pending(kernel, Some(node_id), None, 1),
            IngressMode::All => Ok(PendingRead {
                revision: read_revision(&self.connection)?,
                packages: query_all_trigger(&self.connection, kernel, node_id, incoming_edges)?,
            }),
        }
    }

    pub(super) fn next_pending_on_edge(
        &self,
        kernel: &Kernel,
        node_id: &str,
        edge_id: &str,
    ) -> Result<PendingRead, SqliteStateError> {
        let packages = query_pending(
            &self.connection,
            kernel,
            "SELECT o.producer_activation, o.output_id, o.edge_id, o.authority,
                    o.content_digest, o.holder_node, o.object_type
             FROM pending_heads h INDEXED BY pending_heads_edge
             JOIN package_outputs o
               ON o.producer_activation = h.producer_activation
              AND o.output_id = h.output_id
              AND o.phase = 1
              AND o.holder_node = h.holder_node
              AND o.authority = h.authority
              AND o.edge_id = h.edge_id
             WHERE h.holder_node = ?1 AND h.edge_id = ?2
             ORDER BY h.producer_activation, h.output_id
             LIMIT 1",
            params![node_id, edge_id],
        )?;
        Ok(PendingRead {
            revision: read_revision(&self.connection)?,
            packages,
        })
    }

    pub(super) fn package_history(
        &self,
        package_id: PackageId,
    ) -> Result<Option<PackageHistory>, SqliteStateError> {
        let producer = activation_blob(package_id.producer());
        let output = u128_blob(package_id.output());
        let package = {
            let mut statement = self.connection.prepare(
                "SELECT edge_id, object_type, authority, content_digest, holder_node
                 FROM package_outputs
                 WHERE producer_activation = ?1 AND output_id = ?2",
            )?;
            let mut rows = statement.query(params![producer.as_slice(), output.as_slice()])?;
            let Some(row) = rows.next()? else {
                return Ok(None);
            };
            Package {
                edge_id: row.get::<_, Option<String>>(0)?.map(Arc::from),
                object_type: Arc::from(row.get::<_, String>(1)?),
                authority: decode_authority(&row.get::<_, Vec<u8>>(2)?)?,
                content_digest: decode_digest(row.get(3)?)?,
                node_id: Arc::from(row.get::<_, String>(4)?),
            }
        };
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
        Ok(Some(PackageHistory::new(package, inputs)))
    }

    pub(super) fn snapshot(
        &self,
        kernel: &Kernel,
        objects: &ObjectStore,
    ) -> Result<State, SqliteStateError> {
        validate_definition_binding(&self.connection, kernel)?;
        let (revision, used_nodes, used_edges) = self.connection.query_row(
            "SELECT state_revision, used_node_ids, used_edge_ids FROM session_meta WHERE singleton = 1", [],
            |row| Ok((row.get::<_, i64>(0)?, row.get::<_, Vec<u8>>(1)?, row.get::<_, Vec<u8>>(2)?)),
        )?;
        let mut records =
            BTreeMap::<ActivationId, (Trigger, Payload, BTreeMap<PackageId, Output>)>::new();
        let mut cache = BTreeMap::new();
        let mut statement = self.connection.prepare(
            "SELECT activation_id, trigger_kind, root_node, root_authority, result_digest FROM activations ORDER BY activation_id")?;
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
                    trigger,
                    cached_object(objects, &mut cache, decode_digest(row.get(4)?)?)?,
                    BTreeMap::new(),
                ),
            );
        }
        let mut packages = BTreeMap::new();
        let mut positions = BTreeMap::new();
        let mut deliveries = BTreeMap::new();
        let mut statement = self.connection.prepare(
            "SELECT producer_activation, output_id, birth_edge_id, object_type, authority, content_digest,
                    holder_node, consumer_activation, phase, edge_id, source_node
             FROM package_outputs ORDER BY producer_activation, output_id")?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            let producer = decode_activation(row.get(0)?)?;
            let id = PackageId::from_parts(producer, decode_u128(row.get(1)?, "output ID")?);
            let birth_edge = row.get::<_, Option<String>>(2)?;
            let object_type = row.get::<_, String>(3)?;
            let authority = decode_authority(&row.get::<_, Vec<u8>>(4)?)?;
            let digest = decode_digest(row.get(5)?)?;
            let holder = Arc::<str>::from(row.get::<_, String>(6)?);
            let output = match birth_edge {
                Some(edge) => Output::new(edge, object_type.clone(), authority.clone(), digest),
                None => Output::outbound(object_type.clone(), authority.clone(), digest),
            };
            let (_, _, outputs) = records
                .get_mut(&producer)
                .ok_or_else(|| SqliteStateError::invalid("output producer is absent"))?;
            outputs.insert(id, output);
            if let Some(consumer) = row.get::<_, Option<Vec<u8>>>(7)? {
                let consumer = decode_activation(consumer)?;
                let (trigger, _, _) = records
                    .get_mut(&consumer)
                    .ok_or_else(|| SqliteStateError::invalid("output consumer is absent"))?;
                let Trigger::Pkgs { package_ids } = trigger else {
                    return Err(SqliteStateError::invalid(
                        "root activation has package inputs",
                    ));
                };
                package_ids.insert(id);
            }
            if let Some(phase) = row.get::<_, Option<i64>>(8)? {
                positions.insert(id, Position::new(holder.clone(), decode_phase(phase)?));
            }
            let edge_id = row.get::<_, Option<String>>(9)?.map(Arc::<str>::from);
            if let Some(edge) = &edge_id {
                let source = row
                    .get::<_, Option<String>>(10)?
                    .ok_or_else(|| SqliteStateError::invalid("delivery source is absent"))?;
                deliveries.insert(id, Delivery::new(edge.clone(), source, holder.clone()));
            }
            packages.insert(
                id,
                Package {
                    edge_id,
                    object_type: Arc::from(object_type),
                    authority,
                    content_digest: digest,
                    node_id: holder,
                },
            );
        }
        let activations = records
            .into_iter()
            .map(|(id, (trigger, result, outputs))| (id, Activation::new(trigger, result, outputs)))
            .collect();
        kernel
            .restore_checkpoint(Checkpoint {
                activations,
                packages,
                positions,
                deliveries,
                revision: decode_u64(revision, "state revision")?,
                used_node_ids: decode_ids(&used_nodes)?,
                used_edge_ids: decode_ids(&used_edges)?,
            })
            .map_err(SqliteStateError::invalid)
    }

    pub(super) fn prepare_rewrite(
        &self,
        kernel: &Kernel,
        objects: &ObjectStore,
        grammar: &RewriteGrammar,
        request: &RewriteRequest,
    ) -> Result<Result<SqlitePreparedRewrite, RewriteError>, SqliteStateError> {
        let base = self.snapshot(kernel, objects)?;
        match kernel.prepare_rewrite_with_evidence(&base, grammar, request, |_, digest| {
            objects
                .require(digest)
                .map_err(|error| RewriteError::EvidenceUnavailable(Arc::from(error.to_string())))
        }) {
            Ok(prepared) => Ok(Ok(SqlitePreparedRewrite { prepared })),
            Err(error) => Ok(Err(error)),
        }
    }

    pub(super) fn commit_rewrite(
        &mut self,
        kernel: &Kernel,
        plan: SqlitePreparedRewrite,
    ) -> Result<Option<SqliteRewriteCommit>, SqliteStateError> {
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        if read_revision(&transaction)? != plan.revision() {
            return Ok(None);
        }
        validate_definition_binding(&transaction, kernel)?;
        let retired = plan
            .prepared
            .retirements()
            .keys()
            .copied()
            .collect::<Vec<_>>();
        // The session owner and SQL revision bind the exact predecessor; the
        // admitted plan already owns the state from which its successor follows.
        let (next, current_kernel) = plan
            .prepared
            .into_successor()
            .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
        for package_id in retired {
            let producer = activation_blob(package_id.producer());
            let output = u128_blob(package_id.output());
            let changed = transaction.execute(
                "UPDATE package_outputs SET phase = NULL WHERE producer_activation = ?1 AND output_id = ?2 AND phase IS NOT NULL",
                params![producer.as_slice(), output.as_slice()],
            )?;
            if changed != 1 {
                return Err(SqliteStateError::invalid("retired package is not live"));
            }
        }
        write_current_definition(&transaction, &current_kernel, &next)?;
        rebuild_readiness(&transaction, &current_kernel)?;
        transaction.commit()?;
        Ok(Some(SqliteRewriteCommit {
            current_kernel,
            revision: next.revision(),
        }))
    }

    pub(super) fn transfer(
        &mut self,
        kernel: &Kernel,
        objects: &ObjectStore,
        package_id: PackageId,
        edge_id: &str,
    ) -> Result<Result<SqliteTransferCommit, TransferError>, SqliteStateError> {
        // The selected facts, kernel proof, and update share one transaction
        // under the session lock; no full-state snapshot or stale plan is needed.
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        validate_definition_binding(&transaction, kernel)?;
        let fact = read_transfer_fact(&transaction, package_id)?;
        let observation = TransferObservation {
            package: fact.as_ref().map(|fact| &fact.package),
            position: fact.as_ref().and_then(|fact| fact.position.as_ref()),
            delivered: fact
                .as_ref()
                .is_some_and(|fact| fact.package.edge_id().is_some()),
            consumed: fact.as_ref().is_some_and(|fact| fact.consumed),
        };
        let delivery =
            match kernel.evaluate_transfer(package_id, edge_id, observation, |_, digest| {
                objects.require(digest).map_err(|error| {
                    RewriteError::EvidenceUnavailable(Arc::from(error.to_string()))
                })
            }) {
                Ok(delivery) => delivery,
                Err(TransferError::Admission(RewriteError::InvalidState(message))) => {
                    return Err(SqliteStateError::invalid(message));
                }
                Err(error) => return Ok(Err(error)),
            };
        let producer = activation_blob(package_id.producer());
        let output = u128_blob(package_id.output());
        let changed = transaction.execute(
            "UPDATE package_outputs SET phase = 1, holder_node = ?1, edge_id = ?2, source_node = ?3
             WHERE producer_activation = ?4 AND output_id = ?5 AND phase = 0
               AND holder_node = ?3 AND consumer_activation IS NULL
               AND birth_edge_id IS NULL AND edge_id IS NULL AND source_node IS NULL",
            params![
                delivery.receiver(),
                delivery.edge_id(),
                delivery.source(),
                producer.as_slice(),
                output.as_slice()
            ],
        )?;
        if changed != 1 {
            return Err(SqliteStateError::invalid(
                "transferred package is no longer outbound",
            ));
        }
        let package = fact
            .as_ref()
            .map(|fact| &fact.package)
            .ok_or_else(|| SqliteStateError::invalid("transferred package is absent"))?;
        let authority = encode_authority(package.authority())?;
        insert_pending_head(
            &transaction,
            delivery.receiver(),
            &authority,
            delivery.edge_id(),
            package_id,
        )?;
        refresh_ready_trigger(&transaction, kernel, delivery.receiver(), &authority)?;
        let revision = advance_revision(&transaction)?;
        transaction.commit()?;
        Ok(Ok(SqliteTransferCommit { delivery, revision }))
    }

    fn validate_trigger_projection(&self, kernel: &Kernel) -> Result<(), SqliteStateError> {
        let invalid_head = self.connection.query_row(
            "SELECT EXISTS (
                SELECT 1
                FROM pending_heads h
                LEFT JOIN package_outputs o
                  ON o.producer_activation = h.producer_activation
                 AND o.output_id = h.output_id
                WHERE o.producer_activation IS NULL
                   OR o.phase IS NOT 1
                   OR o.holder_node != h.holder_node
                   OR o.authority != h.authority
                   OR o.edge_id != h.edge_id
                   OR EXISTS (
                       SELECT 1
                       FROM package_outputs earlier
                       WHERE earlier.phase = 1
                         AND earlier.holder_node = h.holder_node
                         AND earlier.authority = h.authority
                         AND earlier.edge_id = h.edge_id
                         AND (earlier.producer_activation, earlier.output_id)
                             < (h.producer_activation, h.output_id)
                   )
                UNION ALL
                SELECT 1
                FROM package_outputs o
                WHERE o.phase = 1
                  AND NOT EXISTS (
                      SELECT 1
                      FROM pending_heads h
                      WHERE h.holder_node = o.holder_node
                        AND h.authority = o.authority
                        AND h.edge_id = o.edge_id
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
        let expected = expected_ready_triggers(&self.connection, kernel)?;
        let actual = {
            let mut statement = self.connection.prepare(
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

fn encode_phase(phase: Phase) -> i64 {
    match phase {
        Phase::Out => 0,
        Phase::In => 1,
    }
}
fn decode_phase(phase: i64) -> Result<Phase, SqliteStateError> {
    match phase {
        0 => Ok(Phase::Out),
        1 => Ok(Phase::In),
        _ => Err(SqliteStateError::invalid("invalid package phase")),
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

fn advance_revision(connection: &Connection) -> Result<u64, SqliteStateError> {
    let revision = read_revision(connection)?
        .checked_add(1)
        .ok_or_else(|| SqliteStateError::invalid("state revision exhausted"))?;
    connection.execute(
        "UPDATE session_meta SET state_revision = ?1 WHERE singleton = 1",
        [encode_u64(revision)?],
    )?;
    Ok(revision)
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
    let fragment: RewriteFragment = serde_json::from_slice(&graph)
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
             used_node_ids = ?3, used_edge_ids = ?4, state_revision = ?5 WHERE singleton = 1",
        params![
            kernel.fingerprint().as_bytes().as_slice(),
            encode_json(&RewriteFragment::from_kernel(kernel))?,
            encode_ids(state.used_node_ids())?,
            encode_ids(state.used_edge_ids())?,
            encode_u64(state.revision())?
        ],
    )?;
    Ok(())
}

fn rebuild_readiness(connection: &Connection, kernel: &Kernel) -> Result<(), SqliteStateError> {
    connection.execute("DELETE FROM pending_heads", [])?;
    connection.execute("DELETE FROM ready_triggers", [])?;
    connection.execute(
        "INSERT INTO pending_heads(holder_node, authority, edge_id, producer_activation, output_id)
         SELECT o.holder_node, o.authority, o.edge_id, o.producer_activation, o.output_id
         FROM package_outputs o WHERE o.phase = 1 AND NOT EXISTS (
             SELECT 1 FROM package_outputs earlier
             WHERE earlier.phase = 1 AND earlier.holder_node = o.holder_node
               AND earlier.authority = o.authority AND earlier.edge_id = o.edge_id
               AND (earlier.producer_activation, earlier.output_id) < (o.producer_activation, o.output_id))", [],
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
            fault TEXT,
            CHECK((status = 2 AND fault IS NOT NULL) OR (status IN (0, 1) AND fault IS NULL))
         );
         CREATE TABLE activations (
            activation_id BLOB PRIMARY KEY CHECK(length(activation_id) = 16),
            trigger_kind INTEGER NOT NULL CHECK(trigger_kind IN (0, 1)),
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
            holder_node TEXT NOT NULL,
            phase INTEGER CHECK(phase IN (0, 1)),
            edge_id TEXT,
            source_node TEXT,
            consumer_activation BLOB CHECK(consumer_activation IS NULL OR length(consumer_activation) = 16),
            PRIMARY KEY(producer_activation, output_id),
            FOREIGN KEY(producer_activation) REFERENCES activations(activation_id),
            FOREIGN KEY(consumer_activation) REFERENCES activations(activation_id),
            CHECK((edge_id IS NULL) = (source_node IS NULL)),
            CHECK(birth_edge_id IS NULL OR (edge_id IS NOT NULL AND birth_edge_id = edge_id)),
            CHECK(phase IS NOT 0 OR edge_id IS NULL),
            CHECK(phase IS NOT 1 OR edge_id IS NOT NULL),
            CHECK(consumer_activation IS NULL OR (phase IS NULL AND edge_id IS NOT NULL))
         );
         CREATE TABLE pending_heads (
            holder_node TEXT NOT NULL,
            authority BLOB NOT NULL,
            edge_id TEXT NOT NULL,
            producer_activation BLOB NOT NULL CHECK(length(producer_activation) = 16),
            output_id BLOB NOT NULL CHECK(length(output_id) = 16),
            PRIMARY KEY(holder_node, authority, edge_id),
            UNIQUE(producer_activation, output_id),
            FOREIGN KEY(producer_activation, output_id) REFERENCES package_outputs(producer_activation, output_id)
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
    connection.execute_batch(context::SCHEMA)?;
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

fn read_transfer_fact(
    transaction: &Transaction<'_>,
    package_id: PackageId,
) -> Result<Option<SqliteTransferFact>, SqliteStateError> {
    let producer = activation_blob(package_id.producer());
    let output = u128_blob(package_id.output());
    let mut statement = transaction.prepare(
        "SELECT phase, consumer_activation IS NOT NULL, birth_edge_id, edge_id, source_node,
                holder_node, object_type, authority, content_digest
         FROM package_outputs WHERE producer_activation = ?1 AND output_id = ?2",
    )?;
    let mut rows = statement.query(params![producer.as_slice(), output.as_slice()])?;
    let Some(row) = rows.next()? else {
        return Ok(None);
    };
    let phase = row
        .get::<_, Option<i64>>(0)?
        .map(decode_phase)
        .transpose()?;
    let consumed = row.get::<_, bool>(1)?;
    let birth_edge = row.get::<_, Option<String>>(2)?;
    let edge = row.get::<_, Option<String>>(3)?;
    let source = row.get::<_, Option<String>>(4)?;
    if edge.is_some() != source.is_some()
        || birth_edge
            .as_ref()
            .is_some_and(|birth| Some(birth) != edge.as_ref())
        || (phase == Some(Phase::Out) && edge.is_some())
        || (phase == Some(Phase::In) && edge.is_none())
        || (consumed && (phase.is_some() || edge.is_none()))
    {
        return Err(SqliteStateError::invalid(
            "transfer package custody and delivery facts disagree",
        ));
    }
    let holder = Arc::<str>::from(row.get::<_, String>(5)?);
    Ok(Some(SqliteTransferFact {
        position: phase.map(|phase| Position::new(holder.clone(), phase)),
        consumed,
        package: Package {
            edge_id: edge.map(Arc::from),
            node_id: holder,
            object_type: Arc::from(row.get::<_, String>(6)?),
            authority: decode_authority(&row.get::<_, Vec<u8>>(7)?)?,
            content_digest: decode_digest(row.get(8)?)?,
        },
    }))
}

fn read_admission_view(
    transaction: &Transaction<'_>,
    package_ids: Option<&BTreeSet<PackageId>>,
) -> Result<SqliteAdmissionView, SqliteStateError> {
    let mut packages = BTreeMap::new();
    for package_id in package_ids.into_iter().flatten() {
        let producer = activation_blob(package_id.producer());
        let output = u128_blob(package_id.output());
        let row = transaction
            .query_row(
                "SELECT consumer_activation, phase, edge_id, holder_node, authority
             FROM package_outputs WHERE producer_activation = ?1 AND output_id = ?2",
                params![producer.as_slice(), output.as_slice()],
                |row| {
                    Ok((
                        row.get::<_, Option<Vec<u8>>>(0)?,
                        row.get::<_, Option<i64>>(1)?,
                        row.get::<_, Option<String>>(2)?,
                        row.get::<_, String>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                    ))
                },
            )
            .optional()?;
        let Some((consumer, phase, edge, holder, authority)) = row else {
            continue;
        };
        let fact =
            match (consumer, phase) {
                (Some(consumer), _) => SqlitePackageFact::Consumed(decode_activation(consumer)?),
                (None, None) => SqlitePackageFact::Retired,
                (None, Some(0)) => SqlitePackageFact::Outbound,
                (None, Some(1)) => SqlitePackageFact::Pending {
                    edge_id: Arc::from(edge.ok_or_else(|| {
                        SqliteStateError::invalid("delivered package omits receipt")
                    })?),
                    node_id: Arc::from(holder),
                    authority: decode_authority(&authority)?,
                },
                _ => return Err(SqliteStateError::invalid("invalid package phase")),
            };
        packages.insert(*package_id, fact);
    }
    Ok(SqliteAdmissionView { packages })
}

fn object_batch(
    delta: &AdmissionDelta,
    emitted_payloads: &[Payload],
) -> Result<(ContentDigest, BTreeMap<ContentDigest, Payload>), SqliteStateError> {
    if emitted_payloads.len() != delta.activation.package_outputs().len()
        || emitted_payloads.len() != delta.package_targets.len()
    {
        return Err(SqliteStateError::invalid(
            "accepted output, target, and proposal payload counts differ",
        ));
    }
    let result_digest = ContentDigest::compute(delta.activation.result());
    let mut objects = BTreeMap::from([(result_digest, delta.activation.result().clone())]);
    for (((package_id, output), payload), (target_package_id, _)) in delta
        .activation
        .package_outputs()
        .iter()
        .zip(emitted_payloads)
        .zip(&delta.package_targets)
    {
        if package_id != target_package_id {
            return Err(SqliteStateError::invalid(
                "accepted output and target package identities differ",
            ));
        }
        let computed = ContentDigest::compute(payload);
        if computed != output.content_digest() {
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
    Ok((result_digest, objects))
}

fn insert_delta(
    transaction: &Transaction<'_>,
    kernel: &Kernel,
    view: &SqliteAdmissionView,
    delta: &AdmissionDelta,
    result_digest: ContentDigest,
) -> Result<(), SqliteStateError> {
    insert_activation_record(transaction, delta.id, &delta.activation, result_digest)?;
    let activation_id_blob = activation_blob(delta.id);
    let mut changed_groups = BTreeSet::<(Arc<str>, Vec<u8>)>::new();
    if let Some(inputs) = delta.activation.inputs() {
        for package_id in inputs {
            let producer = activation_blob(package_id.producer());
            let output = u128_blob(package_id.output());
            let changed = transaction.execute(
                "UPDATE package_outputs
                 SET consumer_activation = ?1, phase = NULL
                 WHERE producer_activation = ?2 AND output_id = ?3
                   AND phase = 1",
                params![
                    activation_id_blob.as_slice(),
                    producer.as_slice(),
                    output.as_slice()
                ],
            )?;
            if changed != 1 {
                return Err(SqliteStateError::invalid(format!(
                    "accepted input {package_id} is not pending"
                )));
            }
            let Some(SqlitePackageFact::Pending {
                edge_id,
                node_id,
                authority,
            }) = view.packages.get(package_id)
            else {
                unreachable!("accepted input was observed pending");
            };
            let authority = encode_authority(authority)?;
            if advance_pending_head(transaction, node_id, &authority, edge_id, *package_id)? {
                changed_groups.insert((Arc::clone(node_id), authority));
            }
        }
    }
    for ((package_id, output), (target_package_id, holder_node)) in delta
        .activation
        .package_outputs()
        .iter()
        .zip(&delta.package_targets)
    {
        if package_id != target_package_id {
            return Err(SqliteStateError::invalid(
                "accepted output and target package identities differ",
            ));
        }
        let delivery = delta.deliveries.get(package_id);
        let phase = if delivery.is_some() {
            Phase::In
        } else {
            Phase::Out
        };
        insert_package_output(
            transaction,
            *package_id,
            output,
            holder_node,
            None,
            Some(phase),
            delivery,
        )?;
        if let Some(delivery) = delivery {
            let authority = encode_authority(output.authority())?;
            if insert_pending_head(
                transaction,
                holder_node,
                &authority,
                delivery.edge_id(),
                *package_id,
            )? {
                changed_groups.insert((Arc::clone(holder_node), authority));
            }
        }
    }
    for (node_id, authority) in changed_groups {
        refresh_ready_trigger(transaction, kernel, &node_id, &authority)?;
    }
    Ok(())
}

fn insert_activation_record(
    transaction: &Transaction<'_>,
    activation_id: ActivationId,
    activation: &Activation,
    result_digest: ContentDigest,
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
    transaction.execute(
        "INSERT INTO activations (
            activation_id, trigger_kind, root_node, root_authority, result_digest
         ) VALUES (?1, ?2, ?3, ?4, ?5)",
        params![
            activation_id.as_slice(),
            trigger_kind,
            root_node,
            root_authority,
            result_digest.as_bytes().as_slice()
        ],
    )?;
    Ok(())
}

fn insert_package_output(
    transaction: &Transaction<'_>,
    package_id: PackageId,
    output: &Output,
    holder_node: &str,
    consumer: Option<ActivationId>,
    phase: Option<Phase>,
    delivery: Option<&Delivery>,
) -> Result<(), SqliteStateError> {
    let producer = activation_blob(package_id.producer());
    let output_id = u128_blob(package_id.output());
    let authority = encode_authority(output.authority())?;
    let consumer = consumer.map(activation_blob);
    transaction.execute(
        "INSERT INTO package_outputs (producer_activation, output_id, birth_edge_id, object_type,
            authority, content_digest, holder_node, consumer_activation, phase, edge_id, source_node)
         VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
        params![producer.as_slice(), output_id.as_slice(), output.edge_id(), output.object_type(),
            authority.as_slice(), output.content_digest().as_bytes().as_slice(), holder_node,
            consumer.as_ref().map(<[u8; 16]>::as_slice), phase.map(encode_phase),
            delivery.map(Delivery::edge_id), delivery.map(Delivery::source)],
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
         SELECT holder_node, authority, edge_id, producer_activation, output_id
         FROM package_outputs INDEXED BY package_outputs_group_pending
         WHERE phase = 1
           AND holder_node = ?1 AND authority = ?2 AND edge_id = ?3
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
    kernel: &Kernel,
    node_id: &str,
    incoming_edges: &BTreeSet<Arc<str>>,
) -> Result<Vec<(PackageId, Package)>, SqliteStateError> {
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
    let mut packages = Vec::with_capacity(incoming_edges.len());
    for edge in incoming_edges {
        let mut selected = query_pending(
            connection,
            kernel,
            "SELECT o.producer_activation, o.output_id, o.edge_id, o.authority,
                    o.content_digest, o.holder_node, o.object_type
             FROM pending_heads h JOIN package_outputs o
               ON o.producer_activation = h.producer_activation AND o.output_id = h.output_id
              AND o.holder_node = h.holder_node AND o.authority = h.authority
              AND o.edge_id = h.edge_id
             WHERE h.holder_node = ?1 AND h.authority = ?2 AND h.edge_id = ?3 AND o.phase = 1",
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

fn query_pending<P>(
    connection: &Connection,
    _kernel: &Kernel,
    sql: &str,
    parameters: P,
) -> Result<Vec<(PackageId, Package)>, SqliteStateError>
where
    P: rusqlite::Params,
{
    let mut statement = connection.prepare(sql)?;
    let mut rows = statement.query(parameters)?;
    let mut packages = Vec::new();
    while let Some(row) = rows.next()? {
        let producer = decode_activation(row.get(0)?)?;
        let output = decode_u128(row.get(1)?, "package output identity")?;
        let edge_id = row.get::<_, Option<String>>(2)?.map(Arc::from);
        let object_type = Arc::from(row.get::<_, String>(6)?);
        packages.push((
            PackageId::from_parts(producer, output),
            Package {
                edge_id,
                object_type,
                authority: decode_authority(&row.get::<_, Vec<u8>>(3)?)?,
                content_digest: decode_digest(row.get(4)?)?,
                node_id: Arc::from(row.get::<_, String>(5)?),
            },
        ));
    }
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
    Ok(ActivationId::from_u128(decode_u128(
        bytes,
        "activation identity",
    )?))
}

fn decode_u128(bytes: Vec<u8>, kind: &str) -> Result<u128, SqliteStateError> {
    let bytes: [u8; 16] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid(format!("{kind} is not 16 bytes")))?;
    Ok(u128::from_be_bytes(bytes))
}

fn decode_digest(bytes: Vec<u8>) -> Result<ContentDigest, SqliteStateError> {
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid("content digest is not 32 bytes"))?;
    Ok(ContentDigest::from_bytes(bytes))
}

fn decode_fingerprint(bytes: Vec<u8>) -> Result<DefinitionFingerprint, SqliteStateError> {
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| SqliteStateError::invalid("definition fingerprint is not 32 bytes"))?;
    Ok(DefinitionFingerprint::from_bytes(bytes))
}

fn decode_u64(value: i64, kind: &str) -> Result<u64, SqliteStateError> {
    u64::try_from(value).map_err(|_| SqliteStateError::invalid(format!("invalid {kind}")))
}

fn encode_u64(value: u64) -> Result<i64, SqliteStateError> {
    i64::try_from(value).map_err(|_| SqliteStateError::invalid("revision exceeds SQLite range"))
}

fn decode_status(value: i64) -> Result<SessionStatus, SqliteStateError> {
    match value {
        0 => Ok(SessionStatus::Open),
        1 => Ok(SessionStatus::Closed),
        2 => Ok(SessionStatus::Faulted),
        _ => Err(SqliteStateError::invalid(format!(
            "unknown session status {value}"
        ))),
    }
}
