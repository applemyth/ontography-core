//! Invocation records are operational facts, independent of graph revisions.
//!
//! The context store lives in the same `SQLite` file as the graph store but is
//! versioned separately: the graph store by `PRAGMA user_version`
//! (`SCHEMA_VERSION`), the context store by `context_meta.schema_version`
//! ([`CONTEXT_SCHEMA_VERSION`]). Each opener checks the store it reads: a
//! full session open checks both, the read-only inspection functions check
//! the context version alone. A run is compatible exactly when every checked
//! version equals the compiled one; there is no migration, and a mismatch is a
//! typed open error. A change to one store's tables or serialized records bumps
//! that store's version only.
//!
//! The graph store never names a context table. It reaches the context store
//! only through the hooks in this module: [`create_schema`],
//! [`verify_schema`], [`interrupt_open`], and the linked write that
//! [`link_submission`] performs inside a submission's transaction.
use super::{
    ActivationId, Connection, ContentDigest, ObjectStore, OpenFlags, OptionalExtension, PackageId,
    Path, SqliteSession, SqliteStateError, Transaction, activation_blob, decode_activation,
    decode_digest, decode_u64, params, u128_blob,
};
use crate::context::{
    ContextError, ContextEvent, ContextPolicy, InvocationId, InvocationRecord, InvocationStatus,
    ReceiptState,
};
use crate::context::{InvocationData, storage};
use ontography_calculus::Reject;

/// Version of the context store: `context_meta`, `context_invocations`, and
/// `context_events`, including their serialized invocation records.
pub(crate) const CONTEXT_SCHEMA_VERSION: i64 = 2;

const SCHEMA: &str = "
CREATE TABLE context_meta (
    singleton INTEGER PRIMARY KEY CHECK(singleton = 1),
    schema_version INTEGER NOT NULL CHECK(schema_version >= 1)
);
CREATE TABLE context_invocations (
    ordinal INTEGER PRIMARY KEY AUTOINCREMENT,
    invocation_id TEXT NOT NULL UNIQUE CHECK(length(invocation_id) = 36),
    node_id TEXT NOT NULL,
    owner TEXT,
    data BLOB NOT NULL,
    status TEXT NOT NULL DEFAULT 'open'
        CHECK(status IN ('open', 'accepted', 'rejected', 'interrupted', 'failed')),
    activation_id BLOB UNIQUE REFERENCES activations(activation_id),
    submission_digest BLOB
        CHECK(submission_digest IS NULL OR length(submission_digest) = 32),
    detail TEXT,
    next_sequence INTEGER NOT NULL DEFAULT 1 CHECK(next_sequence >= 1),
    returned_bytes INTEGER NOT NULL DEFAULT 0 CHECK(returned_bytes >= 0),
    CHECK((status = 'accepted') = (activation_id IS NOT NULL))
);
CREATE INDEX context_invocations_node ON context_invocations(node_id, invocation_id);
CREATE TABLE context_events (
    invocation_id TEXT NOT NULL REFERENCES context_invocations(invocation_id),
    sequence INTEGER NOT NULL CHECK(sequence >= 1),
    receipt_sequence INTEGER NOT NULL
        CHECK(receipt_sequence >= 1 AND receipt_sequence <= sequence),
    state TEXT NOT NULL CHECK(state IN ('prepared', 'sent', 'acknowledged')),
    operation TEXT,
    content_digest BLOB CHECK(content_digest IS NULL OR length(content_digest) = 32),
    byte_count INTEGER CHECK(byte_count IS NULL OR byte_count >= 0),
    source BLOB,
    PRIMARY KEY(invocation_id, sequence),
    UNIQUE(invocation_id, receipt_sequence, state),
    FOREIGN KEY(invocation_id, receipt_sequence)
        REFERENCES context_events(invocation_id, sequence),
    CHECK((state = 'prepared') = (receipt_sequence = sequence)),
    CHECK((state = 'prepared'
           AND operation IS NOT NULL AND content_digest IS NOT NULL
           AND byte_count IS NOT NULL AND source IS NOT NULL)
       OR (state != 'prepared'
           AND operation IS NULL AND content_digest IS NULL
           AND byte_count IS NULL AND source IS NULL))
);
";

/// Creates the context tables and records their schema version.
pub(super) fn create_schema(connection: &Connection) -> Result<(), SqliteStateError> {
    connection.execute_batch(SCHEMA)?;
    connection.execute(
        "INSERT INTO context_meta (singleton, schema_version) VALUES (1, ?1)",
        [CONTEXT_SCHEMA_VERSION],
    )?;
    Ok(())
}

/// Checks the stored context schema version against the compiled one.
///
/// A store without a `context_meta` table predates explicit context
/// versioning and reports version 0.
pub(super) fn verify_schema(connection: &Connection) -> Result<(), SqliteStateError> {
    let version = read_schema_version(connection)?;
    if version != CONTEXT_SCHEMA_VERSION {
        return Err(SqliteStateError::ContextSchemaVersion(version));
    }
    Ok(())
}

fn read_schema_version(connection: &Connection) -> Result<i64, SqliteStateError> {
    let present = connection.query_row(
        "SELECT EXISTS(
            SELECT 1 FROM sqlite_schema WHERE type = 'table' AND name = 'context_meta'
         )",
        [],
        |row| row.get::<_, bool>(0),
    )?;
    if !present {
        return Ok(0);
    }
    Ok(connection
        .query_row(
            "SELECT schema_version FROM context_meta WHERE singleton = 1",
            [],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
        .unwrap_or(0))
}

/// Interrupts every open invocation, recording `reason`.
pub(super) fn interrupt_open(
    connection: &Connection,
    reason: &str,
) -> Result<(), SqliteStateError> {
    connection.execute(
        "UPDATE context_invocations SET status = 'interrupted', detail = ?1
         WHERE status = 'open'",
        [reason],
    )?;
    Ok(())
}

/// Links one invocation to the submission decision inside its transaction.
///
/// Acceptance records the activation; a kernel rejection records the reason.
/// Both write the commitment digest of the submitted output so an exact retry
/// can be recognized. The invocation must still be open.
pub(crate) fn link_submission(
    transaction: &Transaction<'_>,
    id: InvocationId,
    commitment: ContentDigest,
    decision: Result<ActivationId, &Reject>,
) -> Result<(), SqliteStateError> {
    let changed = match decision {
        Ok(activation_id) => transaction.execute(
            "UPDATE context_invocations
             SET status = 'accepted', activation_id = ?2, submission_digest = ?3
             WHERE invocation_id = ?1 AND status = 'open'",
            params![
                id.to_string(),
                activation_blob(activation_id).as_slice(),
                commitment.as_bytes().as_slice()
            ],
        )?,
        Err(reject) => transaction.execute(
            "UPDATE context_invocations
             SET status = 'rejected', detail = ?2, submission_digest = ?3
             WHERE invocation_id = ?1 AND status = 'open'",
            params![
                id.to_string(),
                format!("{reject:?}"),
                commitment.as_bytes().as_slice()
            ],
        )?,
    };
    if changed != 1 {
        return Err(SqliteStateError::invalid("invocation is no longer active"));
    }
    Ok(())
}

/// How one context-store write failed.
///
/// The session's fault rule applies to the context store as to the graph
/// store: a refusal before any write leaves the session open, and a failure
/// once a write has begun faults it, because commit acknowledgment is then
/// uncertain.
#[derive(Debug)]
pub(crate) enum ContextWriteError {
    /// Nothing was written: the invocation is not open, a budget is
    /// exhausted, a pre-write read failed, or the transaction could not begin.
    Refused(ContextError),
    /// A statement or commit failed after the operation's first write.
    Failed(SqliteStateError),
}

impl From<ContextError> for ContextWriteError {
    fn from(error: ContextError) -> Self {
        Self::Refused(error)
    }
}

fn failed(error: rusqlite::Error) -> ContextWriteError {
    ContextWriteError::Failed(error.into())
}

pub(crate) struct PreparedReceipt<'a> {
    pub operation: &'a str,
    pub digest: ContentDigest,
    pub bytes: u64,
    pub source: &'a serde_json::Value,
}

pub(crate) struct StoredInvocation {
    pub status: InvocationStatus,
    pub activation: Option<ActivationId>,
    pub submission: Option<ContentDigest>,
    pub detail: Option<String>,
    pub next_sequence: u64,
    pub returned_bytes: u64,
}
fn status(value: &str) -> Result<InvocationStatus, ContextError> {
    match value {
        "open" => Ok(InvocationStatus::Open),
        "accepted" => Ok(InvocationStatus::Accepted),
        "rejected" => Ok(InvocationStatus::Rejected),
        "interrupted" => Ok(InvocationStatus::Interrupted),
        "failed" => Ok(InvocationStatus::Failed),
        _ => Err(ContextError::Storage("invalid invocation state".into())),
    }
}
pub(crate) fn status_name(s: InvocationStatus) -> &'static str {
    match s {
        InvocationStatus::Open => "open",
        InvocationStatus::Accepted => "accepted",
        InvocationStatus::Rejected => "rejected",
        InvocationStatus::Interrupted => "interrupted",
        InvocationStatus::Failed => "failed",
    }
}
fn receipt_name(s: ReceiptState) -> &'static str {
    match s {
        ReceiptState::Prepared => "prepared",
        ReceiptState::Sent => "sent",
        ReceiptState::Acknowledged => "acknowledged",
    }
}
fn receipt(value: &str) -> Result<ReceiptState, ContextError> {
    match value {
        "prepared" => Ok(ReceiptState::Prepared),
        "sent" => Ok(ReceiptState::Sent),
        "acknowledged" => Ok(ReceiptState::Acknowledged),
        _ => Err(ContextError::Storage("invalid receipt state".into())),
    }
}

impl SqliteSession {
    /// Adds every invocation-owned content reference, including interrupted
    /// invocations and prepared receipts, to the ledger's retention roots.
    pub(super) fn context_references(
        &self,
        payloads: &mut Vec<ContentDigest>,
        contents: &mut Vec<ontography_content::ContentId>,
    ) -> Result<(), SqliteStateError> {
        let mut statement = self
            .connection
            .prepare("SELECT data FROM context_invocations")?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            let data: InvocationData = serde_json::from_slice(&row.get::<_, Vec<u8>>(0)?)
                .map_err(|error| SqliteStateError::invalid(error.to_string()))?;
            if let crate::context::BoundTrigger::Root {
                input,
                dependencies,
                ..
            } = data.trigger
            {
                payloads.push(input);
                contents.extend(dependencies);
            }
        }
        let mut statement = self
            .connection
            .prepare("SELECT content_digest FROM context_events WHERE state = 'prepared'")?;
        let mut rows = statement.query([])?;
        while let Some(row) = rows.next()? {
            payloads.push(decode_digest(row.get(0)?)?);
        }
        Ok(())
    }

    pub(crate) fn verify_context_objects(
        &self,
        objects: &ObjectStore,
    ) -> Result<(), SqliteStateError> {
        let mut invocations = self
            .connection
            .prepare("SELECT invocation_id, data FROM context_invocations ORDER BY ordinal")?;
        let mut rows = invocations.query([])?;
        while let Some(row) = rows.next()? {
            let id: String = row.get(0)?;
            let data: InvocationData = serde_json::from_slice(&row.get::<_, Vec<u8>>(1)?)
                .map_err(|e| SqliteStateError::invalid(e.to_string()))?;
            if data.id.to_string() != id {
                return Err(SqliteStateError::invalid("invocation identity mismatch"));
            }
            if let crate::context::BoundTrigger::Root {
                input,
                dependencies,
                ..
            } = data.trigger
            {
                objects.require(input)?;
                objects.verify_content(&dependencies)?;
            }
            for package in &data.packages {
                let canonical = self.package_history(package.package_id)?.ok_or_else(|| {
                    SqliteStateError::invalid("invocation references unknown package")
                })?;
                if canonical.package().content_digest() != package.content_digest {
                    return Err(SqliteStateError::invalid(
                        "invocation package commitment mismatch",
                    ));
                }
            }
        }
        let mut events = self.connection.prepare(
            "SELECT content_digest, byte_count FROM context_events WHERE state = 'prepared'",
        )?;
        let mut rows = events.query([])?;
        while let Some(row) = rows.next()? {
            let digest = decode_digest(row.get(0)?)?;
            let bytes = decode_u64(row.get(1)?, "context receipt byte count")?;
            if objects.require(digest)?.len() as u64 != bytes {
                return Err(SqliteStateError::invalid(
                    "context receipt byte count mismatch",
                ));
            }
        }
        Ok(())
    }
    pub(crate) fn create_invocation(&self, data: &InvocationData) -> Result<(), ContextWriteError> {
        let encoded = serde_json::to_vec(data).map_err(storage)?;
        self.connection
            .execute(
                "INSERT INTO context_invocations (invocation_id, node_id, owner, data)
                 VALUES (?1, ?2, ?3, ?4)",
                params![data.id.to_string(), data.node_id, data.owner, encoded],
            )
            .map_err(failed)?;
        Ok(())
    }
    pub(crate) fn invocation(&self, id: InvocationId) -> Result<StoredInvocation, ContextError> {
        read_invocation(&self.connection, id)
    }
    pub(crate) fn end_invocation(
        &self,
        id: InvocationId,
        s: InvocationStatus,
        reason: &str,
    ) -> Result<(), ContextWriteError> {
        self.connection
            .execute(
                "UPDATE context_invocations SET status = ?2, detail = ?3
                 WHERE invocation_id = ?1 AND status = 'open'",
                params![id.to_string(), status_name(s), reason],
            )
            .map_err(failed)?;
        Ok(())
    }
    pub(crate) fn interrupt_invocations(
        &self,
        owner: Option<&str>,
        reason: &str,
    ) -> Result<(), ContextWriteError> {
        self.connection
            .execute(
                "UPDATE context_invocations SET status = 'interrupted', detail = ?2
                 WHERE status = 'open' AND (?1 IS NULL OR owner = ?1)",
                params![owner, reason],
            )
            .map_err(failed)?;
        Ok(())
    }
    /// Appends one prepared receipt. Every check precedes the first write, so
    /// a refusal leaves nothing behind.
    pub(crate) fn append_context_event(
        &mut self,
        id: InvocationId,
        policy: &ContextPolicy,
        event: PreparedReceipt<'_>,
        charge: u64,
    ) -> Result<u64, ContextWriteError> {
        let PreparedReceipt {
            operation,
            digest,
            bytes,
            source,
        } = event;
        let tx = self.connection.transaction().map_err(storage)?;
        let current = read_invocation(&tx, id)?;
        if current.status != InvocationStatus::Open {
            return Err(ContextError::Closed.into());
        }
        let total = current
            .returned_bytes
            .checked_add(charge)
            .ok_or_else(|| ContextError::Budget("bytes".into()))?;
        if total > policy.max_bytes as u64 {
            return Err(ContextError::Budget("bytes".into()).into());
        }
        if current.next_sequence > policy.max_events as u64 {
            return Err(ContextError::Budget("events".into()).into());
        }
        let seq = current.next_sequence;
        let source = serde_json::to_vec(source).map_err(storage)?;
        let (sequence, byte_count) = (sql_number(seq)?, sql_number(bytes)?);
        let (next_sequence, returned_bytes) = (sql_number(seq + 1)?, sql_number(total)?);
        tx.execute(
            "INSERT INTO context_events (
                invocation_id, sequence, receipt_sequence, state,
                operation, content_digest, byte_count, source
             ) VALUES (?1, ?2, ?2, 'prepared', ?3, ?4, ?5, ?6)",
            params![
                id.to_string(),
                sequence,
                operation,
                digest.as_bytes().as_slice(),
                byte_count,
                source
            ],
        )
        .map_err(failed)?;
        tx.execute(
            "UPDATE context_invocations SET next_sequence = ?2, returned_bytes = ?3
             WHERE invocation_id = ?1",
            params![id.to_string(), next_sequence, returned_bytes],
        )
        .map_err(failed)?;
        tx.commit().map_err(failed)?;
        Ok(seq)
    }
    /// Appends delivery evidence for a prepared receipt; every check precedes
    /// the first write.
    pub(crate) fn advance_receipt(
        &mut self,
        id: InvocationId,
        sequence: u64,
        state: ReceiptState,
        max_events: usize,
    ) -> Result<(), ContextWriteError> {
        let tx = self.connection.transaction().map_err(storage)?;
        let current = read_invocation(&tx, id)?;
        if current.status != InvocationStatus::Open {
            return Err(ContextError::Closed.into());
        }
        let prior: Option<String> = tx
            .query_row(
                "SELECT state FROM context_events
                 WHERE invocation_id = ?1 AND receipt_sequence = ?2
                 ORDER BY sequence DESC LIMIT 1",
                params![id.to_string(), sql_number(sequence)?],
                |r| r.get(0),
            )
            .optional()
            .map_err(storage)?;
        let Some(prior) = prior else {
            return Err(ContextError::NotFound.into());
        };
        let prior = receipt(&prior)?;
        if prior == state || prior == ReceiptState::Acknowledged {
            return Ok(());
        }
        if state == ReceiptState::Acknowledged && prior != ReceiptState::Sent {
            return Err(
                ContextError::Denied("receipt must be sent before acknowledgement".into()).into(),
            );
        }
        if state == ReceiptState::Prepared {
            return Err(ContextError::Denied("receipt cannot move backwards".into()).into());
        }
        if current.next_sequence > max_events as u64 {
            return Err(ContextError::Budget("events".into()).into());
        }
        let (event, receipt_sequence) = (sql_number(current.next_sequence)?, sql_number(sequence)?);
        let next_sequence = sql_number(current.next_sequence + 1)?;
        tx.execute(
            "INSERT INTO context_events (invocation_id, sequence, receipt_sequence, state)
             VALUES (?1, ?2, ?3, ?4)",
            params![id.to_string(), event, receipt_sequence, receipt_name(state)],
        )
        .map_err(failed)?;
        tx.execute(
            "UPDATE context_invocations SET next_sequence = ?2 WHERE invocation_id = ?1",
            params![id.to_string(), next_sequence],
        )
        .map_err(failed)?;
        tx.commit().map_err(failed)
    }
    pub(crate) fn invocation_page(
        &self,
        node: Option<&str>,
        after: Option<&str>,
        limit: usize,
    ) -> Result<Vec<InvocationRecord>, ContextError> {
        read_page(&self.connection, node, after, limit)
    }
    pub(crate) fn context_receipt_digest(
        &self,
        id: InvocationId,
        sequence: u64,
    ) -> Result<Option<ContentDigest>, ContextError> {
        let bytes: Option<Vec<u8>> = self
            .connection
            .query_row(
                "SELECT content_digest FROM context_events
                 WHERE invocation_id = ?1 AND receipt_sequence = ?2 AND state = 'prepared'",
                params![id.to_string(), sql_number(sequence)?],
                |r| r.get(0),
            )
            .optional()
            .map_err(storage)?;
        bytes.map(decode_digest).transpose().map_err(storage)
    }
    pub(crate) fn context_events(
        &self,
        id: InvocationId,
        after: u64,
        limit: usize,
    ) -> Result<Vec<ContextEvent>, ContextError> {
        read_event_page(&self.connection, id, after, limit)
    }
    pub(crate) fn package_pending_at(
        &self,
        id: PackageId,
        node: &str,
    ) -> Result<bool, ContextError> {
        self.connection
            .query_row(
                "SELECT EXISTS(
                    SELECT 1 FROM package_outputs
                    WHERE producer_activation = ?1 AND output_id = ?2
                      AND status = 0 AND delivery_edge IS NOT NULL AND delivery_receiver = ?3
                 )",
                params![
                    activation_blob(id.producer()).as_slice(),
                    u128_blob(id.output()).as_slice(),
                    node
                ],
                |r| r.get(0),
            )
            .map_err(storage)
    }
}

fn read_invocation(
    connection: &Connection,
    id: InvocationId,
) -> Result<StoredInvocation, ContextError> {
    let row: Option<InvocationRow> = connection
        .query_row(
            "SELECT status, activation_id, submission_digest, detail, next_sequence, returned_bytes
             FROM context_invocations WHERE invocation_id = ?1",
            [id.to_string()],
            |r| {
                Ok((
                    r.get(0)?,
                    r.get(1)?,
                    r.get(2)?,
                    r.get(3)?,
                    r.get(4)?,
                    r.get(5)?,
                ))
            },
        )
        .optional()
        .map_err(storage)?;
    let Some((state, activation, digest, detail, next_sequence, returned_bytes)) = row else {
        return Err(ContextError::NotFound);
    };
    Ok(StoredInvocation {
        status: status(&state)?,
        activation: activation
            .map(decode_activation)
            .transpose()
            .map_err(storage)?,
        submission: digest.map(decode_digest).transpose().map_err(storage)?,
        detail,
        next_sequence: read_number(next_sequence)?,
        returned_bytes: read_number(returned_bytes)?,
    })
}
fn checked_limit(limit: usize) -> Result<i64, ContextError> {
    if limit == 0 || limit > 10_000 {
        return Err(ContextError::Denied("page limit must be 1..=10000".into()));
    }
    i64::try_from(limit).map_err(storage)
}
fn read_page(
    c: &Connection,
    node: Option<&str>,
    after: Option<&str>,
    limit: usize,
) -> Result<Vec<InvocationRecord>, ContextError> {
    let mut stmt = c
        .prepare(
            "SELECT invocation_id, data FROM context_invocations
             WHERE (?1 IS NULL OR node_id = ?1)
               AND (?2 IS NULL OR ordinal > (
                   SELECT ordinal FROM context_invocations WHERE invocation_id = ?2
               ))
             ORDER BY ordinal LIMIT ?3",
        )
        .map_err(storage)?;
    let rows = stmt
        .query_map(params![node, after, checked_limit(limit)?], |r| {
            Ok((r.get::<_, String>(0)?, r.get::<_, Vec<u8>>(1)?))
        })
        .map_err(storage)?;
    rows.map(|row| {
        let (id, data) = row.map_err(storage)?;
        let id = id.parse()?;
        let data: InvocationData = serde_json::from_slice(&data).map_err(storage)?;
        let r = read_invocation(c, id)?;
        Ok(InvocationRecord {
            id,
            node_id: data.node_id,
            status: r.status,
            policy: data.policy,
            packages: data.packages,
            members: data.members,
            activation_id: r.activation.map(|a| format!("{:032x}", a.as_u128())),
            detail: r.detail,
            returned_bytes: r.returned_bytes,
        })
    })
    .collect()
}
fn read_event_page(
    c: &Connection,
    id: InvocationId,
    after: u64,
    limit: usize,
) -> Result<Vec<ContextEvent>, ContextError> {
    let mut stmt = c
        .prepare(
            "SELECT e.sequence, e.receipt_sequence, e.state,
                    p.operation, p.content_digest, p.byte_count, p.source
             FROM context_events e
             JOIN context_events p
               ON p.invocation_id = e.invocation_id AND p.sequence = e.receipt_sequence
             WHERE e.invocation_id = ?1 AND e.sequence > ?2
             ORDER BY e.sequence LIMIT ?3",
        )
        .map_err(storage)?;
    let mut rows = stmt
        .query(params![
            id.to_string(),
            sql_number(after)?,
            checked_limit(limit)?
        ])
        .map_err(storage)?;
    let mut events = Vec::new();
    while let Some(r) = rows.next().map_err(storage)? {
        events.push(ContextEvent {
            invocation_id: id,
            sequence: read_number(r.get(0).map_err(storage)?)?,
            receipt_sequence: read_number(r.get(1).map_err(storage)?)?,
            state: receipt(&r.get::<_, String>(2).map_err(storage)?)?,
            operation: r.get(3).map_err(storage)?,
            content_digest: decode_digest(r.get(4).map_err(storage)?).map_err(storage)?,
            bytes: read_number(r.get(5).map_err(storage)?)?,
            source: serde_json::from_slice(&r.get::<_, Vec<u8>>(6).map_err(storage)?)
                .map_err(storage)?,
        });
    }
    Ok(events)
}
/// Opens a suspended run's facts read-only for context inspection.
///
/// Only the context store is read, so only its version is checked; the graph
/// store may be at any version.
fn readonly(path: &Path) -> Result<Connection, ContextError> {
    let connection =
        Connection::open_with_flags(path.join("state.sqlite3"), OpenFlags::SQLITE_OPEN_READ_ONLY)
            .map_err(storage)?;
    verify_schema(&connection).map_err(storage)?;
    Ok(connection)
}
pub(crate) fn read_invocations(
    path: &Path,
    node: Option<&str>,
    after: Option<&str>,
    limit: usize,
) -> Result<Vec<InvocationRecord>, ContextError> {
    read_page(&readonly(path)?, node, after, limit)
}
pub(crate) fn read_events(
    path: &Path,
    id: InvocationId,
    after: u64,
    limit: usize,
) -> Result<Vec<ContextEvent>, ContextError> {
    read_event_page(&readonly(path)?, id, after, limit)
}

fn sql_number(value: u64) -> Result<i64, ContextError> {
    i64::try_from(value).map_err(storage)
}
fn read_number(value: i64) -> Result<u64, ContextError> {
    u64::try_from(value).map_err(storage)
}

type InvocationRow = (
    String,
    Option<Vec<u8>>,
    Option<Vec<u8>>,
    Option<String>,
    i64,
    i64,
);
