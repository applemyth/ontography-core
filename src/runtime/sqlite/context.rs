//! Invocation records are operational facts, independent of graph revisions.
use super::{
    ActivationId, Connection, ContentDigest, ObjectStore, OpenFlags, OptionalExtension, PackageId,
    Path, SCHEMA_VERSION, SqliteSession, SqliteStateError, activation_blob, decode_activation,
    decode_digest, decode_u64, params, u128_blob,
};
use crate::context::{
    ContextError, ContextEvent, ContextPolicy, InvocationId, InvocationRecord, InvocationStatus,
    ReceiptState,
};
use crate::context::{InvocationData, storage};

pub(super) const SCHEMA: &str = "
CREATE TABLE context_invocations (
 ordinal INTEGER PRIMARY KEY AUTOINCREMENT, invocation_id TEXT NOT NULL UNIQUE CHECK(length(invocation_id)=36), node_id TEXT NOT NULL, owner TEXT, data BLOB NOT NULL,
 status TEXT NOT NULL DEFAULT 'open' CHECK(status IN ('open','accepted','rejected','interrupted','failed')), activation_id BLOB UNIQUE REFERENCES activations(activation_id),
 submission_digest BLOB CHECK(submission_digest IS NULL OR length(submission_digest)=32), detail TEXT, next_sequence INTEGER NOT NULL DEFAULT 1 CHECK(next_sequence>=1),
 returned_bytes INTEGER NOT NULL DEFAULT 0 CHECK(returned_bytes>=0),
 CHECK((status='accepted')=(activation_id IS NOT NULL))
);
CREATE INDEX context_invocations_node ON context_invocations(node_id, invocation_id);
CREATE TABLE context_events (
 invocation_id TEXT NOT NULL REFERENCES context_invocations(invocation_id),
 sequence INTEGER NOT NULL CHECK(sequence>=1), receipt_sequence INTEGER NOT NULL CHECK(receipt_sequence>=1 AND receipt_sequence<=sequence), state TEXT NOT NULL CHECK(state IN ('prepared','sent','acknowledged')),
 operation TEXT, content_digest BLOB CHECK(content_digest IS NULL OR length(content_digest)=32), byte_count INTEGER CHECK(byte_count IS NULL OR byte_count>=0),
 source BLOB, PRIMARY KEY(invocation_id,sequence),
 UNIQUE(invocation_id,receipt_sequence,state),
 FOREIGN KEY(invocation_id,receipt_sequence) REFERENCES context_events(invocation_id,sequence),
 CHECK((state='prepared')=(receipt_sequence=sequence)),
 CHECK((state='prepared' AND operation IS NOT NULL AND content_digest IS NOT NULL AND byte_count IS NOT NULL AND source IS NOT NULL) OR (state!='prepared' AND operation IS NULL AND content_digest IS NULL AND byte_count IS NULL AND source IS NULL))
);
";

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
    pub(crate) fn verify_context_objects(
        &self,
        objects: &ObjectStore,
    ) -> Result<(), SqliteStateError> {
        let mut invocations = self
            .connection
            .prepare("SELECT invocation_id,data FROM context_invocations ORDER BY ordinal")?;
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
            "SELECT content_digest,byte_count FROM context_events WHERE state='prepared'",
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
    pub(crate) fn create_invocation(&self, data: &InvocationData) -> Result<(), ContextError> {
        self.connection.execute("INSERT INTO context_invocations(invocation_id,node_id,owner,data) VALUES(?1,?2,?3,?4)",params![data.id.to_string(),data.node_id,data.owner,serde_json::to_vec(data).map_err(storage)?]).map_err(storage)?;
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
    ) -> Result<(), ContextError> {
        self.connection.execute("UPDATE context_invocations SET status=?2,detail=?3 WHERE invocation_id=?1 AND status='open'",params![id.to_string(),status_name(s),reason]).map_err(storage)?;
        Ok(())
    }
    pub(crate) fn interrupt_invocations(
        &self,
        owner: Option<&str>,
        reason: &str,
    ) -> Result<(), ContextError> {
        self.connection.execute("UPDATE context_invocations SET status='interrupted',detail=?2 WHERE status='open' AND (?1 IS NULL OR owner=?1)",params![owner,reason]).map_err(storage)?;
        Ok(())
    }
    pub(crate) fn append_context_event(
        &mut self,
        id: InvocationId,
        policy: &ContextPolicy,
        event: PreparedReceipt<'_>,
        charge: u64,
    ) -> Result<u64, ContextError> {
        let PreparedReceipt {
            operation,
            digest,
            bytes,
            source,
        } = event;
        let tx = self.connection.transaction().map_err(storage)?;
        let current = read_invocation(&tx, id)?;
        if current.status != InvocationStatus::Open {
            return Err(ContextError::Closed);
        }
        let total = current
            .returned_bytes
            .checked_add(charge)
            .ok_or_else(|| ContextError::Budget("bytes".into()))?;
        if total > policy.max_bytes as u64 {
            return Err(ContextError::Budget("bytes".into()));
        }
        if current.next_sequence > policy.max_events as u64 {
            return Err(ContextError::Budget("events".into()));
        }
        let seq = current.next_sequence;
        tx.execute("INSERT INTO context_events(invocation_id,sequence,receipt_sequence,state,operation,content_digest,byte_count,source) VALUES(?1,?2,?2,'prepared',?3,?4,?5,?6)",params![id.to_string(),sql_number(seq)?,operation,digest.as_bytes().as_slice(),sql_number(bytes)?,serde_json::to_vec(source).map_err(storage)?]).map_err(storage)?;
        tx.execute("UPDATE context_invocations SET next_sequence=?2,returned_bytes=?3 WHERE invocation_id=?1",params![id.to_string(),sql_number(seq+1)?,sql_number(total)?]).map_err(storage)?;
        tx.commit().map_err(storage)?;
        Ok(seq)
    }
    pub(crate) fn advance_receipt(
        &mut self,
        id: InvocationId,
        sequence: u64,
        state: ReceiptState,
        max_events: usize,
    ) -> Result<(), ContextError> {
        let tx = self.connection.transaction().map_err(storage)?;
        let current = read_invocation(&tx, id)?;
        if current.status != InvocationStatus::Open {
            return Err(ContextError::Closed);
        }
        let prior: Option<String> = tx.query_row("SELECT state FROM context_events WHERE invocation_id=?1 AND receipt_sequence=?2 ORDER BY sequence DESC LIMIT 1",params![id.to_string(),sql_number(sequence)?],|r|r.get(0)).optional().map_err(storage)?;
        let Some(prior) = prior else {
            return Err(ContextError::NotFound);
        };
        let prior = receipt(&prior)?;
        if prior == state || prior == ReceiptState::Acknowledged {
            return Ok(());
        }
        if state == ReceiptState::Acknowledged && prior != ReceiptState::Sent {
            return Err(ContextError::Denied(
                "receipt must be sent before acknowledgement".into(),
            ));
        }
        if state == ReceiptState::Prepared {
            return Err(ContextError::Denied("receipt cannot move backwards".into()));
        }
        if current.next_sequence > max_events as u64 {
            return Err(ContextError::Budget("events".into()));
        }
        tx.execute("INSERT INTO context_events(invocation_id,sequence,receipt_sequence,state) VALUES(?1,?2,?3,?4)",params![id.to_string(),sql_number(current.next_sequence)?,sql_number(sequence)?,receipt_name(state)]).map_err(storage)?;
        tx.execute(
            "UPDATE context_invocations SET next_sequence=?2 WHERE invocation_id=?1",
            params![id.to_string(), sql_number(current.next_sequence + 1)?],
        )
        .map_err(storage)?;
        tx.commit().map_err(storage)
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
        let bytes:Option<Vec<u8>>=self.connection.query_row("SELECT content_digest FROM context_events WHERE invocation_id=?1 AND receipt_sequence=?2 AND state='prepared'",params![id.to_string(),sql_number(sequence)?],|r|r.get(0)).optional().map_err(storage)?;
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
        self.connection.query_row("SELECT EXISTS(SELECT 1 FROM package_outputs WHERE producer_activation=?1 AND output_id=?2 AND phase=1 AND holder_node=?3)",params![activation_blob(id.producer()).as_slice(),u128_blob(id.output()).as_slice(),node],|r|r.get(0)).map_err(storage)
    }
}

fn read_invocation(
    connection: &Connection,
    id: InvocationId,
) -> Result<StoredInvocation, ContextError> {
    let row: Option<InvocationRow> = connection.query_row("SELECT status,activation_id,submission_digest,detail,next_sequence,returned_bytes FROM context_invocations WHERE invocation_id=?1",[id.to_string()],|r|Ok((r.get(0)?,r.get(1)?,r.get(2)?,r.get(3)?,r.get(4)?,r.get(5)?))).optional().map_err(storage)?;
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
    let mut stmt=c.prepare("SELECT invocation_id,data FROM context_invocations WHERE (?1 IS NULL OR node_id=?1) AND (?2 IS NULL OR ordinal>(SELECT ordinal FROM context_invocations WHERE invocation_id=?2)) ORDER BY ordinal LIMIT ?3").map_err(storage)?;
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
    let mut stmt=c.prepare("SELECT e.sequence,e.receipt_sequence,e.state,p.operation,p.content_digest,p.byte_count,p.source FROM context_events e JOIN context_events p ON p.invocation_id=e.invocation_id AND p.sequence=e.receipt_sequence WHERE e.invocation_id=?1 AND e.sequence>?2 ORDER BY e.sequence LIMIT ?3").map_err(storage)?;
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
fn readonly(path: &Path) -> Result<Connection, ContextError> {
    let connection =
        Connection::open_with_flags(path.join("state.sqlite3"), OpenFlags::SQLITE_OPEN_READ_ONLY)
            .map_err(storage)?;
    let version: i64 = connection
        .pragma_query_value(None, "user_version", |r| r.get(0))
        .map_err(storage)?;
    if version != SCHEMA_VERSION {
        return Err(ContextError::Storage(format!(
            "unsupported persistent schema version {version}"
        )));
    }
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
