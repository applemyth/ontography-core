use ontography::{
    ActivationProposal, Authority, ContentDigest, Contract, DefinitionId, Graph, Kernel, Node,
    NodeDefinition, ProposalRuntime, RootRule, Schema,
};
use rusqlite::Connection;
use std::sync::Arc;

#[tokio::test]
#[ignore = "known orphan retention after failed SQLite commit"]
async fn failed_sql_commit_leaves_no_unreferenced_payload_after_gc() {
    let temp = tempfile::tempdir().unwrap();
    let run = temp.path().join("run");
    let kernel = Arc::new(
        Kernel::admit(
            DefinitionId::new("orphan-probe").unwrap(),
            Schema::new(["Node"], ["Result"], []).unwrap(),
            Graph::new([Node::new("a").unwrap()], []).unwrap(),
            [Contract::new("result", "Result", |_| Ok(())).unwrap()],
            [NodeDefinition::new("a", ["Node"], "result").unwrap()],
            [],
            [],
            [RootRule::new("a", Authority::new([])).unwrap()],
        )
        .unwrap(),
    );
    let runtime = ProposalRuntime::new(Arc::clone(&kernel));
    let session = runtime.create_persistent(&run).unwrap();
    drop(session);
    drop(runtime);

    let db = run.join("state.sqlite3");
    Connection::open(&db).unwrap().execute_batch(
        "CREATE TRIGGER fail_revision BEFORE UPDATE OF state_revision ON session_meta BEGIN SELECT RAISE(FAIL, 'injected revision failure'); END;"
    ).unwrap();

    let payload: Arc<[u8]> = Arc::from(&b"orphaned unique result"[..]);
    let digest = ContentDigest::compute(&payload);
    let runtime = ProposalRuntime::new(Arc::clone(&kernel));
    let session = runtime.open_persistent(&run).unwrap();
    assert!(
        session
            .submit(ActivationProposal::root(
                "a",
                Authority::new([]),
                payload.clone()
            ))
            .await
            .is_err()
    );
    drop(session);
    drop(runtime);

    let connection = Connection::open(&db).unwrap();
    let count: i64 = connection
        .query_row("SELECT COUNT(*) FROM activations", [], |row| row.get(0))
        .unwrap();
    assert_eq!(count, 0);
    connection
        .execute_batch("DROP TRIGGER fail_revision;")
        .unwrap();
    drop(connection);

    let runtime = ProposalRuntime::new(Arc::clone(&kernel));
    let session = runtime.open_persistent(&run).unwrap();
    assert_eq!(
        session.content(digest).await.unwrap(),
        Some(payload.clone())
    );
    session
        .content_store()
        .await
        .unwrap()
        .collect_garbage()
        .await
        .unwrap();
    assert_eq!(session.content(digest).await.unwrap(), None);
}
