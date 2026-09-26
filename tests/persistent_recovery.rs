//! Recovery reconciles the object store against durable graph and invocation facts.
use ontography::{
    ActivationProposal, ContentDigest, ContextPolicy, InvocationTrigger, PackageId,
    ProposalDecision, ProposalRuntime, SessionStatus,
};
use std::sync::Arc;
#[allow(dead_code)]
mod support;

#[tokio::test]
async fn transient_failure_recovers_live_work_and_only_reclaims_orphans() {
    let dir = tempfile::tempdir().unwrap();
    let run = dir.path().join("run");
    let k = Arc::new(support::kernel(&["A", "B"], &[("ab", "A", "B", "payload")]));
    let runtime = ProposalRuntime::new(k.clone());
    let session = runtime.create_persistent(&run).unwrap();
    let content = session.content_store().await.unwrap();
    let kept = content
        .import_bytes(b"committed dependency".to_vec())
        .await
        .unwrap();
    let orphan = content
        .import_bytes(b"uncommitted dependency".to_vec())
        .await
        .unwrap();
    let invocation_only = content
        .import_bytes(b"invocation-only dependency".to_vec())
        .await
        .unwrap();
    let mut proposal = ActivationProposal::root("A", support::authority(), support::payload());
    proposal.emit(ontography::Emission::outbound(
        "t",
        ontography::OutputAuthority::Carry,
        support::payload(),
    ));
    let ProposalDecision::Committed(producer) = session
        .submit_with_content(proposal, vec![kept])
        .await
        .unwrap()
    else {
        panic!("root must commit")
    };
    let invocation = session
        .begin_invocation_with_content(
            "A",
            InvocationTrigger::Root {
                authority: support::authority(),
                input: Arc::from(b"retained invocation input".as_slice()),
            },
            ContextPolicy::default(),
            vec![invocation_only],
        )
        .await
        .unwrap();
    let receipt = invocation
        .record_tool_response("audit", Arc::from(b"retained receipt".as_slice()))
        .await
        .unwrap();
    invocation.mark_sent(receipt.sequence).await.unwrap();
    invocation.acknowledge(receipt.sequence).await.unwrap();
    drop(invocation);
    drop(content);
    drop(session);
    drop(runtime);
    let db = run.join("state.sqlite3");
    rusqlite::Connection::open(&db).unwrap().execute_batch("CREATE TRIGGER fail_revision BEFORE UPDATE OF state_revision ON session_meta BEGIN SELECT RAISE(FAIL, 'injected'); END;").unwrap();
    let runtime = ProposalRuntime::new(k.clone());
    let session = runtime.open_persistent(&run).unwrap();
    let content = session.content_store().await.unwrap();
    let error = session
        .submit_with_content(
            ActivationProposal::root(
                "A",
                support::authority(),
                Arc::from(b"orphan result".as_slice()),
            ),
            vec![orphan],
        )
        .await
        .unwrap_err();
    assert!(matches!(error, ontography::SessionError::Faulted(_)));
    assert_eq!(session.status(), SessionStatus::Faulted);
    content.release(orphan).await.unwrap();
    content.release(kept).await.unwrap();
    content.release(invocation_only).await.unwrap();
    content.collect_garbage().await.unwrap();
    assert!(matches!(
        content.metadata(orphan).await,
        Err(ontography::ContentError::Missing(_))
    ));
    assert!(content.metadata(kept).await.unwrap().complete);
    assert!(content.metadata(invocation_only).await.unwrap().complete);
    drop(content);
    drop(session);
    drop(runtime);
    rusqlite::Connection::open(&db)
        .unwrap()
        .execute_batch("DROP TRIGGER fail_revision;")
        .unwrap();
    let runtime = ProposalRuntime::new(k);
    let session = runtime.open_persistent(&run).unwrap();
    assert_eq!(session.status(), SessionStatus::Open);
    assert!(session.snapshot().await.fault().is_none());
    for data in [
        b"retained invocation input".as_slice(),
        b"retained receipt".as_slice(),
    ] {
        assert_eq!(
            session
                .content(ContentDigest::compute(data))
                .await
                .unwrap()
                .as_deref(),
            Some(data)
        );
    }
    assert!(
        session
            .content(ContentDigest::compute(b"orphan result"))
            .await
            .unwrap()
            .is_none()
    );
    session
        .transfer(PackageId::from_parts(producer, 0), "ab")
        .await
        .unwrap()
        .unwrap();
    let decision = session
        .submit(ActivationProposal::package(
            PackageId::from_parts(producer, 0),
            support::payload(),
        ))
        .await
        .unwrap();
    assert!(matches!(decision, ProposalDecision::Committed(_)));
}

#[tokio::test]
async fn reopen_reconciles_abandoned_publication_without_a_fault_marker() {
    let dir = tempfile::tempdir().unwrap();
    let run = dir.path().join("run");
    let k = Arc::new(support::kernel(&["A"], &[]));
    let runtime = ProposalRuntime::new(k.clone());
    let session = runtime.create_persistent(&run).unwrap();
    let committed: Arc<[u8]> = Arc::from(b"committed graph result".as_slice());
    session
        .submit(ActivationProposal::root(
            "A",
            support::authority(),
            committed.clone(),
        ))
        .await
        .unwrap();
    let content = session.content_store().await.unwrap();
    // Simulate interruption after the object-store durability fence and before
    // the SQLite publication. No fault marker exists after this crash window.
    let orphan = content
        .import_bytes(b"abandoned artifact".to_vec())
        .await
        .unwrap();
    content.retain_canonical(&[orphan]).await.unwrap();
    content.release(orphan).await.unwrap();
    let payload = b"abandoned graph payload";
    let digest = ContentDigest::compute(payload);
    let orphan_payload = content.import_bytes(payload.to_vec()).await.unwrap();
    content
        .native()
        .tags()
        .set(digest.as_bytes(), orphan_payload.hash())
        .await
        .unwrap();
    content.release(orphan_payload).await.unwrap();
    let imported = content
        .import_bytes(b"pending caller artifact".to_vec())
        .await
        .unwrap();
    let native_owned = content
        .import_bytes(b"native caller artifact".to_vec())
        .await
        .unwrap();
    content
        .native()
        .tags()
        .set("independent-native-owner", native_owned.hash())
        .await
        .unwrap();
    content.release(native_owned).await.unwrap();
    content.native().sync_db().await.unwrap();
    drop(content);
    drop(session);
    drop(runtime);

    let runtime = ProposalRuntime::new(k);
    let session = runtime.open_persistent(&run).unwrap();
    assert_eq!(session.status(), SessionStatus::Open);
    assert!(session.content(digest).await.unwrap().is_none());
    let content = session.content_store().await.unwrap();
    content.collect_garbage().await.unwrap();
    for id in [orphan, orphan_payload] {
        assert!(matches!(
            content.metadata(id).await,
            Err(ontography::ContentError::Missing(_))
        ));
    }
    for id in [imported, native_owned] {
        assert!(content.metadata(id).await.unwrap().complete);
    }
    assert_eq!(
        session
            .content(ContentDigest::compute(&committed))
            .await
            .unwrap(),
        Some(committed)
    );
}

#[tokio::test]
async fn recovery_does_not_clear_a_fault_on_a_corrupt_checkpoint() {
    let dir = tempfile::tempdir().unwrap();
    let run = dir.path().join("run");
    let k = Arc::new(support::kernel(&["A"], &[]));
    let runtime = ProposalRuntime::new(k.clone());
    let session = runtime.create_persistent(&run).unwrap();
    drop(session);
    drop(runtime);
    let db = run.join("state.sqlite3");
    rusqlite::Connection::open(&db)
        .unwrap()
        .execute_batch(
            "UPDATE session_meta SET status = 2, fault = 'injected', state_revision = 1;",
        )
        .unwrap();
    let runtime = ProposalRuntime::new(k);
    assert!(runtime.open_persistent(&run).is_err());
    let status: i64 = rusqlite::Connection::open(&db)
        .unwrap()
        .query_row("SELECT status FROM session_meta", [], |row| row.get(0))
        .unwrap();
    assert_eq!(status, 2);
}
