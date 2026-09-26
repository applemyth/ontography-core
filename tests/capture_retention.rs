//! Capture retention belongs to the capture until publication succeeds.
use ontography::{Authority, Contract, PackageDocument, PackageStore, ProposalRuntime};
use std::collections::BTreeMap;
use std::sync::Arc;
fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}
#[allow(dead_code)]
mod support;
#[tokio::test]
async fn rejected_finish_preserves_other_uncommitted_package() {
    use ontography::{
        ApplicationBuilder, ApplicationContext, ContextPolicy, InvocationTrigger, NodeComponent,
        NodeConfig, WorkspacePolicy,
    };
    use std::os::unix::fs::PermissionsExt;
    let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
    let done = Arc::new(tokio::sync::Notify::new());
    let worker_done = done.clone();
    let config = NodeConfig::new(
        ["Node"],
        Contract::new("result", "Result", |_| Ok(())).unwrap(),
    )
    .unwrap()
    .with_context_policy(ContextPolicy {
        workspace: Some(WorkspacePolicy {
            input_edge: None,
            writable: false,
            output_edge: None,
        }),
        ..ContextPolicy::default()
    });
    let component = NodeComponent::new(config, move |context: ApplicationContext| {
        let tx = tx.clone();
        let done = worker_done.clone();
        async move {
            tx.send(context).unwrap();
            done.notified().await;
            Ok(())
        }
    })
    .with_root_authority(Authority::new([]));
    let mut builder = ApplicationBuilder::new("finish-audit").unwrap();
    builder.entry("entry", component).unwrap();
    let run = builder
        .build()
        .unwrap()
        .start_ephemeral(bytes(b"input"))
        .await
        .unwrap();
    let context = rx.recv().await.unwrap();
    let content = run.session().content_store().await.unwrap();
    let workspace = context.workspace_store();
    let dir = tempfile::tempdir().unwrap();
    let base_dir = dir.path().join("base");
    std::fs::create_dir(&base_dir).unwrap();
    std::fs::write(base_dir.join("base.txt"), b"committed base").unwrap();
    let base = workspace.import_directory(&base_dir).await.unwrap();
    let other_dir = dir.path().join("other");
    std::fs::create_dir(&other_dir).unwrap();
    std::fs::write(other_dir.join("shared.txt"), b"pending shared bytes").unwrap();
    let other = workspace.import_directory(&other_dir).await.unwrap();
    let invocation = context
        .begin_invocation_with_content(
            InvocationTrigger::Root {
                authority: Authority::new([]),
                input: ontography::PackageEnvelope::new(base.root())
                    .to_payload()
                    .unwrap(),
            },
            base.dependencies(),
        )
        .await
        .unwrap();
    let checkout = context
        .prepare_workspace(&invocation)
        .await
        .unwrap()
        .unwrap();
    std::fs::set_permissions(checkout.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
    std::fs::write(checkout.path().join("shared.txt"), b"pending shared bytes").unwrap();
    assert!(checkout.finish().await.is_err());
    content.collect_garbage().await.unwrap();
    workspace.open(other.root()).await.unwrap();
    done.notify_one();
    run.wait_idle().await;
    run.shutdown().await;
}

#[tokio::test]
async fn invalid_capture_releases_imports_and_staging_is_isolated() {
    let runtime = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])));
    let session = runtime.open().unwrap();
    let content = session.content_store().await.unwrap();
    let directory = tempfile::tempdir().unwrap();
    let workspace =
        ontography::workspace::WorkspaceStore::new(content.clone(), directory.path().join("cache"));
    let source = directory.path().join("source");
    std::fs::create_dir(&source).unwrap();
    let data = b"unique failed-capture bytes";
    // Learn the identity, then remove its preexisting retention.
    let id = content.import_bytes(data.to_vec()).await.unwrap();
    content.release(id).await.unwrap();
    content.collect_garbage().await.unwrap();
    std::fs::write(source.join("data"), data).unwrap();
    std::os::unix::fs::symlink("b", source.join("a")).unwrap();
    std::os::unix::fs::symlink("a", source.join("b")).unwrap();
    assert!(workspace.import_directory(&source).await.is_err());
    content.collect_garbage().await.unwrap();
    assert!(matches!(
        content.metadata(id).await,
        Err(ontography::ContentError::Missing(_))
    ));

    let first = content.stage_imports();
    let second = content.stage_imports();
    let id = first.store().import_bytes(data.to_vec()).await.unwrap();
    assert_eq!(
        id,
        second.store().import_bytes(data.to_vec()).await.unwrap()
    );
    drop(first);
    content.collect_garbage().await.unwrap();
    assert!(content.metadata(id).await.unwrap().complete);
    second.retain().await.unwrap();
    content.collect_garbage().await.unwrap();
    assert!(content.metadata(id).await.unwrap().complete);
    content.release(id).await.unwrap();
    content.collect_garbage().await.unwrap();
    assert!(matches!(
        content.metadata(id).await,
        Err(ontography::ContentError::Missing(_))
    ));

    // A cancelled/rejected staged capture must also release new package metadata.
    let packages = PackageStore::new(content.clone());
    let empty = packages
        .put(&PackageDocument::Collection {
            entries: BTreeMap::new(),
        })
        .await
        .unwrap();
    std::fs::remove_file(source.join("a")).unwrap();
    std::fs::remove_file(source.join("b")).unwrap();
    let capture = workspace.capture_staged(&source, empty).await.unwrap();
    let root = capture.package().root();
    content.collect_garbage().await.unwrap();
    workspace.open(root).await.unwrap();
    drop(capture);
    content.collect_garbage().await.unwrap();
    assert!(matches!(
        content.metadata(root).await,
        Err(ontography::ContentError::Missing(_))
    ));
    assert!(matches!(
        content.metadata(id).await,
        Err(ontography::ContentError::Missing(_))
    ));
    workspace.open(empty).await.unwrap();
}
