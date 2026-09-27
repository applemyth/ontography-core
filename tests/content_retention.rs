//! Staged imports own their pins independently of existing artifacts and other stages.
use ontography::{ContentError, PackageDocument, PackageStore, ProposalRuntime};
use std::collections::BTreeMap;
use std::sync::Arc;

#[allow(dead_code)]
mod support;

#[tokio::test]
async fn dropped_staged_changes_preserve_existing_content() {
    let runtime = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])));
    let session = runtime.open().unwrap();
    let content = session.content_store().await.unwrap();
    let packages = PackageStore::new(content.clone());
    let shared_bytes = b"another caller's artifact";
    let shared = content.import_bytes(shared_bytes.to_vec()).await.unwrap();
    let shared_file = packages
        .put(&PackageDocument::File {
            content: shared,
            executable: false,
        })
        .await
        .unwrap();
    let base = packages
        .put(&PackageDocument::Collection {
            entries: BTreeMap::from([("shared.txt".into(), shared_file)]),
        })
        .await
        .unwrap();
    let imports = content.stage_imports();
    imports
        .protect(&packages.resolve(base).await.unwrap().dependencies())
        .await
        .unwrap();
    let staged = imports.store();
    assert_eq!(
        staged.import_bytes(shared_bytes.to_vec()).await.unwrap(),
        shared
    );
    let added = staged
        .import_bytes(b"tentative bytes".to_vec())
        .await
        .unwrap();
    let staged_packages = PackageStore::new(staged);
    let added_file = staged_packages
        .put(&PackageDocument::File {
            content: added,
            executable: false,
        })
        .await
        .unwrap();
    let changes = staged_packages
        .put(&PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("added.txt".into(), Some(added_file))]),
        })
        .await
        .unwrap();
    content.collect_garbage().await.unwrap();
    packages.resolve(changes).await.unwrap();

    // Rejection or cancellation drops every handle to the stage, reclaiming
    // its new bytes and metadata without releasing the base or another import.
    drop(staged_packages);
    drop(imports);
    content.collect_garbage().await.unwrap();
    for id in [added, added_file, changes] {
        assert!(matches!(
            content.metadata(id).await,
            Err(ContentError::Missing(_))
        ));
    }
    packages.resolve(base).await.unwrap();
    assert!(content.metadata(shared).await.unwrap().complete);
}

#[tokio::test]
async fn staged_imports_are_isolated_and_retained_on_acceptance() {
    let runtime = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])));
    let session = runtime.open().unwrap();
    let content = session.content_store().await.unwrap();
    let first = content.stage_imports();
    let second = content.stage_imports();
    let bytes = b"shared staged bytes";
    let id = first.store().import_bytes(bytes.to_vec()).await.unwrap();
    assert_eq!(
        id,
        second.store().import_bytes(bytes.to_vec()).await.unwrap()
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
        Err(ContentError::Missing(_))
    ));
}
