//! Portable package names retain their bytes; filesystem views reject aliases.
use ontography::{PackageDocument, PackageStore, ProposalRuntime};
use std::collections::BTreeMap;
use std::sync::Arc;
#[allow(dead_code)]
mod support;

#[tokio::test]
async fn workspace_rejects_unicode_aliases_without_changing_package_identity() {
    let runtime = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])));
    let session = runtime.open().unwrap();
    let content = session.content_store().await.unwrap();
    let packages = PackageStore::new(content.clone());
    let empty = PackageDocument::Collection {
        entries: BTreeMap::new(),
    };
    let canonical = packages.put(&empty).await.unwrap();
    let alternate = content
        .import_bytes(br#"{ "entries": {}, "kind": "collection" }"#.to_vec())
        .await
        .unwrap();
    assert_eq!(packages.get(alternate).await.unwrap(), empty);
    assert_ne!(alternate, canonical);
    assert_eq!(
        packages
            .put(&packages.get(alternate).await.unwrap())
            .await
            .unwrap(),
        canonical
    );
    let directory = tempfile::tempdir().unwrap();
    let workspace = ontography::workspace::WorkspaceStore::new(content, directory.path());
    for (a, b) in [("é", "e\u{301}"), ("É", "e\u{301}")] {
        let id = packages
            .put(&PackageDocument::Collection {
                entries: BTreeMap::from([(a.into(), canonical), (b.into(), canonical)]),
            })
            .await
            .unwrap();
        assert!(matches!(
            workspace.open(id).await,
            Err(ontography::workspace::WorkspaceError::Invalid(message))
                if message == "case- or Unicode-normalization-colliding paths"
        ));
    }
    let distinct = packages
        .put(&PackageDocument::Collection {
            entries: BTreeMap::from([("é".into(), canonical), ("ø".into(), canonical)]),
        })
        .await
        .unwrap();
    workspace.open(distinct).await.unwrap();
}
