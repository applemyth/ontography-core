//! Package identities and member names preserve their exact representation.
use ontography::{PackageDocument, PackageStore, ProposalRuntime};
use std::collections::BTreeMap;
use std::sync::Arc;
#[allow(dead_code)]
mod support;

#[tokio::test]
async fn package_identity_and_names_preserve_exact_bytes() {
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
    for (a, b) in [("é", "e\u{301}"), ("É", "e\u{301}"), ("é", "ø")] {
        let id = packages
            .put(&PackageDocument::Collection {
                entries: BTreeMap::from([(a.into(), canonical), (b.into(), canonical)]),
            })
            .await
            .unwrap();
        let view = packages.resolve(id).await.unwrap();
        assert_eq!(view.entries().len(), 3);
        for name in [a, b] {
            assert!(view.entries().iter().any(|entry| entry.path == name));
        }
    }
}
