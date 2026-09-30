//! Package limits hold exactly at their boundaries, and resolving costs only
//! what is read and what is visible: views share subtrees instead of copying.

use ontography::{
    ContentId, ContentStore, PackageDocument, PackageError, PackageLimits, PackageStore,
    ProposalRuntime, ResolvedPackage, SessionHandle,
};
use std::collections::BTreeMap;
use std::ops::Sub;
use std::sync::Arc;
#[allow(dead_code)]
mod support;

/// No bound applies unless a test sets it.
fn open() -> PackageLimits {
    PackageLimits {
        max_documents: usize::MAX,
        max_document_bytes: u64::MAX,
        max_evaluation_bytes: u64::MAX,
        max_entries: usize::MAX,
        max_view_bytes: u64::MAX,
    }
}

fn evaluation(bytes: u64) -> PackageLimits {
    PackageLimits {
        max_evaluation_bytes: bytes,
        ..open()
    }
}

struct Fixture {
    _session: SessionHandle,
    content: ContentStore,
    packages: PackageStore,
    documents: Vec<ContentId>,
    files: usize,
}

impl Fixture {
    async fn new() -> Self {
        let session = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])))
            .open()
            .unwrap();
        let content = session.content_store().await.unwrap();
        Self {
            _session: session,
            packages: PackageStore::new(content.clone()).with_limits(open()),
            content,
            documents: Vec::new(),
            files: 0,
        }
    }

    async fn put(&mut self, document: PackageDocument) -> ContentId {
        let id = self.packages.put(&document).await.unwrap();
        self.documents.push(id);
        id
    }

    /// A file whose bytes no other file shares.
    async fn file(&mut self) -> ContentId {
        self.files += 1;
        let content = self
            .content
            .import_bytes(self.files.to_string().into_bytes())
            .await
            .unwrap();
        self.put(PackageDocument::File {
            content,
            executable: false,
        })
        .await
    }

    /// Files `f0..` inside `depth` nested collections, each outer one naming the next `d`.
    async fn workspace(&mut self, files: usize, depth: usize) -> ContentId {
        let mut entries = BTreeMap::new();
        for i in 0..files {
            entries.insert(format!("f{i}"), self.file().await);
        }
        let mut root = self.put(PackageDocument::Collection { entries }).await;
        for _ in 1..depth {
            root = self.collection([("d", root)]).await;
        }
        root
    }

    /// Changes layers, each replacing `path` with a new file.
    async fn saves(&mut self, mut root: ContentId, path: &str, saves: usize) -> ContentId {
        for _ in 0..saves {
            let file = self.file().await;
            root = self
                .put(PackageDocument::Changes {
                    base: root,
                    changes: BTreeMap::from([(path.to_owned(), Some(file))]),
                })
                .await;
        }
        root
    }

    /// `k` collections, each naming its predecessor twice: 2^(k+1) - 1 entries.
    async fn doubling(&mut self, k: usize) -> ContentId {
        let mut root = self.file().await;
        for _ in 0..k {
            root = self.collection([("a", root), ("b", root)]).await;
        }
        root
    }

    async fn collection<const N: usize>(&mut self, entries: [(&str, ContentId); N]) -> ContentId {
        let entries = entries.map(|(name, id)| (name.to_owned(), id));
        self.put(PackageDocument::Collection {
            entries: BTreeMap::from(entries),
        })
        .await
    }

    /// Stored bytes of every document put so far; fixtures never repeat one.
    fn document_bytes(&self) -> u64 {
        self.documents.iter().map(|id| id.size()).sum()
    }

    async fn resolve(
        &self,
        root: ContentId,
        limits: PackageLimits,
    ) -> Result<ResolvedPackage, PackageError> {
        self.packages
            .clone()
            .with_limits(limits)
            .resolve(root)
            .await
    }

    async fn refusal(&self, root: ContentId, limits: PackageLimits) -> &'static str {
        match self.resolve(root, limits).await {
            Err(PackageError::Limit(reason)) => reason,
            other => panic!("expected a limit, got {other:?}"),
        }
    }

    /// The smallest evaluation budget that resolves `root`.
    async fn least_evaluation_bytes(&self, root: ContentId) -> u64 {
        let (mut refused, mut enough) = (0, u64::MAX);
        while enough - refused > 1 {
            let middle = refused + (enough - refused) / 2;
            match self.resolve(root, evaluation(middle)).await {
                Ok(_) => enough = middle,
                Err(PackageError::Limit("evaluation bytes")) => refused = middle,
                Err(error) => panic!("unexpected {error}"),
            }
        }
        enough
    }

    /// Resolution succeeds at `n` and is refused for `reason` at `n - 1`.
    async fn threshold<T: Copy + Sub<Output = T> + From<u8>>(
        &self,
        root: ContentId,
        n: T,
        reason: &str,
        limits: impl Fn(T) -> PackageLimits,
    ) {
        self.resolve(root, limits(n)).await.unwrap();
        assert_eq!(self.refusal(root, limits(n - T::from(1))).await, reason);
    }
}

#[tokio::test]
async fn cost_follows_documents_read_not_folders_or_saves() {
    for files in [1, 7, 50] {
        for depth in [1, 3, 40] {
            for saves in [0, 1, 25] {
                let mut fixture = Fixture::new().await;
                let base = fixture.workspace(files, depth).await;
                let path = format!("{}f0", "d/".repeat(depth - 1));
                let root = fixture.saves(base, &path, saves).await;
                // A chain of saves shares nothing, so reading is the whole cost.
                let bytes = fixture.document_bytes();
                fixture
                    .threshold(root, files + depth + 2 * saves, "documents", |n| {
                        PackageLimits {
                            max_documents: n,
                            ..open()
                        }
                    })
                    .await;
                fixture
                    .threshold(root, bytes, "evaluation bytes", evaluation)
                    .await;
                let view = fixture.resolve(root, open()).await.unwrap();
                assert_eq!(view.entry_count(), files + depth);
                assert_eq!(view.entries().len(), files + depth);
            }
        }
    }
}

#[tokio::test]
async fn nesting_is_bounded_by_the_path_rule_not_a_depth_limit() {
    let mut fixture = Fixture::new().await;
    // "d/" 2047 times, then "f0": exactly the 4096-byte path limit.
    let deepest = fixture.workspace(1, 2048).await;
    let view = fixture
        .resolve(deepest, PackageLimits::default())
        .await
        .unwrap();
    let longest = view.entries().iter().map(|entry| entry.path.len()).max();
    assert_eq!(longest, Some(4096));
    let deeper = fixture.collection([("d", deepest)]).await;
    assert!(matches!(
        fixture.resolve(deeper, PackageLimits::default()).await,
        Err(PackageError::Invalid(_))
    ));
}

#[tokio::test]
async fn created_folders_and_deletions_change_only_their_paths() {
    let mut fixture = Fixture::new().await;
    let base = fixture.workspace(1, 1).await;
    let file = fixture.file().await;
    let created = fixture
        .put(PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("a/b/c".to_owned(), Some(file))]),
        })
        .await;
    let deleted = fixture
        .put(PackageDocument::Changes {
            base: created,
            changes: BTreeMap::from([("a".to_owned(), None)]),
        })
        .await;
    let view = fixture.resolve(created, open()).await.unwrap();
    let paths: Vec<_> = view.entries().into_iter().map(|entry| entry.path).collect();
    assert_eq!(paths, ["", "a", "a/b", "a/b/c", "f0"]);
    // Folders the save created or changed identify it, as the root does.
    for path in ["", "a", "a/b"] {
        assert_eq!(view.entry(path).unwrap().package, created);
    }
    fixture
        .threshold(created, 5, "visible entries", |n| PackageLimits {
            max_entries: n,
            ..open()
        })
        .await;
    let view = fixture.resolve(deleted, open()).await.unwrap();
    assert_eq!(view.entry_count(), 2);
}

#[tokio::test]
async fn republishing_follows_the_view_not_the_record() {
    let mut fixture = Fixture::new().await;
    let (f, secret, edited, public) = (
        fixture.file().await,
        fixture.file().await,
        fixture.file().await,
        fixture.file().await,
    );
    let c = fixture.collection([("f", f)]).await;
    let d = fixture.collection([("secret", secret)]).await;
    let base = fixture.collection([("c", c), ("d", d)]).await;
    let first = fixture
        .put(PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("c/f".to_owned(), Some(edited))]),
        })
        .await;
    let new_d = fixture.collection([("public", public)]).await;
    let current = fixture
        .put(PackageDocument::Changes {
            base: first,
            changes: BTreeMap::from([("d".to_owned(), Some(new_d))]),
        })
        .await;
    let view = fixture.resolve(current, open()).await.unwrap();
    // "c" still carries the first save's ID, but that save's own view holds
    // the old d/secret, which the current view hides.
    assert_eq!(view.entry("c").unwrap().package, first);
    assert!(view.entry("d/secret").is_none());
    let old = fixture.resolve(first, open()).await.unwrap();
    assert!(old.entry("d/secret").is_some());
    assert_eq!(view.republishable("c"), None);
    assert!(!view.publishes(first));
    assert_eq!(view.republishable(""), Some(current));
    assert_eq!(view.republishable("d"), Some(new_d));
    assert_eq!(view.republishable("c/f"), Some(edited));
    assert!(view.publishes(edited));
}

fn parent(path: &str) -> &str {
    path.rsplit_once('/').map_or("", |(parent, _)| parent)
}

#[tokio::test]
async fn lookups_answer_from_the_view() {
    let mut fixture = Fixture::new().await;
    let root = fixture.workspace(3, 3).await;
    let root = fixture.saves(root, "d/d/f1", 2).await;
    let view = fixture.resolve(root, open()).await.unwrap();
    let entries = view.entries();
    assert_eq!(view.entry_count(), entries.len());
    let written: usize = entries.iter().map(|entry| entry.path.len()).sum();
    assert_eq!(view.view_bytes(), written as u64);
    assert_eq!(view.root_entry(), entries[0]);
    for entry in &entries {
        assert_eq!(view.entry(&entry.path).as_ref(), Some(entry));
        if let Some(children) = view.children(&entry.path) {
            let expected: Vec<_> = entries
                .iter()
                .filter(|child| !child.path.is_empty() && parent(&child.path) == entry.path)
                .cloned()
                .collect();
            assert_eq!(children, expected);
        }
    }
    assert!(view.entry("d/missing").is_none());
    assert!(view.children("d/d/f0").is_none());
}

#[tokio::test]
async fn a_shared_base_is_copied_once_and_charged() {
    let mut fixture = Fixture::new().await;
    let base = fixture.workspace(50, 1).await;
    let one = fixture.saves(base, "f0", 1).await;
    let two = fixture.saves(base, "f1", 1).await;
    let root = fixture.collection([("one", one), ("two", two)]).await;
    let documents = fixture.document_bytes();
    // Both saves change one base: the first copies its 50 entries, and the
    // second, as the base's last user, changes it in place.
    let copied = fixture.least_evaluation_bytes(root).await - documents;
    let names: u64 = (0..50).map(|i| format!("f{i}").len() as u64).sum();
    assert!(copied > names + 50 * 16, "{copied} bytes for 50 entries");
    assert!(
        copied < names + 50 * 64 + 1024,
        "{copied} bytes for 50 entries"
    );
    assert_eq!(
        fixture.refusal(root, evaluation(documents - 1)).await,
        "evaluation bytes"
    );
    let view = fixture.resolve(root, open()).await.unwrap();
    assert_ne!(view.entry("one/f0"), view.entry("two/f0"));
    assert_eq!(view.entry_count(), 1 + 2 * 51);
    // A chain over the same base shares nothing, so it costs only its reading.
    let chain = fixture.saves(one, "f1", 1).await;
    let dependencies = fixture.resolve(chain, open()).await.unwrap().dependencies();
    let read: u64 = dependencies
        .iter()
        .filter(|id| fixture.documents.contains(id))
        .map(|id| id.size())
        .sum();
    assert_eq!(fixture.least_evaluation_bytes(chain).await, read);
}

#[tokio::test]
async fn created_folders_are_charged_as_they_are_created() {
    // A save creating k implicit folders costs k equal charges beyond its reading.
    let mut costs = Vec::new();
    for folders in [10, 20] {
        let mut fixture = Fixture::new().await;
        let base = fixture.workspace(1, 1).await;
        let file = fixture.file().await;
        let root = fixture
            .put(PackageDocument::Changes {
                base,
                changes: BTreeMap::from([(format!("{}f", "a/".repeat(folders)), Some(file))]),
            })
            .await;
        costs.push(fixture.least_evaluation_bytes(root).await - fixture.document_bytes());
    }
    assert!(costs[0] > 0);
    assert_eq!(costs[1], 2 * costs[0]);
}

#[tokio::test]
async fn entries_are_counted_after_every_change() {
    let mut fixture = Fixture::new().await;
    let big = fixture.workspace(60, 1).await;
    let other = fixture.workspace(60, 1).await;
    let base = fixture.collection([("z", big)]).await;
    // Adding "a" first overflows the bound; deleting "z" afterwards would not
    // bring it back, because the view is checked after each change.
    let root = fixture
        .put(PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("a".to_owned(), Some(other)), ("z".to_owned(), None)]),
        })
        .await;
    let entries = |n| PackageLimits {
        max_entries: n,
        ..open()
    };
    assert_eq!(fixture.refusal(root, entries(100)).await, "visible entries");
    assert_eq!(
        fixture
            .resolve(root, entries(123))
            .await
            .unwrap()
            .entry_count(),
        62
    );
}

#[tokio::test]
async fn view_bytes_bound_what_writing_out_costs() {
    let mut fixture = Fixture::new().await;
    let link = fixture
        .put(PackageDocument::Symlink {
            target: "t".repeat(100),
        })
        .await;
    let root = fixture.collection([("a", link), ("b", link)]).await;
    // "a" and "b" each write their name and the shared 100-byte target.
    let view = fixture.resolve(root, open()).await.unwrap();
    assert_eq!(view.view_bytes(), 2 * (1 + 100));
    fixture
        .threshold(root, 202, "view bytes", |n| PackageLimits {
            max_view_bytes: n,
            ..open()
        })
        .await;
}

#[tokio::test]
async fn deleting_a_deep_path_lets_the_view_nest_again() {
    let mut fixture = Fixture::new().await;
    // "old/" plus 1,989 "d/" and "f0": 3,984 bytes, which a 200-byte prefix overflows.
    let deep = fixture.workspace(1, 1990).await;
    let keep = fixture.file().await;
    let base = fixture.collection([("keep", keep), ("old", deep)]).await;
    let pruned = fixture
        .put(PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("old".to_owned(), None)]),
        })
        .await;
    let prefix = "x".repeat(200);
    let nested = fixture.collection([(prefix.as_str(), pruned)]).await;
    let view = fixture.resolve(nested, open()).await.unwrap();
    assert_eq!(view.entry_count(), 3);
    let unpruned = fixture.collection([(prefix.as_str(), base)]).await;
    assert!(matches!(
        fixture.resolve(unpruned, open()).await,
        Err(PackageError::Invalid(_))
    ));
}

#[tokio::test]
async fn changes_documents_bound_their_own_entries() {
    let mut fixture = Fixture::new().await;
    let base = fixture.workspace(1, 1).await;
    // Deleting absent paths keeps the view at 2 entries, isolating the document bound.
    let changes = (0..50).map(|i| (format!("x{i}"), None)).collect();
    let root = fixture
        .put(PackageDocument::Changes { base, changes })
        .await;
    fixture
        .threshold(root, 50, "changes entries", |n| PackageLimits {
            max_entries: n,
            ..open()
        })
        .await;
}

#[tokio::test]
async fn visible_entries_bound_every_resolved_tree() {
    let mut fixture = Fixture::new().await;
    let nested = fixture.workspace(50, 3).await;
    let saved = fixture.saves(nested, "d/d/f0", 2).await;
    let entries = |n| PackageLimits {
        max_entries: n,
        ..open()
    };
    for root in [nested, saved] {
        fixture
            .threshold(root, 53, "visible entries", entries)
            .await;
    }
    // A k-member collection always resolves to k + 1 entries, so its document
    // is refused before resolution once it alone would reach the bound.
    let flat = fixture.workspace(50, 1).await;
    fixture
        .threshold(flat, 51, "collection entries", entries)
        .await;
}

#[tokio::test]
async fn document_bytes_bound_put_and_get() {
    let mut fixture = Fixture::new().await;
    let root = fixture.workspace(50, 1).await;
    let largest = fixture.documents.iter().map(|id| id.size()).max().unwrap();
    assert_eq!(largest, root.size());
    let bytes = |n| PackageLimits {
        max_document_bytes: n,
        ..open()
    };
    fixture
        .threshold(root, largest, "document bytes", bytes)
        .await;
    let document = fixture.packages.get(root).await.unwrap();
    let put = |n| fixture.packages.clone().with_limits(bytes(n));
    assert_eq!(put(largest).put(&document).await.unwrap(), root);
    assert!(matches!(
        put(largest - 1).put(&document).await,
        Err(PackageError::Limit("document bytes"))
    ));
}

#[tokio::test]
async fn shared_members_cannot_amplify_past_the_defaults() {
    let mut fixture = Fixture::new().await;
    // 41 documents describing 2^41 - 1 entries, refused from counts alone.
    let bomb = fixture.doubling(40).await;
    assert_eq!(
        fixture.refusal(bomb, PackageLimits::default()).await,
        "visible entries"
    );
}

#[tokio::test]
async fn saves_cost_their_changes_not_the_workspace() {
    let mut fixture = Fixture::new().await;
    // One file shared by 50,000 names, then 1,000 saves. Each save changes
    // one entry in place, where copying views allowed only 18 saves.
    let file = fixture.file().await;
    let entries = (0..50_000).map(|i| (format!("f{i}"), file)).collect();
    let base = fixture.put(PackageDocument::Collection { entries }).await;
    let root = fixture.saves(base, "f0", 1_000).await;
    let view = fixture
        .resolve(root, PackageLimits::default())
        .await
        .unwrap();
    assert_eq!(view.entry_count(), 50_001);
}

#[tokio::test]
async fn long_save_chains_resolve_without_a_depth_limit() {
    let mut fixture = Fixture::new().await;
    let base = fixture.workspace(1, 1).await;
    let root = fixture.saves(base, "f0", 10_000).await;
    let view = fixture
        .resolve(root, PackageLimits::default())
        .await
        .unwrap();
    assert_eq!(view.entry_count(), 2);
}
