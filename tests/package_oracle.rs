//! Differential test for package resolution. Random package DAGs, put only
//! through the public API, must resolve to exactly what a naive recursive
//! reading of the semantics computes: the same paths, packages, kinds and byte
//! order, or an error on both sides.

use ontography::content::Hash;
use ontography::{
    ContentId, ContentStore, PackageDocument, PackageError, PackageLimits, PackageStore,
    ProposalRuntime, ResolvedEntry, ResolvedEntryKind,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
#[allow(dead_code)]
mod support;

const SEEDS: u64 = 300;
/// Soft bound on the documents one naive evaluation of a package visits.
const MAX_COST: usize = 300;
/// Percent chance of each deliberate fault: a file-like base for changes, or a
/// change path through a file or symlink.
const FAULT: u64 = 1;

const BAD_BASE: &str = "changes base is not a directory";
const CROSSING: &str = "change path crosses a non-directory";

/// Shapes each seen in at least `MIN_CASES` cases, so the generator is known
/// to produce them. The last two are the reference's error reasons.
const SHAPES: [&str; 20] = [
    "executable file",
    "shared file content",
    "symlink",
    "empty folder",
    "child under several names",
    "replace file or symlink",
    "replace folder",
    "delete entry",
    "delete absent path",
    "insert new path",
    "implicit folder",
    "several changes in one record",
    "empty changes",
    "changes on changes",
    "changes over a collection holding changes",
    "shared base",
    "edit under a repeated folder",
    "byte order differs from tree order",
    BAD_BASE,
    CROSSING,
];
const MIN_CASES: u64 = 10;

/// Full path to (supplying package, kind). `BTreeMap` order is byte order.
type View = BTreeMap<String, (ContentId, ResolvedEntryKind)>;
/// Every document put, by hash: `ContentId` is not `Hash`, and a raw blob's
/// hash names it.
type Docs = HashMap<Hash, PackageDocument>;

#[tokio::test]
async fn resolution_matches_a_naive_reference() {
    let session = ProposalRuntime::new(Arc::new(support::kernel(&["A"], &[])))
        .open()
        .unwrap();
    let content = session.content_store().await.unwrap();
    let packages = PackageStore::new(content.clone()).with_limits(PackageLimits {
        max_documents: usize::MAX,
        max_document_bytes: u64::MAX,
        max_evaluation_bytes: u64::MAX,
        max_entries: usize::MAX,
        max_view_bytes: u64::MAX,
    });
    let mut cases = BTreeMap::<&str, u64>::new();
    let mut largest = 0;
    for seed in 0..SEEDS {
        let mut case = Case {
            rng: Rng(seed),
            packages: packages.clone(),
            content: content.clone(),
            docs: Docs::new(),
            pool: Vec::new(),
        };
        let root = case.build().await;
        match (packages.resolve(root).await, reference(root, &case.docs)) {
            (Ok(resolved), Ok(view)) => {
                let actual = resolved.entries();
                let expected: Vec<ResolvedEntry> = view
                    .iter()
                    .map(|(path, (package, kind))| ResolvedEntry {
                        path: path.clone(),
                        package: *package,
                        kind: kind.clone(),
                    })
                    .collect();
                for i in 0..actual.len().max(expected.len()) {
                    assert_eq!(actual.get(i), expected.get(i), "seed {seed}, entry {i}");
                }
                let dependencies = resolved.dependencies();
                for id in reachable(root, &case.docs) {
                    assert!(dependencies.contains(&id), "seed {seed}: {id:?}");
                    if let PackageDocument::File { content, .. } = &case.docs[&id.hash()] {
                        assert!(dependencies.contains(content), "seed {seed}: {content:?}");
                    }
                }
                // A package is republishable at a path exactly when its own
                // view is the visible subtree there; anything else could
                // expose files this view hides.
                let mut own = HashMap::<Hash, View>::new();
                for entry in actual.iter().step_by(actual.len().div_ceil(200)) {
                    let own = own.entry(entry.package.hash()).or_insert_with(|| {
                        reference(entry.package, &case.docs).expect("a visible package resolves")
                    });
                    let expected = (subtree(&view, &entry.path) == *own).then_some(entry.package);
                    assert_eq!(
                        resolved.republishable(&entry.path),
                        expected,
                        "seed {seed}: {:?}",
                        entry.path
                    );
                }
                largest = largest.max(actual.len());
                for shape in shapes(root, &case.docs, &view) {
                    *cases.entry(shape).or_default() += 1;
                }
            }
            (Err(error), Err(reason)) => {
                // Semantic failures only: a limit, cycle or storage error would
                // mean the case left the regime this test is about.
                assert!(
                    matches!(error, PackageError::Invalid(_)),
                    "seed {seed}: {error}"
                );
                *cases.entry(reason).or_default() += 1;
            }
            (Ok(_), Err(reason)) => panic!("seed {seed}: resolved; the reference failed: {reason}"),
            (Err(error), Ok(_)) => panic!("seed {seed}: {error}; the reference resolved"),
        }
    }
    println!("{SEEDS} seeds, largest view {largest} entries, cases per shape: {cases:#?}");
    for shape in SHAPES {
        let count = cases.get(shape).copied().unwrap_or_default();
        assert!(count >= MIN_CASES, "only {count} cases with {shape:?}");
    }
}

// The oracle.

/// The part of `view` at `path`, re-rooted there.
fn subtree(view: &View, path: &str) -> View {
    view.iter()
        .filter_map(|(entry, value)| {
            let relative = if path.is_empty() {
                Some(entry.as_str())
            } else if entry == path {
                Some("")
            } else {
                entry.strip_prefix(path)?.strip_prefix('/')
            };
            relative.map(|relative| (relative.to_owned(), value.clone()))
        })
        .collect()
}

/// Evaluate `id` recursively and naively, straight from the semantics.
fn reference(id: ContentId, docs: &Docs) -> Result<View, &'static str> {
    use ResolvedEntryKind::Directory;
    let root = |kind| View::from([(String::new(), (id, kind))]);
    Ok(match &docs[&id.hash()] {
        PackageDocument::File {
            content,
            executable,
        } => root(ResolvedEntryKind::File {
            content: *content,
            executable: *executable,
        }),
        PackageDocument::Symlink { target } => root(ResolvedEntryKind::Symlink {
            target: target.clone(),
        }),
        PackageDocument::Collection { entries } => {
            let mut view = root(Directory);
            for (name, child) in entries {
                graft(&mut view, name, reference(*child, docs)?);
            }
            view
        }
        PackageDocument::Changes { base, changes } => {
            let mut view = reference(*base, docs)?;
            if view[""].1 != Directory {
                return Err(BAD_BASE);
            }
            for (path, replacement) in changes {
                let removed = prune(&mut view, path);
                let changed = removed || replacement.is_some();
                // A file or symlink above the path fails; an existing folder is
                // credited to this record if anything changed; a missing one is
                // created only for an insertion.
                for parent in ancestors(path) {
                    match view.get_mut(parent) {
                        Some((_, kind)) if *kind != Directory => return Err(CROSSING),
                        Some((package, _)) if changed => *package = id,
                        None if replacement.is_some() => {
                            view.insert(parent.to_owned(), (id, Directory));
                        }
                        _ => {}
                    }
                }
                if let Some(replacement) = replacement {
                    graft(&mut view, path, reference(*replacement, docs)?);
                }
            }
            // The root is always credited to this record, even with no changes.
            view.insert(String::new(), (id, Directory));
            view
        }
    })
}

/// Remove `path` and everything under it, reporting whether anything was there.
fn prune(view: &mut View, path: &str) -> bool {
    let under = format!("{path}/");
    let before = view.len();
    view.retain(|entry, _| entry != path && !entry.starts_with(&under));
    view.len() < before
}

/// Place `child` at `prefix`: its root becomes `prefix`, and "x" becomes "prefix/x".
fn graft(view: &mut View, prefix: &str, child: View) {
    for (path, entry) in child {
        let path = if path.is_empty() {
            prefix.to_owned()
        } else {
            format!("{prefix}/{path}")
        };
        view.insert(path, entry);
    }
}

/// Proper ancestors of `path`, nearest first, without the root: "a/b/c"
/// gives "a/b", then "a".
fn ancestors(path: &str) -> impl Iterator<Item = &str> {
    path.rmatch_indices('/')
        .map(move |(slash, _)| &path[..slash])
}

// The generator.

/// `SplitMix64`: a tiny deterministic generator, plenty for test inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n`, up to a negligible modulo bias.
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next() % n as u64).unwrap()
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len())]
    }

    /// One to three characters. '-' and '.' sort just before '/', and '0' just
    /// after it, so names like "a-b", "a.b" and "a0" interleave with "a/x".
    fn name(&mut self) -> String {
        loop {
            let name: String = (0..=self.below(3))
                .map(|_| char::from(self.pick(b"ab-.0")))
                .collect();
            if name != "." && name != ".." {
                return name;
            }
        }
    }

    fn names(&mut self, count: usize) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        while names.len() < count {
            names.insert(self.name());
        }
        names
    }

    /// One to three names joined by '/'.
    fn path(&mut self) -> String {
        let names: Vec<String> = (0..=self.below(3)).map(|_| self.name()).collect();
        names.join("/")
    }

    /// A change path aimed at `view`: an entry, a child of one, a path under
    /// missing parents, or anywhere. It passes through a file or symlink only
    /// as a deliberate fault.
    fn change_path(&mut self, view: &View) -> String {
        let leaves: Vec<&str> = view
            .iter()
            .filter(|(path, (_, kind))| !path.is_empty() && *kind != ResolvedEntryKind::Directory)
            .map(|(path, _)| path.as_str())
            .collect();
        if !leaves.is_empty() && self.chance(FAULT) {
            return child(self.pick(&leaves), &self.name());
        }
        let paths: Vec<&str> = view.keys().map(String::as_str).chain([""]).collect();
        loop {
            let at = self.pick(&paths);
            let path = match self.below(4) {
                0 => at.to_owned(),
                1 => child(at, &self.name()),
                2 => child(&child(at, &self.name()), &self.name()),
                _ => self.path(),
            };
            if !path.is_empty() && !crosses_leaf(view, &path) {
                return path;
            }
        }
    }
}

/// One random case: a package DAG put through the public API.
struct Case {
    rng: Rng,
    packages: PackageStore,
    content: ContentStore,
    docs: Docs,
    /// Packages generated so far, oldest first, with their naive evaluation cost.
    pool: Vec<(ContentId, usize)>,
}

impl Case {
    /// Leaves and compositions in random order. The root names every package
    /// nothing else references, so it reaches them all; half the time it then
    /// carries changes of its own.
    async fn build(&mut self) -> ContentId {
        for _ in 0..3 {
            self.leaf().await;
        }
        for _ in 0..5 + self.rng.below(30) {
            match self.rng.below(10) {
                0 | 1 => self.leaf().await,
                2..=4 => self.collection().await,
                _ => self.changes().await,
            };
        }
        let referenced: Vec<ContentId> = self.docs.values().flat_map(references).collect();
        let tops: Vec<ContentId> = self
            .pool
            .iter()
            .map(|&(id, _)| id)
            .filter(|id| !referenced.contains(id))
            .collect();
        let entries = self.rng.names(tops.len()).into_iter().zip(tops).collect();
        let root = self.put(PackageDocument::Collection { entries }).await;
        if self.rng.chance(50) {
            self.changes_over(root).await
        } else {
            root
        }
    }

    /// A symlink, or a file whose bytes are often shared with other files.
    async fn leaf(&mut self) -> ContentId {
        if self.rng.chance(25) {
            let target = format!("{}{}", self.rng.pick(&["", "../", "/"]), self.rng.path());
            return self.put(PackageDocument::Symlink { target }).await;
        }
        let bytes = if self.rng.chance(60) {
            format!("shared {}", self.rng.below(3))
        } else {
            format!("unique {}", self.rng.next())
        };
        let content = self.content.import_bytes(bytes.into_bytes()).await.unwrap();
        let executable = self.rng.chance(30);
        self.put(PackageDocument::File {
            content,
            executable,
        })
        .await
    }

    /// Up to four children, sometimes none, sometimes one child under two names.
    async fn collection(&mut self) -> ContentId {
        let mut budget = MAX_COST;
        let mut entries = BTreeMap::new();
        for _ in 0..self.rng.below(5) {
            if let Some(child) = self.pick(&mut budget, |_| true) {
                entries.insert(self.rng.name(), child);
            }
        }
        if let Some(&child) = entries.values().next()
            && self.rng.chance(40)
        {
            entries.insert(self.rng.name(), child);
        }
        self.put(PackageDocument::Collection { entries }).await
    }

    /// Changes over a folder-like base, or, as a fault, a file-like one.
    async fn changes(&mut self) -> ContentId {
        let file_like = self.rng.chance(FAULT);
        let mut budget = MAX_COST;
        let base = self.pick(&mut budget, |document| {
            file_like
                == matches!(
                    document,
                    PackageDocument::File { .. } | PackageDocument::Symlink { .. }
                )
        });
        match base {
            Some(base) => self.changes_over(base).await,
            None => self.collection().await,
        }
    }

    /// Up to four edits aimed at `base`'s own entries; their paths never overlap.
    async fn changes_over(&mut self, base: ContentId) -> ContentId {
        let view = reference(base, &self.docs).unwrap_or_default();
        let mut budget = MAX_COST;
        let mut changes = BTreeMap::<String, Option<ContentId>>::new();
        for _ in 0..self.rng.below(5) {
            let path = self.rng.change_path(&view);
            if !changes.keys().any(|key| overlaps(key, &path)) {
                let replacement = if self.rng.chance(30) {
                    None
                } else {
                    self.pick(&mut budget, |_| true)
                };
                changes.insert(path, replacement);
            }
        }
        self.put(PackageDocument::Changes { base, changes }).await
    }

    /// Put `document`, recording it and the cost of evaluating it naively.
    async fn put(&mut self, document: PackageDocument) -> ContentId {
        let id = self.packages.put(&document).await.unwrap();
        let cost = 1 + references(&document)
            .into_iter()
            .map(|child| self.cost(child))
            .sum::<usize>();
        if self.docs.insert(id.hash(), document).is_none() {
            self.pool.push((id, cost));
        }
        id
    }

    fn cost(&self, id: ContentId) -> usize {
        self.pool.iter().find(|(known, _)| *known == id).unwrap().1
    }

    /// A random earlier package that `wanted` accepts and `budget` covers,
    /// favoring recent ones. Its cost is charged to `budget`.
    fn pick(
        &mut self,
        budget: &mut usize,
        wanted: impl Fn(&PackageDocument) -> bool,
    ) -> Option<ContentId> {
        let fits: Vec<(ContentId, usize)> = self
            .pool
            .iter()
            .copied()
            .filter(|&(id, cost)| cost <= *budget && wanted(&self.docs[&id.hash()]))
            .collect();
        if fits.is_empty() {
            return None;
        }
        let (id, cost) = fits[self.rng.below(fits.len()).max(self.rng.below(fits.len()))];
        *budget -= cost;
        Some(id)
    }
}

/// The packages a document names directly.
fn references(document: &PackageDocument) -> Vec<ContentId> {
    match document {
        PackageDocument::Collection { entries } => entries.values().copied().collect(),
        PackageDocument::Changes { base, changes } => std::iter::once(*base)
            .chain(changes.values().flatten().copied())
            .collect(),
        PackageDocument::File { .. } | PackageDocument::Symlink { .. } => Vec::new(),
    }
}

/// `name` inside `parent`, where the empty path is the root.
fn child(parent: &str, name: &str) -> String {
    if parent.is_empty() {
        name.to_owned()
    } else {
        format!("{parent}/{name}")
    }
}

/// Whether an existing proper ancestor of `path` is a file or symlink.
fn crosses_leaf(view: &View, path: &str) -> bool {
    ancestors(path).any(|parent| {
        view.get(parent)
            .is_some_and(|(_, kind)| *kind != ResolvedEntryKind::Directory)
    })
}

/// Whether two change paths are equal or one lies under the other.
fn overlaps(a: &str, b: &str) -> bool {
    a == b || ancestors(a).any(|parent| parent == b) || ancestors(b).any(|parent| parent == a)
}

// Coverage.

/// Every document reachable from `root`, each once.
fn reachable(root: ContentId, docs: &Docs) -> Vec<ContentId> {
    let mut found = Vec::new();
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !found.contains(&id) {
            found.push(id);
            stack.extend(references(&docs[&id.hash()]));
        }
    }
    found
}

/// The target shapes present in one resolved case whose view is `view`.
fn shapes(root: ContentId, docs: &Docs, view: &View) -> BTreeSet<&'static str> {
    use PackageDocument::{Changes, Collection, File, Symlink};
    let mut shapes = BTreeSet::new();
    let mut saves = HashMap::<Hash, usize>::new();
    let mut files = HashMap::<Hash, usize>::new();
    let holds_changes = |child: &ContentId| matches!(docs[&child.hash()], Changes { .. });
    for id in reachable(root, docs) {
        match &docs[&id.hash()] {
            File {
                content,
                executable,
            } => {
                *files.entry(content.hash()).or_default() += 1;
                if *executable {
                    shapes.insert("executable file");
                }
            }
            Symlink { .. } => {
                shapes.insert("symlink");
            }
            Collection { entries } => {
                if entries.is_empty() {
                    shapes.insert("empty folder");
                }
                if entries
                    .values()
                    .any(|a| entries.values().filter(|b| a == *b).count() > 1)
                {
                    shapes.insert("child under several names");
                }
            }
            Changes { base, changes } => {
                *saves.entry(base.hash()).or_default() += 1;
                match &docs[&base.hash()] {
                    Changes { .. } => {
                        shapes.insert("changes on changes");
                    }
                    Collection { entries } if entries.values().any(holds_changes) => {
                        shapes.insert("changes over a collection holding changes");
                    }
                    _ => {}
                }
                if changes.is_empty() {
                    shapes.insert("empty changes");
                }
                if changes.len() > 1 {
                    shapes.insert("several changes in one record");
                }
                let before = reference(*base, docs).unwrap();
                // A collection named twice: an edit under one name must not
                // show under the other.
                let repeated = |parent: &str| {
                    before.get(parent).is_some_and(|(package, _)| {
                        let mut places = before.values().filter(|(other, _)| other == package);
                        let twice = places.nth(1).is_some();
                        twice && matches!(docs[&package.hash()], Collection { .. })
                    })
                };
                for (path, replacement) in changes {
                    shapes.insert(match (before.get(path), replacement) {
                        (None, None) => "delete absent path",
                        (Some(_), None) => "delete entry",
                        (None, Some(_)) => "insert new path",
                        (Some((_, ResolvedEntryKind::Directory)), Some(_)) => "replace folder",
                        (Some(_), Some(_)) => "replace file or symlink",
                    });
                    if replacement.is_some()
                        && ancestors(path).any(|parent| !before.contains_key(parent))
                    {
                        shapes.insert("implicit folder");
                    }
                    if ancestors(path).any(repeated) {
                        shapes.insert("edit under a repeated folder");
                    }
                }
            }
        }
    }
    if saves.values().any(|&records| records > 1) {
        shapes.insert("shared base");
    }
    if files.values().any(|&documents| documents > 1) {
        shapes.insert("shared file content");
    }
    // A tree walk visits "a", "a/x", "a-b"; byte order is "a", "a-b", "a/x".
    let mut tree_order: Vec<&String> = view.keys().collect();
    tree_order.sort_by(|a, b| a.split('/').cmp(b.split('/')));
    if !tree_order.into_iter().eq(view.keys()) {
        shapes.insert("byte order differs from tree order");
    }
    shapes
}
