//! Immutable content packages, composed independently of workflow occurrences.
//!
//! A file package names bytes, a collection names member packages, and a changes
//! package applies path substitutions to another collection view. Retention
//! follows the entire representation, while access can follow only the resolved
//! visible entries. In particular, retaining a base does not grant its old files.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::content::{BlobFormat, ContentError, ContentId, ContentStore};
use ontography_calculus::Payload;

/// An immutable document stored as a raw content blob.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PackageDocument {
    /// A regular file backed by an immutable raw blob.
    File {
        /// Complete file bytes.
        content: ContentId,
        /// Executable intent, independent of host ownership and permissions.
        executable: bool,
    },
    /// A directory-like collection of named, recursively composable packages.
    Collection {
        /// Single-component names, ordered canonically by UTF-8 string ordering.
        #[serde(deserialize_with = "unique_map")]
        entries: BTreeMap<String, ContentId>,
    },
    /// Path substitutions applied to the resolved directory view of `base`.
    Changes {
        /// Immutable package whose current view supplies the baseline.
        base: ContentId,
        /// Replacement member packages; `None` deletes the path and its subtree.
        /// Ancestor/descendant keys in the same map are rejected as ambiguous.
        #[serde(deserialize_with = "unique_map")]
        changes: BTreeMap<String, Option<ContentId>>,
    },
    /// A symbolic link description; resolution does not follow its target.
    Symlink {
        /// Uninterpreted target. Filesystem materialization must enforce its own
        /// containment rules before exposing this link to a process.
        target: String,
    },
}

/// Explicit workflow-payload envelope naming a content package.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PackageEnvelope {
    /// The package document's immutable content identity.
    pub ontography_package: ContentId,
}

impl PackageEnvelope {
    /// Name a content package in an otherwise ordinary workflow payload.
    #[must_use]
    pub const fn new(ontography_package: ContentId) -> Self {
        Self { ontography_package }
    }

    /// Encode the explicit envelope as workflow payload bytes.
    ///
    /// # Errors
    /// Returns an error when JSON encoding fails.
    pub fn to_payload(self) -> Result<Payload, PackageError> {
        Ok(serde_json::to_vec(&self)?.into())
    }

    /// Recognize an explicit package envelope. Other payloads remain ordinary
    /// bytes; a malformed explicit envelope is an error rather than a fallback.
    ///
    /// # Errors
    /// Returns an error for a malformed explicit envelope or non-raw package ID.
    pub fn from_payload(payload: &Payload) -> Result<Option<Self>, PackageError> {
        let Ok(value) = serde_json::from_slice::<serde_json::Value>(payload) else {
            return Ok(None);
        };
        if value.get("ontography_package").is_none() {
            return Ok(None);
        }
        let envelope: Self = serde_json::from_slice(payload)?;
        require_raw(envelope.ontography_package)?;
        Ok(Some(envelope))
    }
}

/// Bounded document loading and visible-tree expansion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackageLimits {
    /// Maximum distinct package documents in the complete retention closure.
    pub max_packages: usize,
    /// Maximum package-reference depth, including stacked changes packages.
    pub max_depth: usize,
    /// Maximum entries in any resolved tree, including its root entry.
    pub max_entries: usize,
    /// Maximum bytes in one package document before decoding it.
    pub max_metadata_bytes: u64,
    /// Maximum document bytes plus expanded path and symlink-target bytes.
    /// Shared compositions must not amplify small documents into huge strings.
    pub max_total_metadata_bytes: u64,
    /// Maximum entries constructed across intermediate resolved trees. This
    /// bounds work and memory even when a small shared DAG expands repeatedly.
    pub max_expanded_entries: usize,
}

impl Default for PackageLimits {
    fn default() -> Self {
        Self {
            max_packages: 100_000,
            max_depth: 128,
            max_entries: 100_000,
            max_metadata_bytes: 16 * 1024 * 1024,
            max_total_metadata_bytes: 64 * 1024 * 1024,
            max_expanded_entries: 1_000_000,
        }
    }
}

/// A visible entry in the resolved view of one root package.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResolvedEntry {
    /// Canonical relative path. The empty string denotes the root itself.
    pub path: String,
    /// Package supplying this entry. Modified and implicit directories identify
    /// their changes package, so directory access must also bind root and path.
    pub package: ContentId,
    /// The current filesystem interpretation, without hidden base references.
    pub kind: ResolvedEntryKind,
}

/// Filesystem-neutral interpretation of one visible entry.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ResolvedEntryKind {
    /// A directory whose children come from this resolved view's paths.
    Directory,
    /// Current file bytes and executable intent.
    File {
        /// Immutable raw file content.
        content: ContentId,
        /// Whether the file is intended to be executable.
        executable: bool,
    },
    /// A link target, never followed during package resolution.
    Symlink {
        /// The recorded target string.
        target: String,
    },
}

/// An immutable composition's resolved current view and retention closure.
#[derive(Clone, Debug)]
pub struct ResolvedPackage {
    root: ContentId,
    entries: Vec<ResolvedEntry>,
    dependencies: Vec<ContentId>,
}

impl ResolvedPackage {
    /// Original content package identity, including any changes expression.
    #[must_use]
    pub const fn root(&self) -> ContentId {
        self.root
    }

    /// Visible entries ordered lexicographically by canonical path.
    #[must_use]
    pub fn entries(&self) -> &[ResolvedEntry] {
        &self.entries
    }

    /// Every representation dependency, including hidden bases and old bytes.
    /// Retention of this set is separate from granting access to its members.
    #[must_use]
    pub fn dependencies(&self) -> Vec<ContentId> {
        self.dependencies.clone()
    }

    /// Distinct package identities occurring in the current resolved view.
    /// Directory capabilities must still be bound to this root and their path:
    /// a modified directory can share its changes-package ID with another path.
    #[must_use]
    pub fn visible_packages(&self) -> Vec<ContentId> {
        unique_ids(self.entries.iter().map(|entry| entry.package))
    }
}

/// Invalid composition, exhausted limits, or content-store failure.
#[derive(Debug, Error)]
pub enum PackageError {
    /// Storage could not return the committed bytes.
    #[error(transparent)]
    Content(#[from] ContentError),
    /// A document or explicit envelope was not valid JSON of the required shape.
    #[error("invalid content package JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// Paths, entry relationships, or content formats are inconsistent.
    #[error("invalid content package: {0}")]
    Invalid(String),
    /// Resolution exceeded a configured finite bound.
    #[error("content package limit exceeded: {0}")]
    Limit(&'static str),
    /// A package-reference cycle was found while traversing the representation.
    #[error("content package reference cycle")]
    Cycle,
}

/// Immutable document operations over a shared content store.
#[derive(Clone, Debug)]
pub struct PackageStore {
    content: ContentStore,
    limits: PackageLimits,
}

impl PackageStore {
    /// Use the shared store with bounded default resolution limits.
    #[must_use]
    pub fn new(content: ContentStore) -> Self {
        Self {
            content,
            limits: PackageLimits::default(),
        }
    }

    /// Configure explicit resource bounds for subsequent operations.
    #[must_use]
    pub const fn with_limits(mut self, limits: PackageLimits) -> Self {
        self.limits = limits;
        self
    }

    /// Store a canonical document. This imports its own metadata, without
    /// creating a workflow activation or changing referenced packages.
    /// IDs commit to the exact serialized bytes, not JSON semantic equivalence.
    ///
    /// # Errors
    /// Returns invalid-document, metadata-limit, or content-storage errors.
    pub async fn put(&self, document: &PackageDocument) -> Result<ContentId, PackageError> {
        validate_document(document, self.limits)?;
        let bytes = serde_json::to_vec(document)?;
        if bytes.len() as u64 > self.limits.max_metadata_bytes {
            return Err(PackageError::Limit("document bytes"));
        }
        Ok(self.content.import_bytes(bytes).await?)
    }

    /// Read and validate one document without granting or resolving its children.
    /// Valid alternate JSON encodings are accepted; re-storing the returned
    /// document uses this implementation's canonical serialization and may
    /// therefore return a different content ID.
    ///
    /// # Errors
    /// Returns invalid-document, metadata-limit, or verified-content errors.
    pub async fn get(&self, id: ContentId) -> Result<PackageDocument, PackageError> {
        require_raw(id)?;
        if id.size() > self.limits.max_metadata_bytes {
            return Err(PackageError::Limit("document bytes"));
        }
        let bytes = self.content.read_range(id, 0..id.size()).await?;
        let document = serde_json::from_slice(&bytes)?;
        validate_document(&document, self.limits)?;
        Ok(document)
    }

    /// Resolve the current view while retaining knowledge of the full closure.
    ///
    /// # Errors
    /// Returns malformed composition, cycle, bound, or content-availability errors.
    pub async fn resolve(&self, root: ContentId) -> Result<ResolvedPackage, PackageError> {
        let loaded = self.load(root).await?;
        resolve_loaded(root, loaded, self.limits)
    }

    /// Inspect the complete representation closure without expanding its view.
    ///
    /// # Errors
    /// Returns invalid-document, cycle, bound, or content-availability errors.
    pub async fn dependencies(&self, root: ContentId) -> Result<Vec<ContentId>, PackageError> {
        Ok(self.load(root).await?.dependencies)
    }

    async fn load(&self, root: ContentId) -> Result<Loaded, PackageError> {
        let mut traversal = Traversal::new(root, self.limits);
        while let Some((id, depth)) = traversal.next()? {
            let document = self.get(id).await?;
            if let PackageDocument::File { content, .. } = &document
                && !self.content.metadata(*content).await?.complete
            {
                return Err(ContentError::Missing(content.hash()).into());
            }
            traversal.insert(id, depth, document);
        }
        Ok(traversal.finish())
    }
}

/// Validate one name in a package collection, without imposing Git or host-OS rules.
///
/// # Errors
/// Rejects empty, dot, traversal, separator, control, or overlong components.
pub fn validate_package_name(name: &str) -> Result<(), PackageError> {
    if name.is_empty()
        || name.len() > 255
        || matches!(name, "." | "..")
        || name.contains(['/', '\\', '\0'])
        || name.chars().any(char::is_control)
    {
        return Err(PackageError::Invalid(format!(
            "invalid member name {name:?}"
        )));
    }
    Ok(())
}

/// Validate a nonempty slash-separated path in a changes document.
///
/// # Errors
/// Rejects absolute, noncanonical, traversal, or overlong paths.
pub fn validate_package_path(path: &str) -> Result<(), PackageError> {
    if path.is_empty() || path.len() > 4096 {
        return Err(PackageError::Invalid(format!(
            "invalid relative path {path:?}"
        )));
    }
    path.split('/').try_for_each(validate_package_name)
}

type Key = ([u8; 32], u64);
type Tree = BTreeMap<String, (ContentId, ResolvedEntryKind)>;

fn key(id: ContentId) -> Key {
    (*id.hash().as_bytes(), id.size())
}

fn require_raw(id: ContentId) -> Result<(), PackageError> {
    if id.format() != BlobFormat::Raw {
        return Err(PackageError::Invalid(
            "package documents and file bytes must be raw blobs".into(),
        ));
    }
    Ok(())
}

fn unique_ids(ids: impl IntoIterator<Item = ContentId>) -> Vec<ContentId> {
    ids.into_iter()
        .map(|id| (key(id), id))
        .collect::<BTreeMap<_, _>>()
        .into_values()
        .collect()
}

fn validate_document(
    document: &PackageDocument,
    limits: PackageLimits,
) -> Result<(), PackageError> {
    match document {
        PackageDocument::File { content, .. } => require_raw(*content),
        PackageDocument::Collection { entries } => {
            if entries.len() >= limits.max_entries {
                return Err(PackageError::Limit("collection entries"));
            }
            for (name, id) in entries {
                validate_package_name(name)?;
                require_raw(*id)?;
            }
            Ok(())
        }
        PackageDocument::Changes { base, changes } => {
            require_raw(*base)?;
            if changes.len() > limits.max_entries {
                return Err(PackageError::Limit("changes entries"));
            }
            for (path, id) in changes {
                validate_package_path(path)?;
                if let Some(id) = id {
                    require_raw(*id)?;
                }
                let mut parent = path.as_str();
                while let Some((prefix, _)) = parent.rsplit_once('/') {
                    if changes.contains_key(prefix) {
                        return Err(PackageError::Invalid(format!(
                            "overlapping changes at {prefix:?} and {path:?}"
                        )));
                    }
                    parent = prefix;
                }
            }
            Ok(())
        }
        PackageDocument::Symlink { target } => {
            if target.is_empty() || target.len() > 4096 || target.chars().any(char::is_control) {
                return Err(PackageError::Invalid("invalid symlink target".into()));
            }
            Ok(())
        }
    }
}

fn references(document: &PackageDocument) -> Vec<ContentId> {
    match document {
        PackageDocument::Collection { entries } => entries.values().copied().collect(),
        PackageDocument::Changes { base, changes } => std::iter::once(*base)
            .chain(changes.values().flatten().copied())
            .collect(),
        PackageDocument::File { .. } | PackageDocument::Symlink { .. } => Vec::new(),
    }
}

enum Visit {
    Enter(ContentId, usize),
    Exit(ContentId),
}

struct Loaded {
    documents: BTreeMap<Key, PackageDocument>,
    order: Vec<ContentId>,
    dependencies: Vec<ContentId>,
}

struct Traversal {
    limits: PackageLimits,
    pending: Vec<Visit>,
    heights: BTreeMap<Key, usize>,
    loaded: Loaded,
    bytes: u64,
}

impl Traversal {
    fn new(root: ContentId, limits: PackageLimits) -> Self {
        Self {
            limits,
            pending: vec![Visit::Enter(root, 0)],
            heights: BTreeMap::new(),
            loaded: Loaded {
                documents: BTreeMap::new(),
                order: Vec::new(),
                dependencies: Vec::new(),
            },
            bytes: 0,
        }
    }

    fn next(&mut self) -> Result<Option<(ContentId, usize)>, PackageError> {
        while let Some(visit) = self.pending.pop() {
            match visit {
                Visit::Exit(id) => {
                    // Cached shared subtrees still contribute their full height
                    // when reached through a deeper branch of the DAG.
                    let height = references(&self.loaded.documents[&key(id)])
                        .iter()
                        .map(|child| self.heights[&key(*child)] + 1)
                        .max()
                        .unwrap_or(0);
                    if height > self.limits.max_depth {
                        return Err(PackageError::Limit("reference depth"));
                    }
                    self.heights.insert(key(id), height);
                    self.loaded.order.push(id);
                }
                Visit::Enter(id, depth) => {
                    if depth > self.limits.max_depth {
                        return Err(PackageError::Limit("reference depth"));
                    }
                    if self.heights.contains_key(&key(id)) {
                        continue;
                    }
                    // A loaded document without a completed height is an
                    // ancestor on the current DFS path, not a second state set.
                    if self.loaded.documents.contains_key(&key(id)) {
                        return Err(PackageError::Cycle);
                    }
                    if self.loaded.documents.len() >= self.limits.max_packages {
                        return Err(PackageError::Limit("package documents"));
                    }
                    self.bytes = self
                        .bytes
                        .checked_add(id.size())
                        .ok_or(PackageError::Limit("total document bytes"))?;
                    if self.bytes > self.limits.max_total_metadata_bytes {
                        return Err(PackageError::Limit("total document bytes"));
                    }
                    return Ok(Some((id, depth)));
                }
            }
        }
        Ok(None)
    }

    fn insert(&mut self, id: ContentId, depth: usize, document: PackageDocument) {
        self.pending.push(Visit::Exit(id));
        for child in references(&document).into_iter().rev() {
            self.pending.push(Visit::Enter(child, depth + 1));
        }
        self.loaded.dependencies.push(id);
        if let PackageDocument::File { content, .. } = &document {
            self.loaded.dependencies.push(*content);
        }
        self.loaded.documents.insert(key(id), document);
    }

    fn finish(mut self) -> Loaded {
        self.loaded.dependencies = unique_ids(self.loaded.dependencies);
        self.loaded
    }
}

struct ExpansionBudget {
    limits: PackageLimits,
    entries: usize,
    bytes: u64,
}

impl ExpansionBudget {
    fn entry(&mut self, path_bytes: usize, kind: &ResolvedEntryKind) -> Result<(), PackageError> {
        self.entries = self.entries.saturating_add(1);
        if self.entries > self.limits.max_expanded_entries {
            return Err(PackageError::Limit("expanded entries"));
        }
        let target_bytes = match kind {
            ResolvedEntryKind::Symlink { target } => target.len(),
            _ => 0,
        };
        self.bytes = self
            .bytes
            .saturating_add(path_bytes as u64)
            .saturating_add(target_bytes as u64);
        if self.bytes > self.limits.max_total_metadata_bytes {
            return Err(PackageError::Limit("expanded metadata bytes"));
        }
        Ok(())
    }
}

fn resolve_loaded(
    root: ContentId,
    loaded: Loaded,
    limits: PackageLimits,
) -> Result<ResolvedPackage, PackageError> {
    let mut trees = BTreeMap::<Key, Tree>::new();
    let mut budget = ExpansionBudget {
        limits,
        entries: 0,
        bytes: loaded.order.iter().map(|id| id.size()).sum(),
    };
    for id in &loaded.order {
        let mut tree = match &loaded.documents[&key(*id)] {
            PackageDocument::File {
                content,
                executable,
            } => singleton(
                *id,
                ResolvedEntryKind::File {
                    content: *content,
                    executable: *executable,
                },
                &mut budget,
            )?,
            PackageDocument::Symlink { target } => singleton(
                *id,
                ResolvedEntryKind::Symlink {
                    target: target.clone(),
                },
                &mut budget,
            )?,
            PackageDocument::Collection { entries } => {
                let mut tree = singleton(*id, ResolvedEntryKind::Directory, &mut budget)?;
                for (name, child) in entries {
                    insert_tree(&mut tree, name, &trees[&key(*child)], &mut budget)?;
                }
                tree
            }
            PackageDocument::Changes { base, changes } => {
                let base = &trees[&key(*base)];
                if !matches!(base.get(""), Some((_, ResolvedEntryKind::Directory))) {
                    return Err(PackageError::Invalid(
                        "changes require a directory-like base".into(),
                    ));
                }
                for (path, (_, kind)) in base {
                    budget.entry(path.len(), kind)?;
                }
                let mut tree = base.clone();
                for (path, replacement) in changes {
                    let changed = remove_tree(&mut tree, path) || replacement.is_some();
                    update_parents(
                        &mut tree,
                        path,
                        *id,
                        replacement.is_some(),
                        changed,
                        &mut budget,
                    )?;
                    if let Some(replacement) = replacement {
                        insert_tree(&mut tree, path, &trees[&key(*replacement)], &mut budget)?;
                    }
                }
                tree
            }
        };
        if tree.len() > limits.max_entries {
            return Err(PackageError::Limit("visible entries"));
        }
        tree.get_mut("").expect("resolved root").0 = *id;
        trees.insert(key(*id), tree);
    }
    Ok(ResolvedPackage {
        root,
        entries: trees
            .remove(&key(root))
            .expect("loaded root")
            .into_iter()
            .map(|(path, (package, kind))| ResolvedEntry {
                path,
                package,
                kind,
            })
            .collect(),
        dependencies: loaded.dependencies,
    })
}

fn singleton(
    package: ContentId,
    kind: ResolvedEntryKind,
    budget: &mut ExpansionBudget,
) -> Result<Tree, PackageError> {
    budget.entry(0, &kind)?;
    Ok(BTreeMap::from([(String::new(), (package, kind))]))
}

fn insert_tree(
    tree: &mut Tree,
    prefix: &str,
    child: &Tree,
    budget: &mut ExpansionBudget,
) -> Result<(), PackageError> {
    if tree
        .len()
        .checked_add(child.len())
        .is_none_or(|count| count > budget.limits.max_entries)
    {
        return Err(PackageError::Limit("visible entries"));
    }
    for (path, (package, kind)) in child {
        let length = prefix.len() + path.len() + usize::from(!path.is_empty());
        budget.entry(length, kind)?;
        let path = if path.is_empty() {
            prefix.to_owned()
        } else {
            format!("{prefix}/{path}")
        };
        validate_package_path(&path)?;
        tree.insert(path, (*package, kind.clone()));
    }
    Ok(())
}

/// Touch only the affected subtree, instead of scanning every entry for each edit.
pub(crate) fn remove_tree<T>(tree: &mut BTreeMap<String, T>, path: &str) -> bool {
    let descendants = descendants(tree, path)
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    let changed = tree.remove(path).is_some() || !descendants.is_empty();
    for child in descendants {
        tree.remove(&child);
    }
    changed
}

/// Canonical descendants in path order, excluding the named root itself.
pub fn descendants<'a, T>(
    tree: &'a BTreeMap<String, T>,
    root: &str,
) -> std::collections::btree_map::Range<'a, String, T> {
    use std::ops::Bound::{Excluded, Included, Unbounded};
    // '/' is immediately before '0', so the upper bound excludes every neighbor.
    tree.range(if root.is_empty() {
        (Excluded(String::new()), Unbounded)
    } else {
        (Included(format!("{root}/")), Excluded(format!("{root}0")))
    })
}

fn update_parents(
    tree: &mut Tree,
    path: &str,
    package: ContentId,
    create: bool,
    changed: bool,
    budget: &mut ExpansionBudget,
) -> Result<(), PackageError> {
    let mut child = path;
    while let Some((parent, _)) = child.rsplit_once('/') {
        match tree.get_mut(parent) {
            Some((_, kind)) if *kind != ResolvedEntryKind::Directory => {
                return Err(PackageError::Invalid(format!(
                    "change path traverses a non-directory at {parent:?}"
                )));
            }
            Some((id, _)) if changed => *id = package,
            None if create => {
                if tree.len() >= budget.limits.max_entries {
                    return Err(PackageError::Limit("visible entries"));
                }
                budget.entry(parent.len(), &ResolvedEntryKind::Directory)?;
                tree.insert(parent.to_owned(), (package, ResolvedEntryKind::Directory));
            }
            _ => {}
        }
        child = parent;
    }
    Ok(())
}

fn unique_map<'de, D, T>(deserializer: D) -> Result<BTreeMap<String, T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct Visitor<T>(std::marker::PhantomData<T>);
    impl<'de, T: Deserialize<'de>> serde::de::Visitor<'de> for Visitor<T> {
        type Value = BTreeMap<String, T>;
        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("a map of distinct package paths")
        }
        fn visit_map<M: serde::de::MapAccess<'de>>(
            self,
            mut map: M,
        ) -> Result<Self::Value, M::Error> {
            let mut values = BTreeMap::new();
            while let Some((name, value)) = map.next_entry::<String, T>()? {
                if values.insert(name, value).is_some() {
                    return Err(serde::de::Error::custom("duplicate package path"));
                }
            }
            Ok(values)
        }
    }
    deserializer.deserialize_map(Visitor(std::marker::PhantomData))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traversal_rejects_cycles_without_confusing_shared_dag_edges() {
        // Real content hashes make constructing a self-reference infeasible.
        // Exercise the graph walker directly with symbolic IDs instead.
        let id: ContentId = serde_json::from_value(
            serde_json::json!({"hash":"00".repeat(32),"format":"Raw","size":1}),
        )
        .unwrap();
        let mut traversal = Traversal::new(id, PackageLimits::default());
        assert!(traversal.next().unwrap().is_some());
        traversal.insert(
            id,
            0,
            PackageDocument::Changes {
                base: id,
                changes: BTreeMap::new(),
            },
        );
        assert!(matches!(traversal.next(), Err(PackageError::Cycle)));
    }
}
