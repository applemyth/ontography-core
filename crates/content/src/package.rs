//! Immutable content packages, composed independently of workflow occurrences.
//!
//! A file package names bytes, a collection names member packages, and a changes
//! package applies path substitutions to another collection view. Retention
//! follows the entire representation, while access can follow only the resolved
//! visible entries. In particular, retaining a base does not grant its old files.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

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

/// Bounds on the two real costs of a view: its input, the documents read and
/// the work of evaluating them, and its output, the entries it makes visible.
/// Hosts choose them for their machine; nothing else limits a package.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackageLimits {
    /// Maximum distinct documents in the complete retention closure.
    pub max_documents: usize,
    /// Maximum bytes in one document before decoding it.
    pub max_document_bytes: u64,
    /// Maximum bytes evaluation may use: every document read, plus each
    /// directory a save creates or copies, charged when it does.
    pub max_evaluation_bytes: u64,
    /// Maximum entries in any resolved view, including its root entry. A small
    /// shared DAG can describe an exponentially large view; this refuses it
    /// from counts alone, before any path is written out.
    pub max_entries: usize,
    /// Maximum bytes of paths and symlink targets in any resolved view: what
    /// writing it out costs.
    pub max_view_bytes: u64,
}

impl Default for PackageLimits {
    fn default() -> Self {
        Self {
            max_documents: 100_000,
            max_document_bytes: 16 * 1024 * 1024,
            max_evaluation_bytes: 64 * 1024 * 1024,
            max_entries: 100_000,
            max_view_bytes: 64 * 1024 * 1024,
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

/// An immutable composition's current view and retention closure.
///
/// The view is one shared tree, evaluated once from the package's documents.
/// Cloning it is cheap, and every question about what the package holds is
/// answered from it, so no caller needs its own copy.
#[derive(Clone)]
pub struct ResolvedPackage {
    root: ContentId,
    tree: Arc<Node>,
    dependencies: Vec<ContentId>,
}

impl ResolvedPackage {
    /// Original content package identity, including any changes expression.
    #[must_use]
    pub const fn root(&self) -> ContentId {
        self.root
    }

    /// Visible entries, including the root, counted without writing out paths.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.tree.len()
    }

    /// Bytes of every visible path and symlink target: what writing the view
    /// out costs, known without doing it.
    #[must_use]
    pub fn view_bytes(&self) -> u64 {
        self.tree.bytes()
    }

    /// Visible entries ordered lexicographically by canonical path. This
    /// writes out every path; `entry` and `children` answer lookups directly.
    #[must_use]
    pub fn entries(&self) -> Vec<ResolvedEntry> {
        let mut entries = Vec::with_capacity(self.entry_count());
        let mut pending = vec![(String::new(), &self.tree)];
        while let Some((path, node)) = pending.pop() {
            if let Node::Dir(dir) = &**node {
                pending.extend(dir.children.iter().map(|(n, c)| (join(&path, n), c)));
            }
            entries.push(node.entry(path));
        }
        entries.sort_unstable_by(|a, b| a.path.cmp(&b.path));
        entries
    }

    /// The root entry, whose path is empty.
    #[must_use]
    pub fn root_entry(&self) -> ResolvedEntry {
        self.tree.entry(String::new())
    }

    /// The visible entry at `path`; the empty path names the root.
    #[must_use]
    pub fn entry(&self, path: &str) -> Option<ResolvedEntry> {
        self.node(path).map(|node| node.entry(path.to_owned()))
    }

    /// Immediate children of the directory at `path`, ordered by name.
    #[must_use]
    pub fn children(&self, path: &str) -> Option<Vec<ResolvedEntry>> {
        let Node::Dir(dir) = &**self.node(path)? else {
            return None;
        };
        Some(
            dir.children
                .iter()
                .map(|(name, child)| child.entry(join(path, name)))
                .collect(),
        )
    }

    /// The package whose own view is exactly the subtree at `path`. A
    /// directory changed by a save carries that save's ID, whose own view is
    /// the save's whole tree, so it has none: republishing that ID would
    /// expose files this view hides.
    #[must_use]
    pub fn republishable(&self, path: &str) -> Option<ContentId> {
        let node = self.node(path)?;
        node.own().then(|| node.package())
    }

    /// Whether `id` is republishable at some path of this view.
    #[must_use]
    pub fn publishes(&self, id: ContentId) -> bool {
        let mut pending = vec![&self.tree];
        while let Some(node) = pending.pop() {
            if node.own() && node.package() == id {
                return true;
            }
            if let Node::Dir(dir) = &**node {
                pending.extend(dir.children.values());
            }
        }
        false
    }

    /// Every representation dependency, including hidden bases and old bytes.
    /// Retention of this set is separate from granting access to its members.
    #[must_use]
    pub fn dependencies(&self) -> Vec<ContentId> {
        self.dependencies.clone()
    }

    fn node(&self, path: &str) -> Option<&Arc<Node>> {
        if path.is_empty() {
            return Some(&self.tree);
        }
        path.split('/')
            .try_fold(&self.tree, |node, name| match &**node {
                Node::Dir(dir) => dir.children.get(name),
                Node::Leaf(..) => None,
            })
    }
}

impl std::fmt::Debug for ResolvedPackage {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResolvedPackage")
            .field("root", &self.root)
            .field("entries", &self.entry_count())
            .finish_non_exhaustive()
    }
}

fn join(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}/{name}")
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
        if bytes.len() as u64 > self.limits.max_document_bytes {
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
        if id.size() > self.limits.max_document_bytes {
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
        while let Some(id) = traversal.next()? {
            let document = self.get(id).await?;
            if let PackageDocument::File { content, .. } = &document
                && !self.content.metadata(*content).await?.complete
            {
                return Err(ContentError::Missing(content.hash()).into());
            }
            traversal.insert(id, document);
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
    Enter(ContentId),
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
    finished: BTreeSet<Key>,
    loaded: Loaded,
    bytes: u64,
}

impl Traversal {
    fn new(root: ContentId, limits: PackageLimits) -> Self {
        Self {
            limits,
            pending: vec![Visit::Enter(root)],
            finished: BTreeSet::new(),
            loaded: Loaded {
                documents: BTreeMap::new(),
                order: Vec::new(),
                dependencies: Vec::new(),
            },
            bytes: 0,
        }
    }

    fn next(&mut self) -> Result<Option<ContentId>, PackageError> {
        while let Some(visit) = self.pending.pop() {
            match visit {
                Visit::Exit(id) => {
                    self.finished.insert(key(id));
                    self.loaded.order.push(id);
                }
                Visit::Enter(id) => {
                    if self.finished.contains(&key(id)) {
                        continue;
                    }
                    // A loaded document that has not finished is an ancestor
                    // on the current DFS path, not a second state set.
                    if self.loaded.documents.contains_key(&key(id)) {
                        return Err(PackageError::Cycle);
                    }
                    if self.loaded.documents.len() >= self.limits.max_documents {
                        return Err(PackageError::Limit("documents"));
                    }
                    self.bytes = self
                        .bytes
                        .checked_add(id.size())
                        .ok_or(PackageError::Limit("evaluation bytes"))?;
                    if self.bytes > self.limits.max_evaluation_bytes {
                        return Err(PackageError::Limit("evaluation bytes"));
                    }
                    return Ok(Some(id));
                }
            }
        }
        Ok(None)
    }

    fn insert(&mut self, id: ContentId, document: PackageDocument) {
        self.pending.push(Visit::Exit(id));
        for child in references(&document).into_iter().rev() {
            self.pending.push(Visit::Enter(child));
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

/// One entry of a view. Subtrees are shared, never copied, unless a save
/// writes through a directory that another document still uses.
#[derive(Clone)]
enum Node {
    /// A file or symlink: always exactly its own document's view.
    Leaf(ContentId, ResolvedEntryKind),
    Dir(Dir),
}

#[derive(Clone)]
struct Dir {
    /// Document supplying this directory: its collection, or the save that changed it.
    package: ContentId,
    /// Whether this directory is exactly its package's own view.
    own: bool,
    /// Visible entries in this subtree, itself included.
    len: usize,
    /// Bytes of every path and symlink target below this directory, relative
    /// to it: what writing the subtree out costs.
    bytes: u64,
    /// Longest relative path below this directory, in bytes.
    depth: usize,
    children: Arc<BTreeMap<String, Arc<Node>>>,
}

/// Longest relative path in any view: every visible path must stay a valid
/// change path, so a later save can still name it.
const MAX_PATH: usize = 4096;
/// Heap one map entry occupies besides its name.
const ENTRY_BYTES: u64 = size_of::<(String, Arc<Node>)>() as u64;
/// Heap the smallest map allocation takes: a std B-tree leaf holds 11 entries.
const LEAF_BYTES: u64 = 11 * ENTRY_BYTES;
/// Heap one node occupies behind its reference counts.
const NODE_BYTES: u64 = (size_of::<Node>() + 2 * size_of::<usize>()) as u64;
/// Heap one directory's map occupies behind its reference counts.
const MAP_BYTES: u64 = (size_of::<BTreeMap<String, Arc<Node>>>() + 2 * size_of::<usize>()) as u64;

impl Node {
    fn len(&self) -> usize {
        match self {
            Self::Leaf(..) => 1,
            Self::Dir(dir) => dir.len,
        }
    }

    fn bytes(&self) -> u64 {
        match self {
            Self::Leaf(_, ResolvedEntryKind::Symlink { target }) => target.len() as u64,
            Self::Leaf(..) => 0,
            Self::Dir(dir) => dir.bytes,
        }
    }

    fn package(&self) -> ContentId {
        match self {
            Self::Leaf(package, _) => *package,
            Self::Dir(dir) => dir.package,
        }
    }

    fn own(&self) -> bool {
        match self {
            Self::Leaf(..) => true,
            Self::Dir(dir) => dir.own,
        }
    }

    /// Longest path through this node when it is named `name`.
    fn span(&self, name: &str) -> usize {
        match self {
            Self::Dir(dir) if !dir.children.is_empty() => name.len() + 1 + dir.depth,
            _ => name.len(),
        }
    }

    /// Bytes this node adds to its parent's view when named `name`: the name
    /// on every entry here, a separator on each below, and its own bytes.
    fn weight(&self, name: &str) -> u64 {
        let len = self.len() as u64;
        len.saturating_mul(name.len() as u64)
            .saturating_add(len - 1)
            .saturating_add(self.bytes())
    }

    fn entry(&self, path: String) -> ResolvedEntry {
        let (package, kind) = match self {
            Self::Leaf(package, kind) => (*package, kind.clone()),
            Self::Dir(dir) => (dir.package, ResolvedEntryKind::Directory),
        };
        ResolvedEntry {
            path,
            package,
            kind,
        }
    }
}

impl Dir {
    fn new(package: ContentId, own: bool, children: BTreeMap<String, Arc<Node>>) -> Self {
        let mut dir = Self {
            package,
            own,
            len: 1,
            bytes: 0,
            depth: 0,
            children: Arc::default(),
        };
        for (name, child) in &children {
            dir.add(name, child);
        }
        dir.children = Arc::new(children);
        dir
    }

    /// Count `child`, named `name`, into this directory's totals.
    fn add(&mut self, name: &str, child: &Node) {
        self.len = self.len.saturating_add(child.len());
        self.bytes = self.bytes.saturating_add(child.weight(name));
        self.depth = self.depth.max(child.span(name));
    }

    /// Take `child`, named `name`, out of the totals; `settle` restores the depth.
    fn subtract(&mut self, name: &str, child: &Node) {
        self.len = self.len.saturating_sub(child.len());
        self.bytes = self.bytes.saturating_sub(child.weight(name));
    }

    /// After a child's longest path went from `old` to `new`, rescan only if
    /// it held this directory's longest path and got shorter. The rescan is
    /// charged like reading the directory again.
    fn settle(
        &mut self,
        old: Option<usize>,
        new: Option<usize>,
        budget: &mut Budget,
    ) -> Result<(), PackageError> {
        if old.is_some_and(|old| old == self.depth && new.is_none_or(|new| new < old)) {
            budget.charge(self.children.len() as u64 * ENTRY_BYTES)?;
            self.depth = self
                .children
                .iter()
                .map(|(name, child)| child.span(name))
                .max()
                .unwrap_or(0);
        }
        Ok(())
    }

    /// Children to change, copied first if another document still shares them.
    fn children_mut(
        &mut self,
        budget: &mut Budget,
    ) -> Result<&mut BTreeMap<String, Arc<Node>>, PackageError> {
        if Arc::strong_count(&self.children) > 1 {
            let entries = self.children.keys();
            let copied: u64 = entries.map(|name| name.len() as u64 + ENTRY_BYTES).sum();
            budget.charge(MAP_BYTES + LEAF_BYTES + copied)?;
        }
        Ok(Arc::make_mut(&mut self.children))
    }

    fn changed_by(&mut self, save: ContentId) {
        self.package = save;
        self.own = false;
    }
}

impl Drop for Dir {
    /// Only the path rule bounds nesting, so release subtrees with a loop:
    /// the default drop would recurse once per level.
    fn drop(&mut self) {
        let mut pending = Vec::new();
        release(&mut self.children, &mut pending);
        while let Some(node) = pending.pop() {
            if let Ok(Node::Dir(mut dir)) = Arc::try_unwrap(node) {
                release(&mut dir.children, &mut pending);
            }
        }
    }
}

/// Move out the children this directory alone owns; shared ones stay put.
fn release(children: &mut Arc<BTreeMap<String, Arc<Node>>>, pending: &mut Vec<Arc<Node>>) {
    if let Some(children) = Arc::get_mut(children) {
        pending.extend(std::mem::take(children).into_values());
    }
}

/// A directory to change in place. A shared node is copied first, which is
/// cheap because its children stay shared until they change too.
fn directory<'a>(
    node: &'a mut Arc<Node>,
    budget: &mut Budget,
) -> Result<&'a mut Dir, PackageError> {
    if Arc::strong_count(node) > 1 {
        budget.charge(NODE_BYTES)?;
    }
    match Arc::make_mut(node) {
        Node::Dir(dir) => Ok(dir),
        Node::Leaf(..) => unreachable!("changes only descend through directories"),
    }
}

/// Bytes evaluation has used: documents read, then whatever saves allocate.
struct Budget {
    spent: u64,
    limit: u64,
}

impl Budget {
    fn charge(&mut self, bytes: u64) -> Result<(), PackageError> {
        self.spent = self.spent.saturating_add(bytes);
        if self.spent > self.limit {
            return Err(PackageError::Limit("evaluation bytes"));
        }
        Ok(())
    }
}

/// Evaluated views awaiting their users. A view moves to its last user, so a
/// base that only one save uses changes in place instead of being copied.
struct Views {
    built: HashMap<Key, Arc<Node>>,
    uses: HashMap<Key, usize>,
}

impl Views {
    fn take(&mut self, id: ContentId) -> Arc<Node> {
        let key = key(id);
        let uses = self.uses.get_mut(&key).expect("counted reference");
        *uses -= 1;
        if *uses == 0 {
            self.built.remove(&key).expect("evaluated before its users")
        } else {
            Arc::clone(&self.built[&key])
        }
    }
}

/// A view within the output bounds, whose every path is still a valid change path.
fn check(node: &Node, limits: PackageLimits) -> Result<(), PackageError> {
    if node.len() > limits.max_entries {
        return Err(PackageError::Limit("visible entries"));
    }
    if node.bytes() > limits.max_view_bytes {
        return Err(PackageError::Limit("view bytes"));
    }
    if matches!(node, Node::Dir(dir) if dir.depth > MAX_PATH) {
        return Err(PackageError::Invalid(format!(
            "resolved paths exceed {MAX_PATH} bytes"
        )));
    }
    Ok(())
}

fn resolve_loaded(
    root: ContentId,
    loaded: Loaded,
    limits: PackageLimits,
) -> Result<ResolvedPackage, PackageError> {
    let mut budget = Budget {
        spent: loaded.order.iter().map(|id| id.size()).sum(),
        limit: limits.max_evaluation_bytes,
    };
    let mut views = Views {
        built: HashMap::new(),
        uses: HashMap::new(),
    };
    for document in loaded.documents.values() {
        for child in references(document) {
            *views.uses.entry(key(child)).or_default() += 1;
        }
    }
    for id in &loaded.order {
        let node = match &loaded.documents[&key(*id)] {
            PackageDocument::File {
                content,
                executable,
            } => Arc::new(Node::Leaf(
                *id,
                ResolvedEntryKind::File {
                    content: *content,
                    executable: *executable,
                },
            )),
            PackageDocument::Symlink { target } => Arc::new(Node::Leaf(
                *id,
                ResolvedEntryKind::Symlink {
                    target: target.clone(),
                },
            )),
            PackageDocument::Collection { entries } => {
                let children = entries
                    .iter()
                    .map(|(name, child)| (name.clone(), views.take(*child)))
                    .collect();
                Arc::new(Node::Dir(Dir::new(*id, true, children)))
            }
            PackageDocument::Changes { base, changes } => {
                let mut tree = views.take(*base);
                if !matches!(*tree, Node::Dir(_)) {
                    return Err(PackageError::Invalid(
                        "changes require a directory-like base".into(),
                    ));
                }
                for (path, replacement) in changes {
                    let replacement = replacement.map(|child| views.take(child));
                    tree = apply(tree, path, replacement, *id, &mut budget)?;
                    check(&tree, limits)?;
                }
                let top = directory(&mut tree, &mut budget)?;
                top.package = *id;
                top.own = true;
                tree
            }
        };
        check(&node, limits)?;
        views.built.insert(key(*id), node);
    }
    Ok(ResolvedPackage {
        root,
        tree: views.built.remove(&key(root)).expect("loaded root"),
        dependencies: loaded.dependencies,
    })
}

/// Replace or delete `path`, changing only the directories on its way. As
/// before, every directory on a changed path then identifies `save`, and
/// missing ones are created only to hold a replacement.
fn apply(
    tree: Arc<Node>,
    path: &str,
    replacement: Option<Arc<Node>>,
    save: ContentId,
    budget: &mut Budget,
) -> Result<Arc<Node>, PackageError> {
    if !changes_anything(&tree, path, replacement.is_some())? {
        return Ok(tree);
    }
    let (parents, name) = path.rsplit_once('/').unwrap_or(("", path));
    // Take each directory out of its parent, so a sole owner changes in place,
    // remembering the longest path it held there.
    let mut trail = Vec::new();
    let mut folder = tree;
    for part in parents.split('/').filter(|part| !part.is_empty()) {
        let dir = directory(&mut folder, budget)?;
        let (child, old) = if let Some(child) = dir.children_mut(budget)?.remove(part) {
            dir.subtract(part, &child);
            let old = child.span(part);
            (child, Some(old))
        } else {
            budget.charge(NODE_BYTES + MAP_BYTES + LEAF_BYTES + part.len() as u64)?;
            let created = Dir::new(save, false, BTreeMap::new());
            (Arc::new(Node::Dir(created)), None)
        };
        trail.push((folder, part, old));
        folder = child;
    }
    let dir = directory(&mut folder, budget)?;
    let removed = dir.children_mut(budget)?.remove(name);
    let old = removed.map(|node| {
        dir.subtract(name, &node);
        node.span(name)
    });
    let new = match replacement {
        Some(node) => {
            dir.add(name, &node);
            let span = node.span(name);
            dir.children_mut(budget)?.insert(name.to_owned(), node);
            Some(span)
        }
        None => None,
    };
    dir.settle(old, new, budget)?;
    dir.changed_by(save);
    while let Some((mut parent, part, old)) = trail.pop() {
        let dir = directory(&mut parent, budget)?;
        dir.add(part, &folder);
        let new = folder.span(part);
        dir.children_mut(budget)?.insert(part.to_owned(), folder);
        dir.settle(old, Some(new), budget)?;
        dir.changed_by(save);
        folder = parent;
    }
    Ok(folder)
}

/// Whether a change at `path` alters the tree. A path through a file is
/// invalid, even for a deletion that would otherwise do nothing.
fn changes_anything(tree: &Node, path: &str, inserting: bool) -> Result<bool, PackageError> {
    let mut node = tree;
    let mut start = 0_usize;
    for part in path.split('/') {
        let Node::Dir(dir) = node else {
            return Err(PackageError::Invalid(format!(
                "change path traverses a non-directory at {:?}",
                &path[..start.saturating_sub(1)]
            )));
        };
        let Some(child) = dir.children.get(part) else {
            return Ok(inserting);
        };
        start += part.len() + 1;
        node = child;
    }
    Ok(true)
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
            PackageDocument::Changes {
                base: id,
                changes: BTreeMap::new(),
            },
        );
        assert!(matches!(traversal.next(), Err(PackageError::Cycle)));
    }
}
