//! Content-addressed local artifacts and verified access to retained payloads.
//!
//! Imports are retained by an artifact tag; ledger payload tags are a separate,
//! protected namespace. Cloned handles and readers keep storage alive
//! independently of the runtime session that produced them.

use std::collections::HashSet;
use std::future::Future;
use std::io::{self, SeekFrom};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};

use bao_tree::{ChunkNum, ChunkRanges};
use bytes::Bytes;
use futures_lite::{Stream, StreamExt};
use iroh_blobs::HashAndFormat;
use iroh_blobs::api::blobs::EncodedItem;
use iroh_blobs::api::proto::BlobStatus;
use iroh_blobs::api::{Store, TempTag};
use iroh_blobs::store::fs::options::Options;
pub use iroh_blobs::{BlobFormat, Hash};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;
use tokio::io::{AsyncRead, AsyncSeek, AsyncWriteExt, ReadBuf};

use ontography_calculus::ContentDigest;

/// Native integrity commitment plus format and expected complete byte length.
/// Deserializing an ID asserts trust in its hash, just like accepting a digest;
/// every read verifies the selected bytes against that hash.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ContentId {
    hash: Hash,
    format: BlobFormat,
    size: u64,
}

impl ContentId {
    /// BLAKE3 root used to verify complete content and byte ranges.
    #[must_use]
    pub const fn hash(self) -> Hash {
        self.hash
    }
    /// Declared blob format. Only raw blobs are imported, retained or verified.
    #[must_use]
    pub const fn format(self) -> BlobFormat {
        self.format
    }
    /// Expected complete length of the root blob, in bytes.
    #[must_use]
    pub const fn size(self) -> u64 {
        self.size
    }
}

/// Local availability of a content commitment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContentMetadata {
    /// Content identity whose local availability was inspected.
    pub id: ContentId,
    /// Whether every byte is available locally.
    pub complete: bool,
}

/// Failure to import, verify, read, or retain content.
#[derive(Debug, Error)]
pub enum ContentError {
    /// A local filesystem or streaming operation failed.
    #[error("content I/O failed: {0}")]
    Io(#[from] io::Error),
    /// The underlying blob store rejected an operation.
    #[error("content store failed: {0}")]
    Backend(String),
    /// The requested content is absent or not yet complete.
    #[error("content {0} is missing or incomplete")]
    Missing(Hash),
    /// Bytes do not satisfy the domain-separated SHA-256 commitment.
    #[error("content does not match payload digest {0}")]
    DigestMismatch(ContentDigest),
    /// Byte bounds are reversed or exceed the expected complete length.
    #[error("range {start}..{end} is outside content of size {size}")]
    InvalidRange {
        /// Inclusive requested start offset.
        start: u64,
        /// Exclusive requested end offset.
        end: u64,
        /// Expected complete content size.
        size: u64,
    },
    /// A format or declared size is inconsistent.
    #[error("content has an invalid format or length")]
    InvalidFormat,
}

pub(super) fn backend_error(error: impl std::fmt::Display) -> ContentError {
    ContentError::Backend(error.to_string())
}

type Result<T> = std::result::Result<T, ContentError>;

/// Domain separator of the SHA-256 payload commitment. `ContentDigest::compute`
/// keeps its own copy private and needs the whole payload in memory, while
/// streaming verification folds Bao leaves incrementally; the unit test below
/// pins this spelling to `compute`.
pub(crate) const PAYLOAD_DOMAIN: &[u8] = b"ontography-payload/v1\0";

type ImportPins = Arc<tokio::sync::Mutex<Vec<(ContentId, TempTag)>>>;

/// Cloneable access to the session's iroh store, without holding a session lock.
#[derive(Clone)]
pub struct ContentStore {
    pub(super) native: Store,
    pub(super) options: Option<Arc<Options>>,
    pub(super) _owner: Arc<dyn Send + Sync>,
    pub(super) gate: Arc<tokio::sync::Mutex<()>>,
    pub(super) runtime: tokio::runtime::Handle,
    imports: Option<ImportPins>,
}

/// Imports pinned only for the lifetime of this batch and its store handles.
///
/// Dropping an unretained batch makes its new bytes collectable without
/// touching another caller's artifact or ledger tags. Successful callers
/// explicitly retain the batch after validation and policy checks.
pub struct StagedImports {
    content: ContentStore,
    pins: ImportPins,
}

impl StagedImports {
    /// Returns a store whose imports belong to this batch.
    #[must_use]
    pub fn store(&self) -> ContentStore {
        self.content.clone()
    }

    /// Pins existing dependencies for the batch's lifetime. Retaining the
    /// batch also retains these dependencies as artifacts.
    ///
    /// # Errors
    /// Reports missing or invalid content and storage failures.
    pub async fn protect(&self, ids: &[ContentId]) -> Result<()> {
        let pins = self.content.protect_content(ids).await?;
        self.pins.lock().await.extend(ids.iter().copied().zip(pins));
        Ok(())
    }

    /// Durably retains this batch's imports as ordinary artifacts.
    ///
    /// # Errors
    /// Reports verification, durability, or tag publication failures.
    pub async fn retain(self) -> Result<()> {
        let pins = self.pins;
        self.content
            .detached(move |store| async move {
                let _guard = store.gate.lock().await;
                let imports = pins.lock().await;
                for (id, _) in imports.iter() {
                    store.fence(*id).await?;
                    store
                        .native
                        .tags()
                        .set(
                            tags::artifact(id.hash, id.format),
                            HashAndFormat::new(id.hash, id.format),
                        )
                        .await
                        .map_err(backend_error)?;
                }
                store.native.sync_db().await.map_err(backend_error)
            })
            .await
    }
}

impl std::fmt::Debug for ContentStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContentStore")
            .field("persistent", &self.options.is_some())
            .finish_non_exhaustive()
    }
}

impl ContentStore {
    /// Wraps the native iroh store that an object-store worker owns.
    ///
    /// `owner` keeps that worker alive while any clone of the handle or any
    /// reader derived from it exists, `gate` serializes durable publication
    /// with garbage collection, and `runtime` is the worker's runtime, on which
    /// the store's background tasks run.
    #[must_use]
    pub fn new(
        native: Store,
        options: Option<Arc<Options>>,
        owner: Arc<dyn Send + Sync>,
        gate: Arc<tokio::sync::Mutex<()>>,
        runtime: tokio::runtime::Handle,
    ) -> Self {
        Self {
            native,
            options,
            _owner: owner,
            gate,
            runtime,
            imports: None,
        }
    }

    /// Starts an isolated import batch. Imports remain pinned until its
    /// handles are dropped, and become durable artifacts only on `retain`.
    #[must_use]
    pub fn stage_imports(&self) -> StagedImports {
        let mut content = self.clone();
        let pins = Arc::new(tokio::sync::Mutex::new(Vec::new()));
        content.imports = Some(Arc::clone(&pins));
        StagedImports { content, pins }
    }

    /// Run one operation on an owned handle, independently of the caller's
    /// executor. Cancelling the caller aborts it and drops its staging guards.
    async fn detached<T, F>(&self, operation: impl FnOnce(Self) -> F) -> Result<T>
    where
        T: Send + 'static,
        F: Future<Output = Result<T>> + Send + 'static,
    {
        let mut task = AbortTask(self.runtime.spawn(operation(self.clone())));
        (&mut task.0).await.map_err(backend_error)?
    }

    /// Import owned bytes, retaining the result across restarts.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn import_bytes(&self, bytes: impl Into<Bytes>) -> Result<ContentId> {
        let bytes = bytes.into();
        self.detached(move |store| async move { store.import_bytes_inner(bytes).await })
            .await
    }

    async fn import_bytes_inner(&self, bytes: impl Into<Bytes>) -> Result<ContentId> {
        let tag = self
            .native
            .add_bytes(bytes)
            .temp_tag()
            .await
            .map_err(backend_error)?;
        let _guard = self.gate.lock().await;
        self.finish_import(tag.hash_and_format()).await
    }

    /// Resolve a graph payload's SHA-256 identity using complete, incremental verification.
    /// A modified digest tag is never accepted as a trusted native-hash mapping.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn resolve(&self, digest: ContentDigest) -> Result<Option<ContentId>> {
        self.detached(move |store| async move { store.resolve_inner(digest).await })
            .await
    }

    async fn resolve_inner(&self, digest: ContentDigest) -> Result<Option<ContentId>> {
        let tag = self
            .native
            .tags()
            .get(tags::ledger_payload(digest))
            .await
            .map_err(backend_error)?;
        let Some(tag) = tag else {
            return Ok(None);
        };
        if tag.format != BlobFormat::Raw {
            return Err(ContentError::DigestMismatch(digest));
        }
        let id = ContentId {
            hash: tag.hash,
            format: tag.format,
            size: self.complete_size(tag.hash).await?,
        };
        self.verify_digest(id, digest).await?;
        Ok(Some(id))
    }

    /// Size hint for applying allocation limits. This does not establish an
    /// integrity binding; use `resolve` before reading a digest by native hash.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>> {
        self.detached(move |store| async move { store.content_size_inner(digest).await })
            .await
    }

    async fn content_size_inner(&self, digest: ContentDigest) -> Result<Option<u64>> {
        if let Some(tag) = self
            .native
            .tags()
            .get(tags::ledger_payload(digest))
            .await
            .map_err(backend_error)?
        {
            if tag.format != BlobFormat::Raw {
                return Err(ContentError::DigestMismatch(digest));
            }
            return Ok(Some(self.complete_size(tag.hash).await?));
        }
        Ok(None)
    }

    /// Resolve a SHA-256 commitment and return a verified byte range.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn read_digest_range(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Bytes>> {
        self.detached(
            move |store| async move { store.read_digest_range_inner(digest, range).await },
        )
        .await
    }

    async fn read_digest_range_inner(
        &self,
        digest: ContentDigest,
        range: Range<u64>,
    ) -> Result<Option<Bytes>> {
        let Some(id) = self.resolve(digest).await? else {
            return Ok(None);
        };
        self.read_range(id, range).await.map(Some)
    }

    /// Resolve a SHA-256 commitment and create a verified seekable reader.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn digest_reader(&self, digest: ContentDigest) -> Result<Option<ContentReader>> {
        self.detached(move |store| async move { store.digest_reader_inner(digest).await })
            .await
    }

    async fn digest_reader_inner(&self, digest: ContentDigest) -> Result<Option<ContentReader>> {
        let Some(id) = self.resolve(digest).await? else {
            return Ok(None);
        };
        self.reader(id).await.map(Some)
    }

    /// Inspect availability and check the ID against the stored size.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn metadata(&self, id: ContentId) -> Result<ContentMetadata> {
        self.detached(move |store| async move { store.metadata_inner(id).await })
            .await
    }

    async fn metadata_inner(&self, id: ContentId) -> Result<ContentMetadata> {
        let status = self.native.status(id.hash).await.map_err(backend_error)?;
        match status {
            BlobStatus::NotFound => Err(ContentError::Missing(id.hash)),
            BlobStatus::Complete { size } | BlobStatus::Partial { size: Some(size) }
                if size != id.size =>
            {
                Err(ContentError::InvalidFormat)
            }
            BlobStatus::Complete { .. } => Ok(ContentMetadata { id, complete: true }),
            BlobStatus::Partial { .. } => {
                // A partial header is a consistency hint, not an authenticated
                // length until the final chunk has been verified.
                let bitfield = self.native.observe(id.hash).await.map_err(backend_error)?;
                if bitfield.total_bytes() != 0 && bitfield.size() != id.size {
                    return Err(ContentError::InvalidFormat);
                }
                Ok(ContentMetadata {
                    id,
                    complete: false,
                })
            }
        }
    }

    /// Read precisely this byte range using Bao-verified chunks. Working memory
    /// is the requested result plus bounded verification buffers.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn read_range(&self, id: ContentId, range: Range<u64>) -> Result<Bytes> {
        self.detached(move |store| async move { store.read_range_inner(id, range).await })
            .await
    }

    async fn read_range_inner(&self, id: ContentId, range: Range<u64>) -> Result<Bytes> {
        Self::check_range(id, &range)?;
        let _tag = self.protect(id).await?;
        let length =
            usize::try_from(range.end - range.start).map_err(|_| ContentError::InvalidFormat)?;
        let mut output = Vec::new();
        output
            .try_reserve_exact(length)
            .map_err(|e| ContentError::Backend(e.to_string()))?;
        if range.is_empty() {
            return Ok(output.into());
        }
        let chunks = ChunkRanges::from(
            ChunkNum::full_chunks(range.start)..ChunkNum::full_chunks(range.end - 1) + 1,
        );
        let mut stream = self.native.export_bao(id.hash, chunks).stream();
        let mut offset = range.start;
        while let Some(item) = stream.next().await {
            match item {
                EncodedItem::Leaf(leaf) => {
                    let start = usize::try_from(
                        offset
                            .checked_sub(leaf.offset)
                            .ok_or(ContentError::InvalidFormat)?,
                    )
                    .map_err(|_| ContentError::InvalidFormat)?;
                    let end =
                        usize::try_from((range.end - leaf.offset).min(leaf.data.len() as u64))
                            .map_err(|_| ContentError::InvalidFormat)?;
                    if start >= end {
                        return Err(ContentError::InvalidFormat);
                    }
                    output.extend_from_slice(&leaf.data[start..end]);
                    offset += (end - start) as u64;
                }
                EncodedItem::Error(error) => return Err(backend_error(error)),
                EncodedItem::Done => break,
                EncodedItem::Size(size) if size != id.size => {
                    return Err(ContentError::InvalidFormat);
                }
                EncodedItem::Parent(_) | EncodedItem::Size(_) => {}
            }
        }
        if offset != range.end {
            return Err(ContentError::InvalidFormat);
        }
        Ok(output.into())
    }

    /// A seekable asynchronous reader that verifies each block before delivery.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn reader(&self, id: ContentId) -> Result<ContentReader> {
        self.detached(move |store| async move { store.reader_inner(id).await })
            .await
    }

    async fn reader_inner(&self, id: ContentId) -> Result<ContentReader> {
        let tag = self.protect(id).await?;
        Ok(ContentReader {
            store: self.clone(),
            id,
            _tag: tag,
            position: 0,
            buffer: Bytes::new(),
            stream: None,
        })
    }

    /// Export verified bytes into a new file. Existing destinations are never
    /// overwritten, and a failed export removes its partial output.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn export_file(&self, id: ContentId, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref().to_path_buf();
        self.detached(move |store| async move { store.export_file_inner(id, path).await })
            .await
    }

    async fn export_file_inner(&self, id: ContentId, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let temporary = PartialExport::new(
            parent.join(format!(".ontography-export-{}.tmp", uuid::Uuid::new_v4())),
        );
        let mut reader = self.reader(id).await?;
        let mut file = tokio::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(temporary.path())
            .await?;
        tokio::io::copy(&mut reader, &mut file).await?;
        file.flush().await?;
        file.sync_all().await?;
        // Publishing only after complete verification also makes cancellation
        // safe: the guard removes the temporary file when this future drops.
        tokio::fs::hard_link(temporary.path(), path).await?;
        Ok(())
    }

    /// Reclaim untagged blobs and abandoned imports, preserving every tagged
    /// artifact and every committed history payload.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn collect_garbage(&self) -> Result<()> {
        self.detached(|store| async move { store.collect_garbage_inner().await })
            .await
    }

    // Only raw blobs carry this crate's tags, so the vendored marker's walk of
    // tags and temporary tags is complete on its own. Its lenient hash-sequence
    // traversal (warn, then sweep the children) cannot apply to anything this
    // crate retains, so no fail-fast pre-marking is needed before delegating.
    async fn collect_garbage_inner(&self) -> Result<()> {
        let _guard = self.gate.lock().await;
        iroh_blobs::store::gc_run_once(&self.native, &mut HashSet::new())
            .await
            .map_err(backend_error)
    }

    /// The native iroh store behind this handle.
    ///
    /// Retention is governed by the tags this crate writes; a caller that edits
    /// tags through the native store bypasses that governance. The runtime's
    /// object store uses it to exercise garbage collection in its tests.
    #[must_use]
    pub const fn native(&self) -> &Store {
        &self.native
    }

    /// Retains `ids` under the protected ledger namespace: each is verified
    /// complete once, fenced to disk, and tagged as both an artifact and a
    /// ledger artifact, and the database is synced once after the last tag.
    /// The object-store worker calls this when a committed ledger reference
    /// names imported content.
    ///
    /// # Errors
    ///
    /// Fails when an id is not a complete raw blob, or when the backend cannot
    /// fence, tag, or sync it.
    pub async fn retain_canonical(&self, ids: &[ContentId]) -> Result<()> {
        let _guard = self.gate.lock().await;
        for id in ids {
            self.verify_id(*id).await?;
            self.fence(*id).await?;
            let value = HashAndFormat::new(id.hash, id.format);
            for tag in [
                tags::artifact(id.hash, id.format),
                tags::ledger_artifact(id.hash, id.format),
            ] {
                self.native
                    .tags()
                    .set(tag, value)
                    .await
                    .map_err(backend_error)?;
            }
        }
        self.native.sync_db().await.map_err(backend_error)
    }

    /// Releases an explicitly imported artifact by deleting its artifact tag.
    ///
    /// The bytes become collectable unless committed ledger history retains
    /// them under the ledger namespace, which this never touches. The tag is
    /// per hash, so content imported twice is released by one call, and
    /// releasing an id that was never imported or was released already is
    /// not an error.
    ///
    /// # Errors
    ///
    /// Fails when the backend cannot delete the tag.
    pub async fn release(&self, id: ContentId) -> Result<()> {
        self.detached(move |store| async move { store.release_inner(id).await })
            .await
    }

    async fn release_inner(&self, id: ContentId) -> Result<()> {
        let _guard = self.gate.lock().await;
        self.native
            .tags()
            .delete(tags::artifact(id.hash, id.format))
            .await
            .map_err(backend_error)?;
        Ok(())
    }

    /// Verifies that every id names a complete raw blob and pins each one
    /// against garbage collection for as long as the returned tags live.
    ///
    /// # Errors
    ///
    /// Fails when an id is not a complete raw blob or the backend cannot pin it.
    pub async fn protect_content(&self, ids: &[ContentId]) -> Result<Vec<TempTag>> {
        let _guard = self.gate.lock().await;
        let mut pins = Vec::with_capacity(ids.len());
        for id in ids {
            self.verify_id(*id).await?;
            pins.push(
                self.native
                    .tags()
                    .temp_tag(HashAndFormat::new(id.hash, id.format))
                    .await
                    .map_err(backend_error)?,
            );
        }
        Ok(pins)
    }

    /// Verifies that every id names a complete raw blob, without retaining it
    /// beyond the check.
    ///
    /// # Errors
    ///
    /// Fails when an id is not a complete raw blob.
    pub async fn verify_content(&self, ids: &[ContentId]) -> Result<()> {
        let _pins = self.protect_content(ids).await?;
        Ok(())
    }

    /// Only raw blobs are retained or verified: this crate never composes hash
    /// sequences, so any other declared format is a malformed ID.
    async fn verify_id(&self, id: ContentId) -> Result<()> {
        if id.format != BlobFormat::Raw {
            return Err(ContentError::InvalidFormat);
        }
        if self
            .verify_complete(HashAndFormat::new(id.hash, id.format))
            .await?
            != id
        {
            return Err(ContentError::InvalidFormat);
        }
        Ok(())
    }

    pub(super) async fn finish_import(&self, value: HashAndFormat) -> Result<ContentId> {
        let id = self.verify_complete(value).await?;
        if let Some(imports) = &self.imports {
            let pin = self
                .native
                .tags()
                .temp_tag(value)
                .await
                .map_err(backend_error)?;
            imports.lock().await.push((id, pin));
            return Ok(id);
        }
        self.fence(id).await?;
        self.native
            .tags()
            .set(tags::artifact(id.hash, id.format), value)
            .await
            .map_err(backend_error)?;
        self.native.sync_db().await.map_err(backend_error)?;
        Ok(id)
    }

    pub(super) async fn fence(&self, id: ContentId) -> Result<()> {
        if let Some(options) = &self.options {
            let options = options.clone();
            tokio::task::spawn_blocking(move || {
                crate::durability::sync_verified(&options, id.hash, id.size)
            })
            .await
            .map_err(backend_error)??;
        }
        Ok(())
    }

    async fn verify_complete(&self, value: HashAndFormat) -> Result<ContentId> {
        let size = self.complete_size(value.hash).await?;
        let id = ContentId {
            hash: value.hash,
            format: value.format,
            size,
        };
        self.stream_verified(id, |_| {}).await?;
        Ok(id)
    }

    async fn verify_digest(&self, id: ContentId, digest: ContentDigest) -> Result<()> {
        let mut sha = Sha256::new();
        sha.update(PAYLOAD_DOMAIN);
        self.stream_verified(id, |leaf| sha.update(leaf)).await?;
        if ContentDigest::from_bytes(sha.finalize().into()) != digest {
            return Err(ContentError::DigestMismatch(digest));
        }
        Ok(())
    }

    /// Feed every Bao-verified leaf of a complete blob, in order, to `sink`.
    /// Bao verification and the SHA-256 payload commitment are separate
    /// concerns: only ledger digest checks fold the leaves into a hash.
    async fn stream_verified(&self, id: ContentId, mut sink: impl FnMut(&[u8])) -> Result<()> {
        if id.size == 0 && id.hash != Hash::EMPTY {
            return Err(ContentError::InvalidFormat);
        }
        let mut offset = 0;
        let mut stream = self.native.export_bao(id.hash, ChunkRanges::all()).stream();
        while let Some(item) = stream.next().await {
            match item {
                EncodedItem::Leaf(leaf) => {
                    if leaf.offset != offset {
                        return Err(ContentError::InvalidFormat);
                    }
                    sink(&leaf.data);
                    offset += leaf.data.len() as u64;
                }
                EncodedItem::Error(error) => return Err(backend_error(error)),
                EncodedItem::Done => break,
                EncodedItem::Size(_) | EncodedItem::Parent(_) => {}
            }
        }
        if offset != id.size {
            return Err(ContentError::InvalidFormat);
        }
        Ok(())
    }

    async fn complete_size(&self, hash: Hash) -> Result<u64> {
        match self.native.status(hash).await.map_err(backend_error)? {
            BlobStatus::Complete { size } => Ok(size),
            _ => Err(ContentError::Missing(hash)),
        }
    }

    async fn protect(&self, id: ContentId) -> Result<TempTag> {
        let _guard = self.gate.lock().await;
        match self.native.status(id.hash).await.map_err(backend_error)? {
            BlobStatus::Complete { size } | BlobStatus::Partial { size: Some(size) }
                if size == id.size => {}
            BlobStatus::Partial { size: None } => {}
            BlobStatus::NotFound => return Err(ContentError::Missing(id.hash)),
            _ => return Err(ContentError::InvalidFormat),
        }
        if id.size == 0 && id.hash != Hash::EMPTY {
            return Err(ContentError::InvalidFormat);
        }
        self.native
            .tags()
            .temp_tag(HashAndFormat::new(id.hash, id.format))
            .await
            .map_err(backend_error)
    }

    fn check_range(id: ContentId, range: &Range<u64>) -> Result<()> {
        if range.start > range.end || range.end > id.size {
            return Err(ContentError::InvalidRange {
                start: range.start,
                end: range.end,
                size: id.size,
            });
        }
        Ok(())
    }
}

/// Tag namespaces in the shared iroh store, one function per namespace.
///
/// A tag's bytes name exactly one retention purpose, so namespaces must never
/// collide: ledger payload tags are exactly the 32 digest bytes, and every
/// other namespace is a longer string under a distinct prefix. These spellings
/// are persisted; changing one silently orphans every existing tag.
pub mod tags {
    use iroh_blobs::{BlobFormat, Hash};

    use ontography_calculus::ContentDigest;

    fn format_code(format: BlobFormat) -> u8 {
        u8::from(format != BlobFormat::Raw)
    }

    /// Retention of an explicitly imported artifact until it is released.
    #[must_use]
    pub fn artifact(hash: Hash, format: BlobFormat) -> String {
        format!("ontography-artifact:{hash}:{}", format_code(format))
    }

    /// Protected retention of content referenced by committed ledger history.
    pub(crate) fn ledger_artifact(hash: Hash, format: BlobFormat) -> String {
        format!("ontography-ledger-artifact:{hash}:{}", format_code(format))
    }

    /// The raw blob holding a ledger payload, named by its SHA-256 commitment.
    #[must_use]
    pub fn ledger_payload(digest: ContentDigest) -> [u8; 32] {
        *digest.as_bytes()
    }
}

struct AbortTask<T>(tokio::task::JoinHandle<T>);
impl<T> Drop for AbortTask<T> {
    fn drop(&mut self) {
        self.0.abort();
    }
}

/// A staged export path, removed on drop so that an unpublished partial file
/// never outlives the operation that wrote it.
pub struct PartialExport(PathBuf);
impl PartialExport {
    /// Stages an export at `path`; the file is removed when the value drops.
    #[must_use]
    pub const fn new(path: PathBuf) -> Self {
        Self(path)
    }
    /// The staged path.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.0
    }
}
impl Drop for PartialExport {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

type VerifiedStream = Pin<Box<dyn Stream<Item = EncodedItem> + Send>>;

/// A bounded-buffer verified reader. Seeking never requires reading the skipped bytes.
pub struct ContentReader {
    store: ContentStore,
    id: ContentId,
    _tag: TempTag,
    position: u64,
    buffer: Bytes,
    stream: Option<VerifiedStream>,
}

impl AsyncRead for ContentReader {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        output: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        if output.remaining() == 0 || self.position >= self.id.size {
            return Poll::Ready(Ok(()));
        }
        if self.buffer.is_empty() {
            if self.stream.is_none() {
                let chunks = ChunkRanges::from(ChunkNum::full_chunks(self.position)..);
                self.stream = Some(Box::pin(
                    self.store.native.export_bao(self.id.hash, chunks).stream(),
                ));
            }
            loop {
                match self
                    .stream
                    .as_mut()
                    .expect("initialized stream")
                    .as_mut()
                    .poll_next(cx)
                {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(Some(EncodedItem::Leaf(leaf))) => {
                        let Some(start) = self
                            .position
                            .checked_sub(leaf.offset)
                            .and_then(|start| usize::try_from(start).ok())
                        else {
                            return Poll::Ready(Err(io::Error::other(
                                "invalid verified stream offset",
                            )));
                        };
                        if start >= leaf.data.len()
                            || leaf.offset + leaf.data.len() as u64 > self.id.size
                        {
                            return Poll::Ready(Err(io::Error::other(
                                "invalid verified stream length",
                            )));
                        }
                        self.buffer = leaf.data.slice(start..);
                        break;
                    }
                    Poll::Ready(Some(EncodedItem::Error(error))) => {
                        return Poll::Ready(Err(io::Error::other(error)));
                    }
                    Poll::Ready(Some(EncodedItem::Size(size))) if size != self.id.size => {
                        return Poll::Ready(Err(io::Error::other(
                            "verified stream size does not match content ID",
                        )));
                    }
                    Poll::Ready(Some(EncodedItem::Parent(_) | EncodedItem::Size(_))) => {}
                    Poll::Ready(Some(EncodedItem::Done) | None) => {
                        return Poll::Ready(Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "verified stream ended before expected length",
                        )));
                    }
                }
            }
        }
        let length = output.remaining().min(self.buffer.len());
        output.put_slice(&self.buffer.split_to(length));
        self.position += length as u64;
        Poll::Ready(Ok(()))
    }
}

impl AsyncSeek for ContentReader {
    fn start_seek(mut self: Pin<&mut Self>, position: SeekFrom) -> io::Result<()> {
        let offset = match position {
            SeekFrom::Start(value) => Some(value),
            SeekFrom::End(value) => self.id.size.checked_add_signed(value),
            SeekFrom::Current(value) => self.position.checked_add_signed(value),
        }
        .ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "seek offset outside u64 range")
        })?;
        self.position = offset;
        self.buffer = Bytes::new();
        self.stream = None;
        Ok(())
    }

    fn poll_complete(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<u64>> {
        Poll::Ready(Ok(self.position))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streaming_domain_matches_content_digest_compute() {
        let sample = b"payload sample with \0 and \xff bytes";
        let mut sha = Sha256::new();
        sha.update(PAYLOAD_DOMAIN);
        sha.update(sample);
        assert_eq!(
            ContentDigest::from_bytes(sha.finalize().into()),
            ContentDigest::compute(sample)
        );
    }

    #[test]
    fn tag_namespaces_cannot_collide() {
        let hash = Hash::new(b"sample");
        let raw = tags::ledger_payload(ContentDigest::compute(b"sample"));
        assert_eq!(raw.len(), 32);
        let prefixes = ["ontography-artifact:", "ontography-ledger-artifact:"];
        let named = [
            tags::artifact(hash, BlobFormat::Raw),
            tags::ledger_artifact(hash, BlobFormat::Raw),
        ];
        for (index, (tag, prefix)) in named.iter().zip(prefixes).enumerate() {
            assert!(tag.starts_with(prefix));
            assert!(tag.len() > raw.len(), "a named tag could equal a raw tag");
            for (other, candidate) in prefixes.iter().enumerate() {
                assert!(index == other || !prefix.starts_with(candidate));
            }
        }
    }
}
