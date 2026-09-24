//! Content-addressed local artifacts and verified access to retained payloads.
//!
//! Imports retain their result until explicitly released. Ledger payload tags are
//! a separate, protected namespace. Cloned handles and readers keep storage alive
//! independently of the runtime session that produced them.

use std::collections::{BTreeSet, HashSet};
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
use iroh_blobs::api::blobs::{AddBytesOptions, EncodedItem};
use iroh_blobs::api::proto::BlobStatus;
use iroh_blobs::api::{Store, TempTag};
use iroh_blobs::format::collection::Collection;
use iroh_blobs::hashseq::HashSeq;
use iroh_blobs::store::fs::options::Options;
pub use iroh_blobs::{BlobFormat, Hash};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;
use tokio::io::{AsyncRead, AsyncSeek, AsyncWriteExt, ReadBuf};

use crate::ContentDigest;

pub mod network;

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
    /// Interpretation of the blob as raw bytes or a sequence of raw links.
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
    /// A format, child reference, or declared size is inconsistent.
    #[error("content has an invalid format or length")]
    InvalidFormat,
    /// A transfer was paused, retaining verified downloaded chunks.
    #[error("download cancelled; verified partial data retained")]
    Cancelled,
}

pub(super) fn backend_error(error: impl std::fmt::Display) -> ContentError {
    ContentError::Backend(error.to_string())
}

type Result<T> = std::result::Result<T, ContentError>;

/// Cloneable access to the session's iroh store, without holding a session lock.
#[derive(Clone)]
pub struct ContentStore {
    pub(super) native: Store,
    pub(super) options: Option<Arc<Options>>,
    pub(super) _owner: Arc<dyn Send + Sync>,
    pub(super) gate: Arc<tokio::sync::Mutex<()>>,
    pub(super) runtime: tokio::runtime::Handle,
}

impl std::fmt::Debug for ContentStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContentStore")
            .field("persistent", &self.options.is_some())
            .finish_non_exhaustive()
    }
}

impl ContentStore {
    pub(crate) fn new(
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
        }
    }

    /// Execute gate-held operations independently of the caller's executor.
    /// Cancelling the caller aborts the operation and drops staging guards.
    pub(super) async fn run<T: Send + 'static>(
        &self,
        future: impl Future<Output = Result<T>> + Send + 'static,
    ) -> Result<T> {
        let mut task = AbortTask(self.runtime.spawn(future));
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
        let store = self.clone();
        self.run(async move { store.import_bytes_inner(bytes).await })
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

    /// Copy a file into owned storage; the source may be changed or removed afterwards.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn import_file(&self, path: impl AsRef<Path>) -> Result<ContentId> {
        let path = path.as_ref().to_path_buf();
        let store = self.clone();
        self.run(async move { store.import_file_inner(path).await })
            .await
    }

    async fn import_file_inner(&self, path: impl AsRef<Path>) -> Result<ContentId> {
        let path = tokio::fs::canonicalize(path.as_ref()).await?;
        let tag = self
            .native
            .add_path(path)
            .temp_tag()
            .await
            .map_err(backend_error)?;
        let _guard = self.gate.lock().await;
        self.finish_import(tag.hash_and_format()).await
    }

    /// Import a bounded-buffer stream. Filesystem stores never collect the whole
    /// stream into application memory; ephemeral stores necessarily retain bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn import_stream(
        &self,
        stream: impl Stream<Item = io::Result<Bytes>> + Send + Sync + 'static,
    ) -> Result<ContentId> {
        let store = self.clone();
        self.run(async move { store.import_stream_inner(stream).await })
            .await
    }

    async fn import_stream_inner(
        &self,
        stream: impl Stream<Item = io::Result<Bytes>> + Send + Sync + 'static,
    ) -> Result<ContentId> {
        // iroh 0.103's sender/receiver join can hang when its input stream
        // yields an error without sending Done. Finish staging the prefix,
        // then discard its temporary root and return the original error.
        let failure = Arc::new(std::sync::Mutex::new(None));
        let stream = ImportStream {
            stream: Box::pin(stream),
            failure: failure.clone(),
            ended: false,
        };
        let tag = self
            .native
            .add_stream(stream)
            .await
            .temp_tag()
            .await
            .map_err(backend_error)?;
        if let Some(error) = failure
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
        {
            return Err(error.into());
        }
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
        let store = self.clone();
        self.run(async move { store.resolve_inner(digest).await })
            .await
    }

    async fn resolve_inner(&self, digest: ContentDigest) -> Result<Option<ContentId>> {
        let tag = self
            .native
            .tags()
            .get(digest.as_bytes())
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
        let store = self.clone();
        self.run(async move { store.content_size_inner(digest).await })
            .await
    }

    async fn content_size_inner(&self, digest: ContentDigest) -> Result<Option<u64>> {
        if let Some(tag) = self
            .native
            .tags()
            .get(digest.as_bytes())
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
        let store = self.clone();
        self.run(async move { store.read_digest_range_inner(digest, range).await })
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
        let store = self.clone();
        self.run(async move { store.digest_reader_inner(digest).await })
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
        let store = self.clone();
        self.run(async move { store.metadata_inner(id).await })
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
        let store = self.clone();
        self.run(async move { store.read_range_inner(id, range).await })
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
        let store = self.clone();
        self.run(async move { store.reader_inner(id).await }).await
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
        let store = self.clone();
        self.run(async move { store.export_file_inner(id, path).await })
            .await
    }

    async fn export_file_inner(&self, id: ContentId, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let temporary =
            PartialExport(parent.join(format!(".ontography-export-{}.tmp", uuid::Uuid::new_v4())));
        let mut reader = self.reader(id).await?;
        let mut file = tokio::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary.0)
            .await?;
        tokio::io::copy(&mut reader, &mut file).await?;
        file.flush().await?;
        file.sync_all().await?;
        // Publishing only after complete verification also makes cancellation
        // safe: the guard removes the temporary file when this future drops.
        tokio::fs::hard_link(&temporary.0, path).await?;
        Ok(())
    }

    /// Store an iroh hash sequence. Links refer to raw blobs, following iroh's
    /// one-level hash-sequence format; nested collections need explicit roots.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn import_hash_sequence(&self, children: &[ContentId]) -> Result<ContentId> {
        let children = children.to_vec();
        let store = self.clone();
        self.run(async move { store.import_hash_sequence_inner(&children).await })
            .await
    }

    async fn import_hash_sequence_inner(&self, children: &[ContentId]) -> Result<ContentId> {
        let _guard = self.gate.lock().await;
        for child in children {
            self.verify_id(*child, true).await?;
        }
        let bytes = children
            .iter()
            .map(|id| id.hash)
            .collect::<HashSeq>()
            .into_inner();
        let tag = self
            .native
            .add_bytes_with_opts(AddBytesOptions {
                data: bytes,
                format: BlobFormat::HashSeq,
            })
            .temp_tag()
            .await
            .map_err(backend_error)?;
        self.finish_import(tag.hash_and_format()).await
    }

    /// Verify a native hash-sequence root and return its ordered raw links.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn read_hash_sequence(&self, id: ContentId) -> Result<Vec<Hash>> {
        let store = self.clone();
        self.run(async move { store.read_hash_sequence_inner(id).await })
            .await
    }

    async fn read_hash_sequence_inner(&self, id: ContentId) -> Result<Vec<Hash>> {
        if id.format != BlobFormat::HashSeq {
            return Err(ContentError::InvalidFormat);
        }
        let _tag = self.protect(id).await?;
        let data = self
            .native
            .get_bytes(id.hash)
            .await
            .map_err(backend_error)?;
        if data.len() as u64 != id.size {
            return Err(ContentError::InvalidFormat);
        }
        Ok(HashSeq::try_from(data)
            .map_err(backend_error)?
            .iter()
            .collect())
    }

    /// Import a named file bundle using the native interoperable collection format.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn import_collection(
        &self,
        entries: impl IntoIterator<Item = (String, ContentId)>,
    ) -> Result<ContentId> {
        let entries: Vec<_> = entries.into_iter().collect();
        let store = self.clone();
        self.run(async move { store.import_collection_inner(entries).await })
            .await
    }

    async fn import_collection_inner(
        &self,
        entries: impl IntoIterator<Item = (String, ContentId)>,
    ) -> Result<ContentId> {
        let _guard = self.gate.lock().await;
        let mut names = BTreeSet::new();
        let mut collection = Collection::default();
        for (name, child) in entries {
            if !names.insert(name.clone()) {
                return Err(ContentError::InvalidFormat);
            }
            self.verify_id(child, true).await?;
            collection.push(name, child.hash);
        }
        let tag = collection
            .store(&self.native)
            .await
            .map_err(backend_error)?;
        self.finish_import(tag.hash_and_format()).await
    }

    /// Verify collection metadata and return its named raw content references.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn read_collection(&self, id: ContentId) -> Result<Vec<(String, ContentId)>> {
        let store = self.clone();
        self.run(async move { store.read_collection_inner(id).await })
            .await
    }

    async fn read_collection_inner(&self, id: ContentId) -> Result<Vec<(String, ContentId)>> {
        if id.format != BlobFormat::HashSeq {
            return Err(ContentError::InvalidFormat);
        }
        let _tag = self.protect(id).await?;
        if self.complete_size(id.hash).await? != id.size {
            return Err(ContentError::InvalidFormat);
        }
        let collection = Collection::load(id.hash, &self.native)
            .await
            .map_err(backend_error)?;
        let mut entries = Vec::with_capacity(collection.len());
        for (name, hash) in collection.iter() {
            entries.push((
                name.clone(),
                ContentId {
                    hash: *hash,
                    format: BlobFormat::Raw,
                    size: self.complete_size(*hash).await?,
                },
            ));
        }
        Ok(entries)
    }

    /// Retain imported content. Idempotent; retaining an existing ID verifies
    /// and fences the complete content before publishing the persistent tag.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn retain(&self, id: ContentId) -> Result<()> {
        let store = self.clone();
        self.run(async move { store.retain_inner(id).await }).await
    }

    async fn retain_inner(&self, id: ContentId) -> Result<()> {
        let _guard = self.gate.lock().await;
        self.verify_id(id, false).await?;
        self.finish_import(HashAndFormat::new(id.hash, id.format))
            .await?;
        Ok(())
    }

    /// Release only the artifact retention tag. Ledger tags, active readers,
    /// transfers, and collections can continue retaining the same bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn release(&self, id: ContentId) -> Result<bool> {
        let store = self.clone();
        self.run(async move { store.release_inner(id).await }).await
    }

    async fn release_inner(&self, id: ContentId) -> Result<bool> {
        let _guard = self.gate.lock().await;
        let removed = self
            .native
            .tags()
            .delete(artifact_tag(id.hash, id.format))
            .await
            .map_err(backend_error)?;
        self.native.sync_db().await.map_err(backend_error)?;
        Ok(removed != 0)
    }

    /// Reclaim unretained artifacts and abandoned imports, preserving every
    /// committed history payload. Corrupt retention roots abort collection.
    ///
    /// # Errors
    ///
    /// Returns an error if storage fails, required content is unavailable,
    /// verification fails, or the supplied identity, format, or bounds are invalid.
    pub async fn collect_garbage(&self) -> Result<()> {
        let store = self.clone();
        self.run(async move { store.collect_garbage_inner().await })
            .await
    }

    async fn collect_garbage_inner(&self) -> Result<()> {
        let _guard = self.gate.lock().await;
        let mut live = HashSet::new();
        let mut tags = self.native.tags().list().await.map_err(backend_error)?;
        while let Some(tag) = tags.next().await {
            let tag = tag.map_err(backend_error)?;
            self.mark(tag.hash_and_format(), &mut live).await?;
        }
        let mut temporary = self
            .native
            .tags()
            .list_temp_tags()
            .await
            .map_err(backend_error)?;
        while let Some(tag) = temporary.next().await {
            self.mark(tag, &mut live).await?;
        }
        iroh_blobs::store::gc_run_once(&self.native, &mut live)
            .await
            .map_err(backend_error)
    }

    pub(crate) async fn retain_canonical(&self, ids: &[ContentId]) -> Result<()> {
        let _guard = self.gate.lock().await;
        for id in ids {
            self.verify_id(*id, false).await?;
            self.finish_import(HashAndFormat::new(id.hash, id.format))
                .await?;
            self.native
                .tags()
                .set(
                    format!(
                        "ontography-ledger-artifact:{}:{}",
                        id.hash,
                        format_code(id.format)
                    ),
                    HashAndFormat::new(id.hash, id.format),
                )
                .await
                .map_err(backend_error)?;
        }
        self.native.sync_db().await.map_err(backend_error)
    }

    pub(crate) async fn protect_content(&self, ids: &[ContentId]) -> Result<Vec<TempTag>> {
        let _guard = self.gate.lock().await;
        let mut pins = Vec::with_capacity(ids.len());
        for id in ids {
            self.verify_id(*id, false).await?;
            if id.format == BlobFormat::HashSeq {
                let data = self
                    .native
                    .get_bytes(id.hash)
                    .await
                    .map_err(backend_error)?;
                for hash in HashSeq::try_from(data).map_err(backend_error)?.iter() {
                    self.verify_complete(HashAndFormat::new(hash, BlobFormat::Raw))
                        .await?;
                }
            }
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

    pub(crate) async fn verify_content(&self, ids: &[ContentId]) -> Result<()> {
        let _pins = self.protect_content(ids).await?;
        Ok(())
    }

    async fn verify_id(&self, id: ContentId, raw_only: bool) -> Result<()> {
        if raw_only && id.format != BlobFormat::Raw {
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
        self.fence(id).await?;
        if value.format == BlobFormat::HashSeq {
            let data = self
                .native
                .get_bytes(value.hash)
                .await
                .map_err(backend_error)?;
            for hash in HashSeq::try_from(data).map_err(backend_error)?.iter() {
                let child = self
                    .verify_complete(HashAndFormat::new(hash, BlobFormat::Raw))
                    .await?;
                self.fence(child).await?;
            }
        }
        self.native
            .tags()
            .set(artifact_tag(id.hash, id.format), value)
            .await
            .map_err(backend_error)?;
        self.native.sync_db().await.map_err(backend_error)?;
        Ok(id)
    }

    pub(super) async fn fence(&self, id: ContentId) -> Result<()> {
        if let Some(options) = &self.options {
            let options = options.clone();
            tokio::task::spawn_blocking(move || {
                crate::runtime::object_store::durability::sync_verified(&options, id.hash, id.size)
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
        self.scan(id).await?;
        Ok(id)
    }

    async fn verify_digest(&self, id: ContentId, digest: ContentDigest) -> Result<()> {
        if self.scan(id).await? != digest {
            return Err(ContentError::DigestMismatch(digest));
        }
        Ok(())
    }

    async fn scan(&self, id: ContentId) -> Result<ContentDigest> {
        if id.size == 0 && id.hash != Hash::EMPTY {
            return Err(ContentError::InvalidFormat);
        }
        let mut sha = Sha256::new();
        sha.update(b"ontography-payload/v1\0");
        let mut offset = 0;
        let mut stream = self.native.export_bao(id.hash, ChunkRanges::all()).stream();
        while let Some(item) = stream.next().await {
            match item {
                EncodedItem::Leaf(leaf) => {
                    if leaf.offset != offset {
                        return Err(ContentError::InvalidFormat);
                    }
                    sha.update(&leaf.data);
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
        Ok(ContentDigest::from_bytes(sha.finalize().into()))
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

    async fn mark(&self, value: HashAndFormat, live: &mut HashSet<Hash>) -> Result<()> {
        live.insert(value.hash);
        if value.format == BlobFormat::HashSeq {
            // Partial transfer roots do not yet have traversable children. The
            // transfer's own tags protect data already downloaded independently.
            if !matches!(
                self.native
                    .status(value.hash)
                    .await
                    .map_err(backend_error)?,
                BlobStatus::Complete { .. }
            ) {
                return Ok(());
            }
            let mut hashes = self
                .native
                .export_bao(value.hash, ChunkRanges::all())
                .hashes();
            while let Some(hash) = hashes.next().await {
                live.insert(hash.map_err(backend_error)?);
            }
        }
        Ok(())
    }
}

fn format_code(format: BlobFormat) -> u8 {
    u8::from(format != BlobFormat::Raw)
}
fn artifact_tag(hash: Hash, format: BlobFormat) -> String {
    format!("ontography-artifact:{hash}:{}", format_code(format))
}

struct AbortTask<T>(tokio::task::JoinHandle<T>);
impl<T> Drop for AbortTask<T> {
    fn drop(&mut self) {
        self.0.abort();
    }
}

struct ImportStream<S> {
    stream: Pin<Box<S>>,
    failure: Arc<std::sync::Mutex<Option<io::Error>>>,
    ended: bool,
}

impl<S: Stream<Item = io::Result<Bytes>>> Stream for ImportStream<S> {
    type Item = io::Result<Bytes>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.ended {
            return Poll::Ready(None);
        }
        match self.stream.as_mut().poll_next(cx) {
            Poll::Ready(Some(Err(error))) => {
                self.ended = true;
                *self
                    .failure
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(error);
                Poll::Ready(None)
            }
            Poll::Ready(None) => {
                self.ended = true;
                Poll::Ready(None)
            }
            result => result,
        }
    }
}

struct PartialExport(PathBuf);
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
