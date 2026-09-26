//! Session-owned immutable payload storage.

use ontography_content::content::{ContentId, ContentStore};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use iroh_blobs::api::TempTag;
use thiserror::Error;

use ontography_calculus::{ContentDigest, Payload};

mod iroh;

use self::iroh::{Command, Worker};

const IROH_FORMAT: &[u8] = b"ontography-iroh-blobs/v1\n";

#[derive(Debug, Error)]
pub(super) enum ObjectStoreError {
    #[error("object store I/O failed at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    #[error("object {0} is missing")]
    Missing(ContentDigest),
    #[error("object {0} does not match its digest")]
    DigestMismatch(ContentDigest),
}

/// Synchronous facade over the worker-owned iroh store; see `iroh` for the
/// boundary's rationale.
pub(super) struct ObjectStore {
    worker: Arc<Worker>,
    content: ContentStore,
}

impl ObjectStore {
    fn start(path: Option<&Path>) -> Result<Self, ObjectStoreError> {
        let (worker, content) = iroh::start(path)?;
        Ok(Self { worker, content })
    }

    pub(super) fn memory(
        objects: BTreeMap<ContentDigest, Payload>,
    ) -> Result<Self, ObjectStoreError> {
        let store = Self::start(None)?;
        store.publish(&objects)?;
        Ok(store)
    }

    pub(super) fn content_store(&self) -> ContentStore {
        self.content.clone()
    }

    pub(super) fn content_size(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<u64>, ObjectStoreError> {
        self.worker.request(|reply| Command::Size(digest, reply))
    }

    pub(super) fn retain_content(&self, ids: &[ContentId]) -> Result<(), ObjectStoreError> {
        if ids.is_empty() {
            return Ok(());
        }
        self.worker
            .request(|reply| Command::Retain(ids.to_vec(), reply))
    }

    pub(super) fn protect_content(
        &self,
        ids: &[ContentId],
    ) -> Result<Vec<TempTag>, ObjectStoreError> {
        if ids.is_empty() {
            return Ok(Vec::new());
        }
        self.worker
            .request(|reply| Command::Protect(ids.to_vec(), reply))
    }

    pub(super) fn verify_content(&self, ids: &[ContentId]) -> Result<(), ObjectStoreError> {
        if ids.is_empty() {
            return Ok(());
        }
        self.worker
            .request(|reply| Command::Verify(ids.to_vec(), reply))
    }

    pub(super) fn create(path: &Path) -> Result<Self, ObjectStoreError> {
        fs::create_dir(path).map_err(|source| io_error(path, source))?;
        sync_directory(path.parent().unwrap_or(path))?;
        let store = Self::start(Some(path))?;
        let marker = path.join("format");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&marker)
            .map_err(|source| io_error(&marker, source))?;
        file.write_all(IROH_FORMAT)
            .and_then(|()| file.sync_all())
            .map_err(|source| io_error(&marker, source))?;
        sync_directory(path)?;
        Ok(store)
    }

    pub(super) fn open(path: &Path) -> Result<Self, ObjectStoreError> {
        if !fs::metadata(path)
            .map_err(|source| io_error(path, source))?
            .is_dir()
        {
            return Err(io_error(
                path,
                io::Error::new(io::ErrorKind::NotADirectory, "not a directory"),
            ));
        }
        let marker = path.join("format");
        let format = fs::read(&marker).map_err(|source| io_error(&marker, source))?;
        if format != IROH_FORMAT {
            return Err(invalid_store(&marker, "unsupported object-store format"));
        }
        // FsStore::load creates missing databases. Resume must never replace
        // a missing or truncated store.
        validate_iroh_layout(path)?;
        Self::start(Some(path))
    }

    pub(super) fn put_all(
        &mut self,
        objects: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<(), ObjectStoreError> {
        for (digest, payload) in objects {
            if !digest.verifies(payload) {
                return Err(ObjectStoreError::DigestMismatch(*digest));
            }
        }
        self.publish(objects)
    }

    fn publish(&self, objects: &BTreeMap<ContentDigest, Payload>) -> Result<(), ObjectStoreError> {
        self.worker
            .request(|reply| Command::Put(objects.clone(), reply))
    }

    pub(super) fn get(&self, digest: ContentDigest) -> Result<Option<Payload>, ObjectStoreError> {
        self.worker.request(|reply| Command::Get(digest, reply))
    }

    pub(super) fn require(&self, digest: ContentDigest) -> Result<Payload, ObjectStoreError> {
        self.get(digest)?.ok_or(ObjectStoreError::Missing(digest))
    }
}

fn validate_iroh_layout(path: &Path) -> Result<(), ObjectStoreError> {
    let database = path.join("blobs.db");
    let metadata = fs::metadata(&database).map_err(|source| io_error(&database, source))?;
    if !metadata.is_file() || metadata.len() == 0 {
        return Err(invalid_store(&database, "missing or empty iroh database"));
    }
    for name in ["data", "temp"] {
        let directory = path.join(name);
        if !fs::metadata(&directory)
            .map_err(|source| io_error(&directory, source))?
            .is_dir()
        {
            return Err(invalid_store(&directory, "expected iroh directory"));
        }
    }
    Ok(())
}

fn invalid_store(path: &Path, message: &str) -> ObjectStoreError {
    io_error(path, io::Error::new(io::ErrorKind::InvalidData, message))
}

#[cfg(unix)]
fn sync_directory(path: &Path) -> Result<(), ObjectStoreError> {
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|source| io_error(path, source))
}

#[cfg(not(unix))]
fn sync_directory(_path: &Path) -> Result<(), ObjectStoreError> {
    Ok(())
}

fn io_error(path: &Path, source: io::Error) -> ObjectStoreError {
    ObjectStoreError::Io {
        path: path.to_path_buf(),
        source,
    }
}

#[cfg(test)]
mod content_tests {
    use super::*;
    use bytes::Bytes;
    use ontography_content::content::ContentError;
    use tokio::io::{AsyncReadExt, AsyncSeekExt};

    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            let path = std::env::temp_dir()
                .join(format!("ontography-content-test-{}", uuid::Uuid::new_v4()));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[tokio::test]
    async fn verified_ranges_and_seek_work_across_boundaries_and_owner_drop() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let bytes: Vec<u8> = (0_u8..251).cycle().take(100_000).collect();
        let id = store.import_bytes(bytes.clone()).await.unwrap();
        drop(objects);
        assert_eq!(
            store.read_range(id, 16_000..34_000).await.unwrap().as_ref(),
            &bytes[16_000..34_000]
        );
        assert!(matches!(
            store.read_range(id, 0..100_001).await,
            Err(ContentError::InvalidRange { .. })
        ));
        let mut reader = store.reader(id).await.unwrap();
        reader.seek(io::SeekFrom::Start(32_111)).await.unwrap();
        let mut tail = Vec::new();
        reader.read_to_end(&mut tail).await.unwrap();
        assert_eq!(tail, bytes[32_111..]);
        drop(store);
        reader.seek(io::SeekFrom::Start(0)).await.unwrap();
        let mut prefix = [0; 8];
        reader.read_exact(&mut prefix).await.unwrap();
        assert_eq!(&prefix, &bytes[..8]);
    }

    #[tokio::test]
    async fn untagged_blobs_are_collected_but_history_and_live_readers_survive() {
        let payload = Payload::from(b"retained ledger payload".as_slice());
        let digest = ContentDigest::compute(&payload);
        let objects = ObjectStore::memory(BTreeMap::from([(digest, payload.clone())])).unwrap();
        let store = objects.content_store();
        let artifact = store
            .import_bytes(Bytes::from_static(b"disposable artifact"))
            .await
            .unwrap();
        let mut reader = store.reader(artifact).await.unwrap();
        store.release(artifact).await.unwrap();
        store.collect_garbage().await.unwrap();
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes).await.unwrap();
        assert_eq!(bytes, b"disposable artifact");
        drop(reader);
        store.collect_garbage().await.unwrap();
        assert!(store.metadata(artifact).await.is_err());
        assert_eq!(
            store
                .read_digest_range(digest, 0..8)
                .await
                .unwrap()
                .unwrap()
                .as_ref(),
            b"retained"
        );
        assert_eq!(objects.require(digest).unwrap(), payload);
    }

    #[tokio::test]
    async fn owned_and_inlined_imports_survive_reopen_and_verify_corruption() {
        let directory = Directory::new();
        let root = directory.0.join("objects");
        let exported = directory.0.join("exported");
        let bytes = vec![73; 200_000];
        let objects = ObjectStore::create(&root).unwrap();
        let store = objects.content_store();
        let id = store.import_bytes(bytes.clone()).await.unwrap();
        let inlined = store
            .import_bytes(Bytes::from_static(b"onetwo"))
            .await
            .unwrap();
        drop(store);
        drop(objects);
        let reopened = ObjectStore::open(&root).unwrap();
        let store = reopened.content_store();
        assert_eq!(store.read_range(inlined, 0..6).await.unwrap(), "onetwo");
        store.export_file(id, &exported).await.unwrap();
        assert_eq!(fs::read(&exported).unwrap(), bytes);
        assert!(store.export_file(id, &exported).await.is_err());
        // Out-of-band corruption is detected by range verification immediately.
        let data = root
            .join("data")
            .join(format!("{}.data", id.hash().to_hex()));
        let mut file = OpenOptions::new().write(true).open(data).unwrap();
        file.write_all(b"corruption").unwrap();
        file.sync_all().unwrap();
        assert!(store.read_range(id, 0..10).await.is_err());
    }

    #[tokio::test]
    async fn empty_content_and_canonical_artifact_pins_survive_untagging() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let id = store.import_bytes(Bytes::new()).await.unwrap();
        assert!(store.read_range(id, 0..0).await.unwrap().is_empty());
        objects.retain_content(&[id]).unwrap();
        store.release(id).await.unwrap();
        store.collect_garbage().await.unwrap();
        objects.verify_content(&[id]).unwrap();
    }

    /// `release` deletes only the artifact tag: an unreferenced import is
    /// collected afterwards, while an import that committed ledger history
    /// retains survives under its ledger tag. Releasing twice is harmless.
    #[tokio::test]
    async fn release_collects_unreferenced_imports_and_keeps_ledger_content() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let unreferenced = store
            .import_bytes(Bytes::from_static(b"unreferenced import"))
            .await
            .unwrap();
        let referenced = store
            .import_bytes(Bytes::from_static(b"ledger-referenced import"))
            .await
            .unwrap();
        objects.retain_content(&[referenced]).unwrap();
        store.release(unreferenced).await.unwrap();
        store.release(unreferenced).await.unwrap();
        store.release(referenced).await.unwrap();
        store.collect_garbage().await.unwrap();
        assert!(matches!(
            store.metadata(unreferenced).await,
            Err(ContentError::Missing(_))
        ));
        assert_eq!(store.read_range(referenced, 0..6).await.unwrap(), "ledger");
        objects.verify_content(&[referenced]).unwrap();
    }

    #[tokio::test]
    async fn altered_digest_tags_cannot_authorize_ranges() {
        let expected = Payload::from(b"expected content".as_slice());
        let digest = ContentDigest::compute(&expected);
        let objects = ObjectStore::memory(BTreeMap::from([(digest, expected)])).unwrap();
        let store = objects.content_store();
        let replacement = store
            .import_bytes(Bytes::from_static(b"substituted content"))
            .await
            .unwrap();
        store
            .native()
            .tags()
            .set(digest.as_bytes(), replacement.hash())
            .await
            .unwrap();
        assert!(
            matches!(store.read_digest_range(digest, 0..3).await, Err(ContentError::DigestMismatch(found)) if found == digest)
        );
        assert!(objects.require(digest).is_err());
    }
}
