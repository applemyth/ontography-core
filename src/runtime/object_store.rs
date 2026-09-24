//! Session-owned immutable payload storage.

use crate::content::{ContentId, ContentStore};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use thiserror::Error;

use crate::{ContentDigest, Payload};

pub(crate) mod durability;
mod iroh;

use self::iroh::IrohStore;

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

pub(super) struct ObjectStore {
    store: IrohStore,
}

impl ObjectStore {
    pub(super) fn memory(
        objects: BTreeMap<ContentDigest, Payload>,
    ) -> Result<Self, ObjectStoreError> {
        let store = IrohStore::memory()?;
        store.put_all(&objects)?;
        Ok(Self { store })
    }

    pub(super) fn content_store(&self) -> ContentStore {
        self.store.content_store()
    }

    pub(super) fn content_size(
        &self,
        digest: ContentDigest,
    ) -> Result<Option<u64>, ObjectStoreError> {
        self.store.content_size(digest)
    }

    pub(super) fn retain_content(&self, ids: &[ContentId]) -> Result<(), ObjectStoreError> {
        if ids.is_empty() {
            return Ok(());
        }
        self.store.retain_content(ids)
    }

    pub(super) fn protect_content(
        &self,
        ids: &[ContentId],
    ) -> Result<Vec<iroh_blobs::api::TempTag>, ObjectStoreError> {
        if ids.is_empty() {
            return Ok(Vec::new());
        }
        self.store.protect_content(ids)
    }

    pub(super) fn verify_content(&self, ids: &[ContentId]) -> Result<(), ObjectStoreError> {
        if ids.is_empty() {
            return Ok(());
        }
        self.store.verify_content(ids)
    }

    pub(super) fn create(path: &Path) -> Result<Self, ObjectStoreError> {
        fs::create_dir(path).map_err(|source| io_error(path, source))?;
        sync_directory(path.parent().unwrap_or(path))?;
        let store = IrohStore::open(path)?;
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
        Ok(Self { store })
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
        Ok(Self {
            store: IrohStore::open(path)?,
        })
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
        self.store.put_all(objects)
    }

    pub(super) fn get(&self, digest: ContentDigest) -> Result<Option<Payload>, ObjectStoreError> {
        self.store.get(digest)
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
    use crate::content::{BlobFormat, ContentError};
    use bytes::Bytes;
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
    async fn released_blobs_are_collected_but_history_and_live_readers_survive() {
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
    async fn collections_keep_raw_children_until_root_released() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let child = store
            .import_bytes(Bytes::from_static(b"source file"))
            .await
            .unwrap();
        let collection = store
            .import_collection([("src/file".to_owned(), child)])
            .await
            .unwrap();
        assert_eq!(collection.format(), BlobFormat::HashSeq);
        store.release(child).await.unwrap();
        store.collect_garbage().await.unwrap();
        assert_eq!(
            store.read_collection(collection).await.unwrap(),
            vec![("src/file".to_owned(), child)]
        );
        assert_eq!(store.read_hash_sequence(collection).await.unwrap().len(), 2);
        assert!(store.import_hash_sequence(&[collection]).await.is_err());
        store.release(collection).await.unwrap();
        store.collect_garbage().await.unwrap();
        assert!(store.metadata(child).await.is_err());
    }

    #[tokio::test]
    async fn copied_file_and_stream_survive_reopen_and_verify_corruption() {
        let directory = Directory::new();
        let root = directory.0.join("objects");
        let source = directory.0.join("source");
        let bytes = vec![73; 200_000];
        fs::write(&source, &bytes).unwrap();
        let objects = ObjectStore::create(&root).unwrap();
        let store = objects.content_store();
        let id = store.import_file(&source).await.unwrap();
        let chunks = futures_lite::stream::iter(vec![
            Ok(Bytes::from_static(b"one")),
            Ok(Bytes::from_static(b"two")),
        ]);
        let streamed = store.import_stream(chunks).await.unwrap();
        fs::remove_file(&source).unwrap();
        drop(store);
        drop(objects);
        let reopened = ObjectStore::open(&root).unwrap();
        let store = reopened.content_store();
        assert_eq!(store.read_range(streamed, 0..6).await.unwrap(), "onetwo");
        store.export_file(id, &source).await.unwrap();
        assert_eq!(fs::read(&source).unwrap(), bytes);
        assert!(store.export_file(id, &source).await.is_err());
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
    async fn empty_content_and_canonical_artifact_pins_survive_release() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let id = store.import_bytes(Bytes::new()).await.unwrap();
        assert!(store.read_range(id, 0..0).await.unwrap().is_empty());
        objects.retain_content(&[id]).unwrap();
        store.release(id).await.unwrap();
        store.collect_garbage().await.unwrap();
        objects.verify_content(&[id]).unwrap();
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
            .native
            .tags()
            .set(digest.as_bytes(), replacement.hash())
            .await
            .unwrap();
        assert!(
            matches!(store.read_digest_range(digest, 0..3).await, Err(ContentError::DigestMismatch(found)) if found == digest)
        );
        assert!(objects.require(digest).is_err());
    }

    #[tokio::test(flavor = "current_thread")]
    async fn stalled_stream_does_not_block_synchronous_ledger_publication() {
        let mut objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let (send_bytes, receive_bytes) = tokio::sync::mpsc::channel(1);
        let (finished, completion) = std::sync::mpsc::channel();
        // A watchdog bounds regressions even if the caller's sole executor is
        // blocked in the synchronous object-store publication boundary.
        let watchdog = std::thread::spawn(move || {
            let _ = completion.recv_timeout(std::time::Duration::from_secs(2));
            drop(send_bytes);
        });
        let stream = futures_lite::stream::unfold(receive_bytes, |mut receiver| async {
            receiver.recv().await.map(|bytes| (Ok(bytes), receiver))
        });
        let import = tokio::spawn(async move { store.import_stream(stream).await });
        tokio::time::sleep(std::time::Duration::from_millis(20)).await;
        let start = std::time::Instant::now();
        let payload = Payload::from(b"independent ledger content".as_slice());
        let digest = ContentDigest::compute(&payload);
        objects
            .put_all(&BTreeMap::from([(digest, payload)]))
            .unwrap();
        assert!(start.elapsed() < std::time::Duration::from_secs(1));
        finished.send(()).unwrap();
        watchdog.join().unwrap();
        import.await.unwrap().unwrap();
    }

    #[tokio::test]
    async fn failed_stream_returns_source_error_without_retaining_prefix() {
        let objects = ObjectStore::memory(BTreeMap::new()).unwrap();
        let store = objects.content_store();
        let stream = futures_lite::stream::iter(vec![
            Ok(Bytes::from_static(b"unfinished prefix")),
            Err(io::Error::new(
                io::ErrorKind::ConnectionReset,
                "source disconnected",
            )),
        ]);
        let result = tokio::time::timeout(
            std::time::Duration::from_secs(1),
            store.import_stream(stream),
        )
        .await
        .unwrap();
        assert!(
            matches!(result, Err(ContentError::Io(error)) if error.kind() == io::ErrorKind::ConnectionReset)
        );
        store.collect_garbage().await.unwrap();
        assert!(
            !store
                .native
                .has(crate::content::Hash::new(b"unfinished prefix"))
                .await
                .unwrap()
        );
    }
}
