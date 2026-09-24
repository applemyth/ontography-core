//! Synchronous ledger boundary around an asynchronous iroh filesystem or memory store.
//!
//! The worker owns its async executor until the last session, content handle,
//! reader, or transfer releases storage. It runs independently of the caller.
//! This preserves the existing non-cancellable `SQLite` publication boundary and
//! lets retained session handles keep reading after runtime shutdown.

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};

use crate::content::{ContentId, ContentStore};
use bytes::Bytes;
use iroh_blobs::api::{Store, TempTag};
use iroh_blobs::store::fs::{FsStore, options::Options};
use iroh_blobs::store::mem::MemStore;
use iroh_blobs::{BlobFormat, Hash};
use tokio::io::AsyncReadExt;

use super::{ObjectStoreError, durability, io_error};
use crate::{ContentDigest, Payload};

type Result<T> = std::result::Result<T, ObjectStoreError>;
type Reply<T> = SyncSender<Result<T>>;

enum Command {
    Put(BTreeMap<ContentDigest, Payload>, Reply<()>),
    Get(ContentDigest, Reply<Option<Payload>>),
    Retain(Vec<ContentId>, Reply<()>),
    Verify(Vec<ContentId>, Reply<()>),
    Size(ContentDigest, Reply<Option<u64>>),
    Protect(Vec<ContentId>, Reply<Vec<TempTag>>),
}

pub(in crate::runtime) struct IrohStore {
    owner: Arc<Worker>,
    content: ContentStore,
}

struct Worker {
    path: PathBuf,
    commands: Mutex<Option<SyncSender<Command>>>,
    worker: Mutex<Option<JoinHandle<()>>>,
    runtime: Mutex<Option<tokio::runtime::Handle>>,
}

struct Started {
    native: Store,
    options: Option<Arc<Options>>,
    runtime: tokio::runtime::Handle,
}

impl IrohStore {
    pub(super) fn open(path: &Path) -> Result<Self> {
        Self::start(Some(path))
    }

    pub(super) fn memory() -> Result<Self> {
        Self::start(None)
    }

    fn start(path: Option<&Path>) -> Result<Self> {
        let persistent = path.map(Path::to_path_buf);
        let path = path.unwrap_or(Path::new("<memory>")).to_path_buf();
        let worker_path = path.clone();
        let (commands, requests) = mpsc::sync_channel(1);
        let (started, ready) = mpsc::sync_channel(1);
        let gate = Arc::new(tokio::sync::Mutex::new(()));
        let worker_gate = gate.clone();
        let worker = thread::Builder::new()
            .name("ontography-objects".into())
            .spawn(move || {
                run(
                    &worker_path,
                    persistent.as_deref(),
                    requests,
                    started,
                    worker_gate,
                );
            })
            .map_err(|source| io_error(&path, source))?;
        let owner = Arc::new(Worker {
            path,
            commands: Mutex::new(Some(commands)),
            worker: Mutex::new(Some(worker)),
            runtime: Mutex::new(None),
        });
        let ready = ready.recv().map_err(|_| owner.disconnected())??;
        *owner.runtime.lock().expect("new worker lock") = Some(ready.runtime.clone());
        let content = ContentStore::new(
            ready.native,
            ready.options,
            owner.clone(),
            gate,
            ready.runtime,
        );
        Ok(Self { owner, content })
    }

    pub(super) fn content_store(&self) -> ContentStore {
        self.content.clone()
    }

    pub(super) fn put_all(&self, objects: &BTreeMap<ContentDigest, Payload>) -> Result<()> {
        self.request(|reply| Command::Put(objects.clone(), reply))
    }

    pub(super) fn get(&self, digest: ContentDigest) -> Result<Option<Payload>> {
        self.request(|reply| Command::Get(digest, reply))
    }

    pub(super) fn content_size(&self, digest: ContentDigest) -> Result<Option<u64>> {
        self.request(|reply| Command::Size(digest, reply))
    }

    pub(super) fn retain_content(&self, ids: &[ContentId]) -> Result<()> {
        self.request(|reply| Command::Retain(ids.to_vec(), reply))
    }

    pub(super) fn protect_content(&self, ids: &[ContentId]) -> Result<Vec<TempTag>> {
        self.request(|reply| Command::Protect(ids.to_vec(), reply))
    }

    pub(super) fn verify_content(&self, ids: &[ContentId]) -> Result<()> {
        self.request(|reply| Command::Verify(ids.to_vec(), reply))
    }

    fn request<T>(&self, command: impl FnOnce(Reply<T>) -> Command) -> Result<T> {
        let (reply, response) = mpsc::sync_channel(1);
        self.owner
            .commands
            .lock()
            .map_err(|_| self.owner.disconnected())?
            .as_ref()
            .ok_or_else(|| self.owner.disconnected())?
            .send(command(reply))
            .map_err(|_| self.owner.disconnected())?;
        response.recv().map_err(|_| self.owner.disconnected())?
    }
}

impl Worker {
    fn disconnected(&self) -> ObjectStoreError {
        io_error(
            &self.path,
            io::Error::new(
                io::ErrorKind::BrokenPipe,
                "iroh object-store worker stopped",
            ),
        )
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        self.commands
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        if let Some(worker) = self
            .worker
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
        {
            // A download can release the final owner on this runtime's worker.
            // Joining from there would deadlock runtime shutdown. A short-lived
            // reaper performs that join; synchronous owners still close eagerly.
            let current = tokio::runtime::Handle::try_current().ok();
            let owned = self
                .runtime
                .get_mut()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if current
                .as_ref()
                .zip(owned.as_ref())
                .is_some_and(|(current, owned)| current.id() == owned.id())
            {
                let _ = thread::Builder::new()
                    .name("ontography-store-reaper".into())
                    .spawn(move || {
                        let _ = worker.join();
                    });
            } else {
                let _ = worker.join();
            }
        }
    }
}

fn run(
    path: &Path,
    persistent: Option<&Path>,
    requests: Receiver<Command>,
    started: Reply<Started>,
    gate: Arc<tokio::sync::Mutex<()>>,
) {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(source) => {
            let _ = started.send(Err(io_error(path, source)));
            return;
        }
    };
    let loaded = runtime.block_on(async {
        if let Some(root) = persistent {
            let options = Arc::new(Options::new(root));
            let store = FsStore::load_with_opts(root.join("blobs.db"), (*options).clone())
                .await
                .map_err(|e| api_error(path, e))?;
            store.sync_db().await.map_err(|e| api_error(path, e))?;
            durability::sync_directories(&options).map_err(|source| io_error(path, source))?;
            Ok((Store::from(store), Some(options)))
        } else {
            Ok((Store::from(MemStore::new()), None))
        }
    });
    let (store, options) = match loaded {
        Ok(loaded) => loaded,
        Err(error) => {
            let _ = started.send(Err(error));
            return;
        }
    };
    // The worker-local handle does not own the worker, avoiding an ownership cycle.
    let content = ContentStore::new(
        store.clone(),
        options.clone(),
        Arc::new(()),
        gate.clone(),
        runtime.handle().clone(),
    );
    if started
        .send(Ok(Started {
            native: store.clone(),
            options: options.clone(),
            runtime: runtime.handle().clone(),
        }))
        .is_ok()
    {
        for command in requests {
            match command {
                Command::Put(objects, reply) => {
                    let _ = reply.send(runtime.block_on(async {
                        let _guard = gate.lock().await;
                        put_all(path, &store, options.as_deref(), objects).await
                    }));
                }
                Command::Get(digest, reply) => {
                    let _ = reply.send(runtime.block_on(get(path, &store, digest)));
                }
                Command::Retain(ids, reply) => {
                    let _ = reply.send(
                        runtime
                            .block_on(content.retain_canonical(&ids))
                            .map_err(|e| api_error(path, e)),
                    );
                }
                Command::Size(digest, reply) => {
                    let _ = reply.send(
                        runtime
                            .block_on(content.content_size(digest))
                            .map_err(|e| api_error(path, e)),
                    );
                }
                Command::Protect(ids, reply) => {
                    let _ = reply.send(
                        runtime
                            .block_on(content.protect_content(&ids))
                            .map_err(|e| api_error(path, e)),
                    );
                }
                Command::Verify(ids, reply) => {
                    let _ = reply.send(
                        runtime
                            .block_on(content.verify_content(&ids))
                            .map_err(|e| api_error(path, e)),
                    );
                }
            }
        }
    }
    let _ = runtime.block_on(store.shutdown());
}

async fn put_all(
    path: &Path,
    store: &Store,
    options: Option<&Options>,
    objects: BTreeMap<ContentDigest, Payload>,
) -> Result<()> {
    for (digest, payload) in objects {
        let hash = Hash::new(&payload);
        let tag = store
            .tags()
            .get(digest.as_bytes())
            .await
            .map_err(|error| api_error(path, error))?;
        if let Some(tag) = tag {
            if tag.format != BlobFormat::Raw || tag.hash != hash {
                return Err(ObjectStoreError::DigestMismatch(digest));
            }
            // A previously imported blob can survive an interrupted commit.
            // Check it before reusing it, and cross the durability barrier again.
            verify_existing(path, store, hash, digest, &payload).await?;
        } else {
            let tag = store
                .add_bytes(Bytes::from_owner(payload.clone()))
                .with_named_tag(digest.as_bytes())
                .await
                .map_err(|error| api_error(path, error))?;
            if tag.format != BlobFormat::Raw || tag.hash != hash {
                return Err(ObjectStoreError::DigestMismatch(digest));
            }
        }
        if let Some(options) = options {
            durability::sync_import(options, hash, &payload)
                .map_err(|source| io_error(path, source))?;
        }
    }
    // The file barrier must precede the database barrier. SQLite may publish
    // graph references only after both exact contents and digest tags are durable.
    store
        .sync_db()
        .await
        .map_err(|error| api_error(path, error))
}

async fn verify_existing(
    path: &Path,
    store: &Store,
    hash: Hash,
    digest: ContentDigest,
    payload: &[u8],
) -> Result<()> {
    let mut reader = store.reader(hash);
    let mut buffer = vec![0_u8; 64 * 1024];
    for expected in payload.chunks(buffer.len()) {
        let actual = &mut buffer[..expected.len()];
        reader
            .read_exact(actual)
            .await
            .map_err(|source| io_error(path, source))?;
        if actual != expected {
            return Err(ObjectStoreError::DigestMismatch(digest));
        }
    }
    if reader
        .read(&mut buffer[..1])
        .await
        .map_err(|source| io_error(path, source))?
        != 0
    {
        return Err(ObjectStoreError::DigestMismatch(digest));
    }
    Ok(())
}

async fn get(path: &Path, store: &Store, digest: ContentDigest) -> Result<Option<Payload>> {
    let Some(tag) = store
        .tags()
        .get(digest.as_bytes())
        .await
        .map_err(|error| api_error(path, error))?
    else {
        return Ok(None);
    };
    if tag.format != BlobFormat::Raw {
        return Err(ObjectStoreError::DigestMismatch(digest));
    }
    let mut bytes = Vec::new();
    store
        .reader(tag.hash)
        .read_to_end(&mut bytes)
        .await
        .map_err(|source| io_error(path, source))?;
    // The raw iroh reader does not verify local bytes. Ontography's existing
    // domain-separated digest is the integrity authority for every retrieval.
    if !digest.verifies(&bytes) || Hash::new(&bytes) != tag.hash {
        return Err(ObjectStoreError::DigestMismatch(digest));
    }
    Ok(Some(Payload::from(bytes)))
}

fn api_error(path: &Path, error: impl std::fmt::Display) -> ObjectStoreError {
    io_error(path, io::Error::other(error.to_string()))
}
