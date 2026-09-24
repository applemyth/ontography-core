//! Explicit, scoped iroh providers and resumable, verified content downloads.
//!
//! A provider serves only the roots supplied to [`ContentStore::serve`]. A
//! published hash sequence also permits reading its children through that root.
//! An optional peer allowlist restricts access further. Endpoints belong to the
//! embedding application; it chooses addresses, relays, discovery and identity.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use futures_lite::StreamExt;
use iroh::endpoint::Connection;
use iroh::protocol::{AcceptError, ProtocolHandler, Router};
pub use iroh::{Endpoint, EndpointAddr, EndpointId};
use iroh_blobs::api::remote::GetProgressItem;
use iroh_blobs::api::{Store, TempTag};
use iroh_blobs::provider::events::{
    AbortReason, EventMask, EventSender, ObserveMode, ProviderMessage, RequestMode,
};
pub use iroh_blobs::ticket::BlobTicket;
use iroh_blobs::{BlobFormat, Hash, HashAndFormat};
use tokio::sync::watch;
use tokio::task::JoinHandle;

use super::{ContentError, ContentId, ContentStore, backend_error};

type Result<T> = std::result::Result<T, ContentError>;

/// State of a resumable download. Cancellation keeps verified partial bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DownloadState {
    /// Resolving or connecting to the ticket provider.
    Connecting,
    /// Receiving and verifying missing Bao ranges.
    Downloading,
    /// Complete bytes are being verified and durably imported.
    Verifying,
    /// All requested content is verified and durably retained.
    Complete(ContentId),
    /// The attempt stopped; its available verified ranges remain retained.
    Cancelled,
    /// The attempt failed; its available verified ranges remain retained.
    Failed(String),
}

/// A progress snapshot. Byte counts exclude Bao proofs and transport overhead.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DownloadProgress {
    /// Verified bytes already present before this attempt (including children).
    pub local_bytes: u64,
    /// Payload bytes received during this attempt.
    pub received_bytes: u64,
    /// Current phase or terminal result.
    pub state: DownloadState,
}

/// Locally available content for a ticket, independent of any active attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DownloadAvailability {
    /// Available verified payload bytes, including hash-sequence children.
    pub local_bytes: u64,
    /// Whether all requested root and child bytes are available. This alone
    /// does not assert that Ontography's durable import barrier has completed.
    pub complete: bool,
}

/// A download running on the store's runtime, independent of its observer.
///
/// Dropping this handle requests cancellation and keeps partial data pinned for
/// a later retry with the same ticket. [`Self::finish`] waits for verification
/// and durable retention. Cancellation is cooperative: already queued disk
/// writes are drained before the job reports `Cancelled`.
pub struct ContentDownload {
    ticket: BlobTicket,
    progress: watch::Receiver<DownloadProgress>,
    cancel: watch::Sender<bool>,
    task: Option<JoinHandle<Result<ContentId>>>,
    _store: ContentStore,
}

impl fmt::Debug for ContentDownload {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ContentDownload")
            .field("ticket", &self.ticket)
            .field("progress", &*self.progress.borrow())
            .finish_non_exhaustive()
    }
}

impl ContentDownload {
    /// The portable ticket used for this attempt and later retries.
    #[must_use]
    pub fn ticket(&self) -> &BlobTicket {
        &self.ticket
    }

    /// Return the most recent progress snapshot.
    #[must_use]
    pub fn progress(&self) -> DownloadProgress {
        self.progress.borrow().clone()
    }

    /// Subscribe without delaying the download when updates are not consumed.
    #[must_use]
    pub fn subscribe(&self) -> watch::Receiver<DownloadProgress> {
        self.progress.clone()
    }

    /// Stop this attempt while retaining partial bytes and its persistent pin.
    pub fn cancel(&self) {
        self.cancel.send_replace(true);
    }

    /// Wait for durable completion, or an error/cancellation. A failed attempt
    /// can be retried by calling [`ContentStore::download`] with the same ticket.
    ///
    /// # Errors
    /// Returns transport, integrity, storage, or cancellation errors.
    pub async fn finish(mut self) -> Result<ContentId> {
        self.task
            .take()
            .ok_or_else(|| backend_error("download task is absent"))?
            .await
            .map_err(backend_error)?
    }
}

impl Drop for ContentDownload {
    fn drop(&mut self) {
        self.cancel.send_replace(true);
    }
}

/// An explicitly started, read-only provider for a fixed set of content roots.
///
/// Dropping it schedules shutdown; use [`Self::shutdown`] to await completion.
/// Shutdown closes its endpoint, including other users of endpoint clones, so
/// pass an endpoint dedicated to this provider. It does not close the store.
pub struct ContentProvider {
    router: Option<Router>,
    endpoint: Endpoint,
    contents: BTreeMap<Hash, ContentId>,
    store: ContentStore,
}

impl fmt::Debug for ContentProvider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ContentProvider")
            .field("contents", &self.contents)
            .finish_non_exhaustive()
    }
}

impl ContentProvider {
    /// Current endpoint address, including configured direct and relay routes.
    #[must_use]
    pub fn address(&self) -> EndpointAddr {
        self.endpoint.addr()
    }

    /// Make a portable iroh ticket for one of this provider's published roots.
    ///
    /// # Errors
    /// Returns an error if this exact content ID was not published.
    pub fn ticket(&self, content: ContentId) -> Result<BlobTicket> {
        if self.contents.get(&content.hash()) != Some(&content) {
            return Err(ContentError::Missing(content.hash()));
        }
        Ok(BlobTicket::new(
            self.address(),
            content.hash(),
            content.format(),
        ))
    }

    /// Stop serving and close the dedicated endpoint, leaving storage usable.
    ///
    /// # Errors
    /// Returns an error if the provider task could not shut down cleanly.
    pub async fn shutdown(mut self) -> Result<()> {
        if let Some(router) = self.router.take() {
            router.shutdown().await.map_err(backend_error)?;
        }
        Ok(())
    }
}

impl Drop for ContentProvider {
    fn drop(&mut self) {
        if let Some(router) = self.router.take() {
            let store = self.store.clone();
            self.store.runtime.spawn(async move {
                let _ = router.shutdown().await;
                drop(store);
            });
        }
    }
}

#[derive(Clone)]
struct ScopedProtocol {
    store: Store,
    events: EventSender,
    allowed_peers: Option<Arc<BTreeSet<EndpointId>>>,
    _pins: Arc<Vec<TempTag>>,
}

impl fmt::Debug for ScopedProtocol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ScopedProtocol").finish_non_exhaustive()
    }
}

impl ProtocolHandler for ScopedProtocol {
    async fn accept(&self, connection: Connection) -> std::result::Result<(), AcceptError> {
        if self
            .allowed_peers
            .as_ref()
            .is_some_and(|peers| !peers.contains(&connection.remote_id()))
        {
            connection.close(
                iroh_blobs::protocol::ERR_PERMISSION,
                b"peer is not authorized",
            );
            return Ok(());
        }
        iroh_blobs::provider::handle_connection(
            connection,
            self.store.clone(),
            self.events.clone(),
        )
        .await;
        Ok(())
    }
}

impl ContentStore {
    /// Serve selected, complete content roots using a dedicated endpoint.
    ///
    /// `allowed_peers = None` grants read access to anyone with a published hash;
    /// `Some(peers)` additionally authenticates against those endpoint identities.
    /// An empty peer set denies everyone. Pushes are always disabled. Ordinary
    /// session startup never starts a provider or opens a network endpoint.
    ///
    /// # Errors
    /// Returns an error for missing content, conflicting IDs, or storage failure.
    pub async fn serve(
        &self,
        endpoint: Endpoint,
        contents: impl IntoIterator<Item = ContentId>,
        allowed_peers: Option<BTreeSet<EndpointId>>,
    ) -> Result<ContentProvider> {
        let contents = contents.into_iter().collect::<Vec<_>>();
        let store = self.clone();
        self.run(async move { store.serve_inner(endpoint, contents, allowed_peers).await })
            .await
    }

    async fn serve_inner(
        &self,
        endpoint: Endpoint,
        contents: Vec<ContentId>,
        allowed_peers: Option<BTreeSet<EndpointId>>,
    ) -> Result<ContentProvider> {
        let guard = self.gate.lock().await;
        let mut selected = BTreeMap::new();
        for id in contents {
            if selected
                .insert(id.hash(), id)
                .is_some_and(|previous| previous != id)
            {
                return Err(ContentError::InvalidFormat);
            }
        }
        let contents = selected;
        let mut pins = Vec::with_capacity(contents.len());
        for content in contents.values() {
            if self.complete_size(content.hash()).await? != content.size() {
                return Err(ContentError::InvalidFormat);
            }
            let value = HashAndFormat {
                hash: content.hash(),
                format: content.format(),
            };
            pins.push(
                self.native
                    .tags()
                    .temp_tag(value)
                    .await
                    .map_err(backend_error)?,
            );
            if !self
                .native
                .remote()
                .local(value)
                .await
                .map_err(backend_error)?
                .is_complete()
            {
                return Err(ContentError::Missing(content.hash()));
            }
        }
        let (events, mut requests) = EventSender::channel(
            64,
            EventMask {
                get: RequestMode::Intercept,
                get_many: RequestMode::Disabled,
                push: RequestMode::Disabled,
                observe: ObserveMode::Intercept,
                ..EventMask::DEFAULT
            },
        );
        let published = contents.clone();
        let authorization_store = self.native.clone();
        self.runtime.spawn(async move {
            while let Some(request) = requests.recv().await {
                match request {
                    ProviderMessage::GetRequestReceived(request) => {
                        let get = &request.inner.request;
                        let mut permitted = published.get(&get.hash).is_some_and(|content| {
                            content.format() == BlobFormat::HashSeq
                                || get.ranges.is_blob()
                                || get.ranges.is_empty()
                        });
                        if permitted && !get.ranges.is_blob() && !get.ranges.is_empty() {
                            // A resumed request may omit the root. Upstream's
                            // provider follows a hash sequence using get_bytes,
                            // so verify that manifest before authorizing its
                            // children even when its bytes won't be transmitted.
                            let mut children = authorization_store
                                .export_bao(get.hash, bao_tree::ChunkRanges::all())
                                .hashes();
                            while let Some(child) = children.next().await {
                                if child.is_err() {
                                    permitted = false;
                                    break;
                                }
                            }
                        }
                        let _ = request
                            .tx
                            .send(if permitted {
                                Ok(())
                            } else {
                                Err(AbortReason::Permission)
                            })
                            .await;
                    }
                    ProviderMessage::ObserveRequestReceived(request) => {
                        let permitted = published.contains_key(&request.inner.request.hash);
                        let _ = request
                            .tx
                            .send(if permitted {
                                Ok(())
                            } else {
                                Err(AbortReason::Permission)
                            })
                            .await;
                    }
                    _ => {}
                }
            }
        });
        let protocol = ScopedProtocol {
            store: self.native.clone(),
            events,
            allowed_peers: allowed_peers.map(Arc::new),
            _pins: Arc::new(pins),
        };
        let router = {
            let _entered = self.runtime.enter();
            Router::builder(endpoint.clone())
                .accept(iroh_blobs::ALPN, protocol)
                .spawn()
        };
        drop(guard);
        Ok(ContentProvider {
            router: Some(router),
            endpoint,
            contents,
            store: self.clone(),
        })
    }

    /// Start or resume fetching a raw blob or hash sequence from an iroh ticket.
    ///
    /// The ticket's BLAKE3 root is the integrity commitment; downloaded content
    /// does not inherit any remote claim about Ontography's SHA-256 identity.
    /// Completion verifies content locally, establishes its local identity and
    /// crosses the normal durable import barrier. Save the ticket to resume an
    /// interrupted attempt after reopening a persistent store.
    ///
    /// # Errors
    /// Returns an error if the store cannot retain or inspect the transfer root.
    /// Transport and verification errors are reported by the returned job.
    pub async fn download(
        &self,
        endpoint: Endpoint,
        ticket: BlobTicket,
    ) -> Result<ContentDownload> {
        let store = self.clone();
        self.run(async move { store.download_inner(endpoint, ticket).await })
            .await
    }

    async fn download_inner(
        &self,
        endpoint: Endpoint,
        ticket: BlobTicket,
    ) -> Result<ContentDownload> {
        let value = ticket.hash_and_format();
        let guard = self.gate.lock().await;
        let pin = self
            .native
            .tags()
            .temp_tag(value)
            .await
            .map_err(backend_error)?;
        self.native
            .tags()
            .set(transfer_tag(value), value)
            .await
            .map_err(backend_error)?;
        self.native.sync_db().await.map_err(backend_error)?;
        let local_bytes = self
            .native
            .remote()
            .local(value)
            .await
            .map_err(backend_error)?
            .local_bytes();
        let initial = DownloadProgress {
            local_bytes,
            received_bytes: 0,
            state: DownloadState::Connecting,
        };
        let (progress_tx, progress) = watch::channel(initial);
        let (cancel, cancel_rx) = watch::channel(false);
        let store = self.clone();
        let job_ticket = ticket.clone();
        let task = self.runtime.spawn(async move {
            run_download(store, endpoint, job_ticket, progress_tx, cancel_rx, pin).await
        });
        drop(guard);
        Ok(ContentDownload {
            ticket,
            progress,
            cancel,
            task: Some(task),
            _store: self.clone(),
        })
    }

    /// Inspect verified locally available bytes, including any retained partial
    /// data, without connecting to the provider.
    ///
    /// # Errors
    /// Returns an error if local availability cannot be inspected.
    pub async fn download_status(&self, ticket: &BlobTicket) -> Result<DownloadAvailability> {
        let local = self
            .native
            .remote()
            .local(ticket.hash_and_format())
            .await
            .map_err(backend_error)?;
        Ok(DownloadAvailability {
            local_bytes: local.local_bytes(),
            complete: local.is_complete(),
        })
    }

    /// Release an abandoned download's persistent pin. This does not delete
    /// retained artifacts or graph history. Active transfers hold temporary
    /// protection; garbage collection can reclaim the rest after they stop.
    ///
    /// # Errors
    /// Returns an error if the retention change cannot be persisted.
    pub async fn discard_download(&self, ticket: &BlobTicket) -> Result<()> {
        let store = self.clone();
        let value = ticket.hash_and_format();
        self.run(async move { store.discard_download_inner(value).await })
            .await
    }

    async fn discard_download_inner(&self, value: HashAndFormat) -> Result<()> {
        let _guard = self.gate.lock().await;
        self.native
            .tags()
            .delete(transfer_tag(value))
            .await
            .map_err(backend_error)?;
        self.native.sync_db().await.map_err(backend_error)?;
        Ok(())
    }
}

fn transfer_tag(value: HashAndFormat) -> String {
    format!(
        "ontography/download/{}/{}",
        value.hash.to_hex(),
        u8::from(value.format == BlobFormat::HashSeq)
    )
}

async fn run_download(
    store: ContentStore,
    endpoint: Endpoint,
    ticket: BlobTicket,
    progress: watch::Sender<DownloadProgress>,
    mut cancel: watch::Receiver<bool>,
    _pin: TempTag,
) -> Result<ContentId> {
    let value = ticket.hash_and_format();
    let transfer = async {
        let local = store
            .native
            .remote()
            .local(value)
            .await
            .map_err(backend_error)?;
        if local.is_complete() {
            return Ok(());
        }
        let connection = endpoint
            .connect(ticket.addr().clone(), iroh_blobs::ALPN)
            .await
            .map_err(backend_error)?;
        progress.send_modify(|p| p.state = DownloadState::Downloading);
        let stream = store.native.remote().fetch(connection, value).stream();
        tokio::pin!(stream);
        while let Some(item) = stream.next().await {
            match item {
                GetProgressItem::Progress(bytes) => {
                    progress.send_modify(|p| p.received_bytes = bytes);
                }
                GetProgressItem::Done(_) => return Ok(()),
                GetProgressItem::Error(error) => return Err(backend_error(error)),
            }
        }
        Err(backend_error("download ended without a completion result"))
    };
    let result = tokio::select! {
        biased;
        () = async {
            if !*cancel.borrow() { let _ = cancel.changed().await; }
        } => Err(ContentError::Cancelled),
        result = transfer => result,
    };
    if let Err(error) = result {
        // Dropping the fetch stream cancels its writer. Iroh checkpoints partial
        // data and its verified chunk bitfield as the file actor becomes idle.
        // wait_idle drains those writes before acknowledging cancellation.
        let checkpoint = checkpoint_download(&store, value).await;
        let error = checkpoint.err().unwrap_or(error);
        progress.send_modify(|p| {
            p.state = if matches!(error, ContentError::Cancelled) {
                DownloadState::Cancelled
            } else {
                DownloadState::Failed(error.to_string())
            }
        });
        return Err(error);
    }
    progress.send_modify(|p| p.state = DownloadState::Verifying);
    let _guard = store.gate.lock().await;
    let result = async {
        let content = store.finish_import(value).await?;
        store
            .native
            .tags()
            .delete(transfer_tag(value))
            .await
            .map_err(backend_error)?;
        store.native.sync_db().await.map_err(backend_error)?;
        Ok::<_, ContentError>(content)
    }
    .await;
    match &result {
        Ok(content) => {
            progress.send_modify(|p| p.state = DownloadState::Complete(*content));
        }
        Err(error) => progress.send_modify(|p| p.state = DownloadState::Failed(error.to_string())),
    }
    result
}

// Acknowledged cancellation is a durable checkpoint for the ranges iroh has
// already verified. Waiting for idle can also wait for concurrent store work;
// callers wanting immediate cancellation can call cancel() and keep the handle.
async fn checkpoint_download(store: &ContentStore, value: HashAndFormat) -> Result<()> {
    store.native.wait_idle().await.map_err(backend_error)?;
    let mut hashes = vec![value.hash];
    if value.format == BlobFormat::HashSeq
        && store.native.has(value.hash).await.map_err(backend_error)?
    {
        let mut children = store
            .native
            .export_bao(value.hash, bao_tree::ChunkRanges::all())
            .hashes();
        while let Some(child) = children.next().await {
            hashes.push(child.map_err(backend_error)?);
        }
    }
    if let Some(options) = store.options.clone() {
        tokio::task::spawn_blocking(move || -> std::io::Result<()> {
            for hash in hashes {
                for path in [
                    options.path.data_path(&hash),
                    options.path.outboard_path(&hash),
                    options.path.sizes_path(&hash),
                    options.path.bitfield_path(&hash),
                ] {
                    match std::fs::File::open(path) {
                        Ok(file) => file.sync_all()?,
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                        Err(error) => return Err(error),
                    }
                }
            }
            std::fs::File::open(&options.path.data_path)?.sync_all()?;
            std::fs::File::open(&options.path.temp_path)?.sync_all()?;
            if let Some(root) = options.path.data_path.parent() {
                std::fs::File::open(root)?.sync_all()?;
            }
            Ok(())
        })
        .await
        .map_err(backend_error)??;
    }
    store.native.sync_db().await.map_err(backend_error)
}
