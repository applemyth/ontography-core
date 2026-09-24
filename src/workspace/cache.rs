use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ContentId;
use crate::content::Hash;
use crate::package::{ResolvedEntryKind, ResolvedPackage};

use super::{CacheStats, Checkout, Result, WorkspaceError, WorkspaceStore, filesystem};

/// Clones share explicit ownership; no process-global pathname registry is needed.
#[derive(Debug)]
pub(super) struct SharedCache {
    root: PathBuf,
    cleanup_root: Option<PathBuf>,
    state: Arc<tokio::sync::Mutex<CacheStats>>,
}
impl SharedCache {
    pub(super) fn new(root: PathBuf) -> Self {
        Self {
            root,
            cleanup_root: None,
            state: Arc::new(tokio::sync::Mutex::new(CacheStats::default())),
        }
    }
    pub(super) fn for_run(run_path: Option<&Path>) -> Self {
        let root = run_path.map_or_else(
            || std::env::temp_dir().join(format!("ontography-workspaces-{}", uuid::Uuid::new_v4())),
            |path| path.join("workspaces"),
        );
        Self {
            root: root.join("bases"),
            cleanup_root: run_path.is_none().then_some(root),
            state: Arc::new(tokio::sync::Mutex::new(CacheStats::default())),
        }
    }
    pub(super) fn root(&self) -> &Path {
        &self.root
    }
    pub(super) async fn stats(&self) -> CacheStats {
        *self.state.lock().await
    }
}

impl Drop for SharedCache {
    fn drop(&mut self) {
        if let Some(root) = &self.cleanup_root {
            let _ = filesystem::remove_checkout(root);
        }
    }
}

fn permissions(path: &Path, mode: u32) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
    }
    #[cfg(not(unix))]
    {
        let mut permissions = fs::metadata(path)?.permissions();
        permissions.set_readonly(mode & 0o200 == 0);
        fs::set_permissions(path, permissions)?;
    }
    Ok(())
}
fn private_directory(path: &Path) -> Result<()> {
    match fs::create_dir(path) {
        Ok(()) => permissions(path, 0o700)?,
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
            let metadata = fs::symlink_metadata(path)?;
            if !metadata.is_dir() || metadata.file_type().is_symlink() {
                return Err(WorkspaceError::Invalid(format!(
                    "cache path is not a real directory: {}",
                    path.display()
                )));
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if metadata.permissions().mode() & 0o077 != 0 {
                    return Err(WorkspaceError::Invalid(format!(
                        "cache directory is not private: {}",
                        path.display()
                    )));
                }
            }
        }
        Err(e) => return Err(e.into()),
    }
    Ok(())
}
fn initialize(root: &Path) -> Result<()> {
    if let Some(parent) = root.parent() {
        fs::create_dir_all(parent)?;
    }
    private_directory(root)?;
    private_directory(&root.join("blobs"))
}
fn verify_file(path: &Path, id: ContentId) -> Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.len() != id.size() {
        return Err(WorkspaceError::Invalid(format!(
            "invalid clone file: {}",
            path.display()
        )));
    }
    let mut file = fs::File::open(path)?;
    let mut bytes = Vec::new();
    (&mut file)
        .take(id.size().saturating_add(1))
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != id.size() || Hash::new(&bytes) != id.hash() {
        return Err(WorkspaceError::Invalid(format!(
            "cache/clone hash mismatch: {}",
            path.display()
        )));
    }
    Ok(())
}

struct TemporaryFile(PathBuf);
impl Drop for TemporaryFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn cached_blob(store: &WorkspaceStore, id: ContentId, stats: &mut CacheStats) -> Result<PathBuf> {
    let target = store.cache.root.join("blobs").join(id.hash().to_string());
    match fs::symlink_metadata(&target) {
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            let temporary = TemporaryFile(
                store
                    .cache
                    .root
                    .join("blobs")
                    .join(format!(".export-{}", uuid::Uuid::new_v4())),
            );
            // This function runs only on the blocking pool. Cancellation leaves
            // the job owning its paths until export/cleanup actually completes.
            tokio::runtime::Handle::current()
                .block_on(store.content.export_file(id, &temporary.0))?;
            stats.file_exports += 1;
            permissions(&temporary.0, 0o444)?;
            match fs::hard_link(&temporary.0, &target) {
                Ok(()) => {}
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(e) => return Err(e.into()),
            }
        }
        Err(e) => return Err(e.into()),
    }
    let metadata = fs::symlink_metadata(&target)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || !metadata.permissions().readonly()
        || metadata.len() != id.size()
    {
        return Err(WorkspaceError::Invalid(format!(
            "invalid immutable cached file: {}",
            target.display()
        )));
    }
    // Verify the actual private clone below, avoiding a second full hash read.
    Ok(target)
}

fn checkout_blocking(
    store: &WorkspaceStore,
    package: &ResolvedPackage,
    destination: &Path,
    stats: &mut CacheStats,
) -> Result<Checkout> {
    initialize(&store.cache.root)?;
    let name = destination
        .file_name()
        .ok_or_else(|| WorkspaceError::Invalid("checkout destination needs a basename".into()))?;
    let parent = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let path = fs::canonicalize(parent)?.join(name);
    if path.starts_with(fs::canonicalize(&store.cache.root)?) {
        return Err(WorkspaceError::Invalid(
            "checkout destination is inside baseline cache".into(),
        ));
    }
    fs::create_dir(&path)?;
    let checkout = Checkout {
        path: path.clone(),
        removed: false,
        _cache: Arc::clone(&store.cache),
    };
    permissions(&path, 0o700)?;
    for entry in package.entries().iter().filter(|e| !e.path.is_empty()) {
        let target = path.join(&entry.path);
        match &entry.kind {
            ResolvedEntryKind::Directory => {
                // Existing names include aliases on case/normalization-insensitive
                // filesystems. Never silently merge two logical directories.
                fs::create_dir(&target)?;
                permissions(&target, 0o700)?;
            }
            ResolvedEntryKind::File {
                content,
                executable,
            } => {
                let source = cached_blob(store, *content, stats)?;
                reflink_copy::reflink(&source, &target).map_err(|source| {
                    WorkspaceError::UnsupportedCopyOnWrite {
                        path: target.clone(),
                        source,
                    }
                })?;
                stats.cloned_files += 1;
                #[cfg(unix)]
                {
                    use std::os::unix::fs::MetadataExt;
                    let from = fs::metadata(&source)?;
                    let to = fs::metadata(&target)?;
                    if (from.dev(), from.ino()) == (to.dev(), to.ino()) || to.nlink() != 1 {
                        return Err(WorkspaceError::Invalid(
                            "OS clone did not produce an independent inode".into(),
                        ));
                    }
                }
                verify_file(&target, *content)?;
                permissions(&target, if *executable { 0o755 } else { 0o644 })?;
            }
            ResolvedEntryKind::Symlink { .. } => {}
        }
    }
    for entry in package.entries() {
        if let ResolvedEntryKind::Symlink { target } = &entry.kind {
            #[cfg(unix)]
            std::os::unix::fs::symlink(target, path.join(&entry.path))?;
            #[cfg(not(unix))]
            {
                let _ = target;
                return Err(WorkspaceError::Invalid(
                    "symlink checkout requires Unix".into(),
                ));
            }
        }
    }
    filesystem::validate_materialized_links(&path, package)?;
    Ok(checkout)
}

pub(super) async fn checkout(
    store: &WorkspaceStore,
    package: &ResolvedPackage,
    destination: &Path,
) -> Result<Checkout> {
    // Move the owned lock into the blocking job: dropping the awaiting future
    // must not unlock a cache while its filesystem job is still running.
    let mut stats = Arc::clone(&store.cache.state).lock_owned().await;
    let store = store.clone();
    let package = package.clone();
    let destination = destination.to_owned();
    let git = package.entries().iter().any(|entry| entry.path == ".git");
    let checkout = tokio::task::spawn_blocking(move || {
        checkout_blocking(&store, &package, &destination, &mut stats)
    })
    .await
    .map_err(|error| WorkspaceError::Invalid(error.to_string()))??;
    if git {
        super::git::rebuild_index(checkout.path()).await?;
    }
    Ok(checkout)
}
