//! The file barrier missing from iroh-blobs 0.103.0's local import path.
//!
//! The storage gate serializes durable publication with garbage collection.
//! Imports use owned copies and stable `Options` for the store lifetime. After an import
//! and its persistent tag complete, fence their files here, then await
//! `FsStore::sync_db()` before publishing a ledger reference. This module must
//! be reviewed when upgrading iroh's import or file layout implementation.

use std::fs::{self, File};
use std::io::{self, Read};
use std::path::Path;

use bao_tree::io::outboard::PreOrderOutboard;
use bao_tree::io::sync::valid_ranges;
use bao_tree::{BaoTree, ChunkNum, ChunkRanges};
use iroh_blobs::Hash;
use iroh_blobs::store::IROH_BLOCK_SIZE;
use iroh_blobs::store::fs::options::Options;

/// Fence the files of a completed owned import, using its verified payload.
///
/// Placement follows the configured thresholds, rather than treating a missing
/// file as evidence that its contents were inlined. Compare the data and verify
/// its outboard as upstream can log a failed rename and continue with an
/// existing destination. Callers must subsequently await `sync_db()`.
///
/// # Errors
///
/// Fails when an owned file is missing or has the wrong size, its data differs
/// from `payload`, its outboard does not verify, or a sync fails.
pub fn sync_import(options: &Options, hash: Hash, payload: &[u8]) -> io::Result<()> {
    let size = payload.len() as u64;
    let tree = BaoTree::new(size, IROH_BLOCK_SIZE);
    let owns_data = !options.is_inlined_data(size);
    let outboard_size = tree.outboard_size();
    let owns_outboard = !options.is_inlined_outboard(outboard_size);
    if owns_data {
        let path = options.path.data_path(&hash);
        let mut file = open_owned_file(&path, size)?;
        compare_data(&mut file, payload).map_err(|error| at_path(&path, error))?;
        file.sync_all().map_err(|error| at_path(&path, error))?;
    }
    if owns_outboard {
        let path = options.path.outboard_path(&hash);
        let file = open_owned_file(&path, outboard_size)?;
        verify_outboard(&file, tree, hash, payload).map_err(|error| at_path(&path, error))?;
        file.sync_all().map_err(|error| at_path(&path, error))?;
    }
    if owns_data || owns_outboard {
        sync_directories(options)?;
    }
    // Fully inlined imports publish no filenames. Store initialization already
    // fenced these directories; their content needs only the database barrier.
    Ok(())
}

/// Fence a complete import after the caller has incrementally verified all its
/// Bao chunks. File sizes and ownership are checked independently of placement.
/// The caller keeps the storage mutation gate and subsequently syncs the DB.
pub(crate) fn sync_verified(options: &Options, hash: Hash, size: u64) -> io::Result<()> {
    let tree = BaoTree::new(size, IROH_BLOCK_SIZE);
    if !options.is_inlined_data(size) {
        let path = options.path.data_path(&hash);
        open_owned_file(&path, size)?
            .sync_all()
            .map_err(|e| at_path(&path, e))?;
    }
    let outboard_size = tree.outboard_size();
    if !options.is_inlined_outboard(outboard_size) {
        let path = options.path.outboard_path(&hash);
        open_owned_file(&path, outboard_size)?
            .sync_all()
            .map_err(|e| at_path(&path, e))?;
    }
    sync_directories(options)
}

/// Persist owned-file renames and creation of the data and temporary directories.
/// The caller separately fences creation of the enclosing store directory.
///
/// # Errors
///
/// Fails when a store directory cannot be opened or synced.
pub fn sync_directories(options: &Options) -> io::Result<()> {
    let data = &options.path.data_path;
    let temporary = &options.path.temp_path;
    sync_directory(data)?;
    if temporary != data {
        sync_directory(temporary)?;
    }
    let parent = data
        .parent()
        .ok_or_else(|| invalid("data directory has no parent"))?;
    sync_directory(parent)?;
    let temporary_parent = temporary
        .parent()
        .ok_or_else(|| invalid("temporary directory has no parent"))?;
    if temporary_parent != parent {
        sync_directory(temporary_parent)?;
    }
    Ok(())
}

fn open_owned_file(path: &Path, expected_size: u64) -> io::Result<File> {
    let metadata = fs::symlink_metadata(path).map_err(|error| at_path(path, error))?;
    if !metadata.is_file() {
        return Err(at_path(path, invalid("expected a regular owned file")));
    }
    let file = File::open(path).map_err(|error| at_path(path, error))?;
    if file.metadata().map_err(|error| at_path(path, error))?.len() != expected_size {
        return Err(at_path(
            path,
            invalid("owned file has an unexpected length"),
        ));
    }
    Ok(file)
}

/// Compare a stored copy against the imported payload in bounded chunks, and
/// require the copy to end where the payload ends.
///
/// # Errors
///
/// Fails when `stored` cannot be read, differs from `payload`, or does not end
/// where the payload ends.
pub fn compare_data(stored: &mut impl Read, payload: &[u8]) -> io::Result<()> {
    let mut buffer = vec![0_u8; 64 * 1024];
    for expected in payload.chunks(buffer.len()) {
        let actual = &mut buffer[..expected.len()];
        stored.read_exact(actual)?;
        if actual != expected {
            return Err(invalid("stored data differs from the imported payload"));
        }
    }
    if stored.read(&mut buffer[..1])? != 0 {
        return Err(invalid("stored data is longer than the imported payload"));
    }
    Ok(())
}

fn verify_outboard(file: &File, tree: BaoTree, hash: Hash, payload: &[u8]) -> io::Result<()> {
    let outboard = PreOrderOutboard {
        tree,
        root: hash.into(),
        data: file,
    };
    let mut verified = ChunkNum(0);
    for range in valid_ranges(outboard, payload, &ChunkRanges::all()) {
        let range = range?;
        if range.start != verified {
            return Err(invalid("outboard does not verify the complete payload"));
        }
        verified = range.end;
    }
    if verified != tree.chunks() {
        return Err(invalid("outboard does not verify the complete payload"));
    }
    Ok(())
}

#[cfg(unix)]
fn sync_directory(path: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(path).map_err(|error| at_path(path, error))?;
    if !metadata.is_dir() {
        return Err(at_path(path, invalid("expected an owned directory")));
    }
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| at_path(path, error))
}

#[cfg(not(unix))]
fn sync_directory(path: &Path) -> io::Result<()> {
    Err(at_path(
        path,
        io::Error::new(
            io::ErrorKind::Unsupported,
            "durable iroh directory synchronization is implemented only on Unix",
        ),
    ))
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn at_path(path: &Path, error: io::Error) -> io::Error {
    io::Error::new(error.kind(), format!("{}: {error}", path.display()))
}

#[cfg(all(test, unix))]
mod tests {
    use bao_tree::io::outboard::PreOrderMemOutboard;

    use super::*;

    struct StoreDirectory {
        root: std::path::PathBuf,
        options: Options,
    }

    impl StoreDirectory {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "ontography-iroh-durability-{}",
                uuid::Uuid::new_v4()
            ));
            let options = Options::new(&root);
            fs::create_dir_all(&options.path.data_path).unwrap();
            fs::create_dir_all(&options.path.temp_path).unwrap();
            Self { root, options }
        }

        fn write_import(&self, payload: &[u8]) -> Hash {
            let outboard = PreOrderMemOutboard::create(payload, IROH_BLOCK_SIZE);
            let hash = outboard.root.into();
            if !self.options.is_inlined_data(payload.len() as u64) {
                fs::write(self.options.path.data_path(&hash), payload).unwrap();
            }
            if !self.options.is_inlined_outboard(outboard.data.len() as u64) {
                fs::write(self.options.path.outboard_path(&hash), outboard.data).unwrap();
            }
            hash
        }
    }

    impl Drop for StoreDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn empty_and_inline_imports_do_not_require_files() {
        let store = StoreDirectory::new();
        for payload in [Vec::new(), vec![7; 16 * 1024]] {
            sync_import(&store.options, Hash::new(&payload), &payload).unwrap();
        }
        assert_eq!(
            fs::read_dir(&store.options.path.data_path).unwrap().count(),
            0
        );
    }

    #[test]
    fn required_data_cannot_be_missing_truncated_or_changed() {
        let store = StoreDirectory::new();
        let payload = vec![7; 16 * 1024 + 1];
        let hash = Hash::new(&payload);
        let path = store.options.path.data_path(&hash);
        let result = sync_import(&store.options, hash, &payload);
        assert_eq!(result.unwrap_err().kind(), io::ErrorKind::NotFound);
        fs::write(&path, &payload[..payload.len() - 1]).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
        fs::write(&path, vec![8; payload.len()]).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
        store.write_import(&payload);
        sync_import(&store.options, hash, &payload).unwrap();
    }

    #[test]
    fn required_outboard_cannot_be_missing_truncated_or_corrupt() {
        let mut store = StoreDirectory::new();
        store.options.inline.max_outboard_inlined = 0;
        let payload = vec![7; 32 * 1024 + 1];
        let hash = store.write_import(&payload);
        sync_import(&store.options, hash, &payload).unwrap();
        let path = store.options.path.outboard_path(&hash);
        let mut outboard = fs::read(&path).unwrap();
        fs::remove_file(&path).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::NotFound
        );
        fs::write(&path, &outboard[..outboard.len() - 1]).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
        outboard[0] ^= 1;
        fs::write(&path, &outboard).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn inline_data_can_have_a_required_outboard() {
        let mut store = StoreDirectory::new();
        store.options.inline.max_data_inlined = 64 * 1024;
        store.options.inline.max_outboard_inlined = 0;
        let payload = vec![4; 32 * 1024];
        let hash = store.write_import(&payload);
        assert!(!store.options.path.data_path(&hash).exists());
        sync_import(&store.options, hash, &payload).unwrap();
    }

    #[test]
    fn owned_file_symlinks_and_missing_directories_fail_closed() {
        let store = StoreDirectory::new();
        let payload = vec![7; 16 * 1024 + 1];
        let hash = Hash::new(&payload);
        let external = store.root.join("external");
        fs::write(&external, &payload).unwrap();
        std::os::unix::fs::symlink(&external, store.options.path.data_path(&hash)).unwrap();
        assert_eq!(
            sync_import(&store.options, hash, &payload)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
        fs::remove_dir(&store.options.path.temp_path).unwrap();
        assert_eq!(
            sync_directories(&store.options).unwrap_err().kind(),
            io::ErrorKind::NotFound
        );
    }
}
