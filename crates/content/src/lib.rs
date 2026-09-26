//! Content-addressed storage and immutable content packages for Ontography.
//!
//! [`content`] retains and verifies raw blobs, [`package`] composes them into
//! immutable file, collection, and change packages, and [`durability`] supplies
//! the file barrier an object store crosses before publishing a ledger
//! reference to retained bytes.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod content;
pub mod durability;
pub mod package;

pub use content::{ContentError, ContentId, ContentMetadata, ContentReader, ContentStore};
pub use package::{
    PackageDocument, PackageEnvelope, PackageError, PackageLimits, PackageStore, ResolvedEntry,
    ResolvedEntryKind, ResolvedPackage,
};
