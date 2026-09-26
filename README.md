# Ontography core

Rust library extracted from Ontography revision
`a78384bc0c458e6559716b22a8f99a1ae4c540fa`, immediately before session-origin.
The source began as an unchanged extraction, including the application and
workspace APIs present at that revision. This checkout now also contains QA
probes and a fix for duplicate keys in native application JSON.

## Workspace layout

The repository is a Cargo workspace. The root package `ontography-core` is a
facade whose Rust crate name remains `ontography`; it re-exports the public
names of the member crates unchanged, so the original imports keep working.
The members build on one another in this order:

| Package | Path | Contents | Depend on it for |
| --- | --- | --- | --- |
| `ontography-calculus` | `crates/calculus` | Graph declarations, the kernel, and the storage adapter contract in `ontography_calculus::storage` (the package and frontier views, the transition and its verifier, the checkpoint and its error, the fragment encoding, and the record and identity types an adapter stores; the facade re-exports it as `ontography::storage`). Depends only on `serde`, `sha2`, `thiserror`, and `uuid`. | Modelling or verifying workflow law without any I/O. |
| `ontography-content` | `crates/content` | Content-addressed blob storage over the vendored `iroh-blobs`, immutable content packages, and the file durability barrier. | Retaining, verifying, or reading content and packages. |
| `ontography-runtime` | `crates/runtime` | Persistent proposal sessions (SQLite plus the object store), invocation context, activity reporting, and opaque execution hosting. | Running and persisting a workflow. |
| `ontography-workspace` | `crates/workspace` | Private copy-on-write checkouts of content packages, cloned from a shared verified baseline cache, and capture of a checkout's edits back into a `Changes` package. Unix only. | Giving a process a filesystem view of a package. |
| `ontography-application` | `crates/application` | Executable components bound to kernel configuration, JSON application and project authoring, and the running application. | Composing and launching an application. |

Use the facade from a sibling Rust project:

```toml
[dependencies]
ontography = { package = "ontography-core", path = "../ontography-core" }
```

Depend on a member directly when a smaller dependency closure matters, for
example `ontography-calculus = { path = "../ontography-core/crates/calculus" }`.

Dependency versions, lints, and the pinned toolchain are set once at the
workspace root; every member inherits them and disables registry publication.
The vendored `iroh-blobs` comes from the same upstream revision and retains its
original licenses and patch notes. Local path and Git dependencies are
supported.

Run the retained tests with `cargo test --workspace`. The integration tests
under `tests/` compile against the facade. Two tests are ignored: the orphan
retention probe documents a known failure (see
[CORE_QA_RESEARCH.md](CORE_QA_RESEARCH.md)), and the wide fan-out restoration
probe in `tests/calculus.rs` is a scalability run meant for release mode.

## Retirement, locality, and extension

Every package is exactly one of live, consumed, or retired. A retirement is a
canonical record with reason, revision, and optional evidence; the retired
package's holder and phase are derived from its record, never stored twice.
`Kernel::retire` and `SessionHandle::retire` retire one live package explicitly.
Rewrite cleanup is local: an `Out` package is rechecked only when its holder's
outgoing edge set changed, and an `In` receipt at an `All` receiver is retired
as `RouteRemoved` when its delivery edge leaves the incoming set, so rewrites
with disjoint footprints commute. `Kernel::prepare_extension` and
`SessionHandle::extend` add schema vocabulary and contracts without touching
the graph or frontier. Persistent stores are schema version 10; older stores
are refused on open, not migrated.
