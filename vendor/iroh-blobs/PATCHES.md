# Local patches to iroh-blobs 0.103.0

Source: the [published 0.103.0 crate](https://crates.io/crates/iroh-blobs/0.103.0),
upstream commit [`e82cbdcbdac9a78033174aad55e3199b2cf4c0dc`](https://github.com/n0-computer/iroh-blobs/tree/e82cbdcbdac9a78033174aad55e3199b2cf4c0dc).
Archive SHA-256: `5be50b0e2d0a9ba65cee4e0dfb708b3704e02ad12bd4c14c6307e94245943126`.
The upstream source, manifests, build script, licenses, examples, tests, and
documentation are retained. Development automation files are omitted.

## Runtime shutdown

The change in `src/store/fs.rs`, `RtWrapper::drop`:

```diff
-            tokio::task::block_in_place(|| {
-                drop(rt);
-            });
+            // This wrapper can be dropped by a task on the runtime it owns.
+            // Waiting for that runtime here would wait for this task itself.
+            rt.shutdown_background();
```

Both failed initialization and normal actor exit can drop the wrapper from a
task on the runtime it owns. Waiting for runtime shutdown from that task
deadlocks. This caused competing opens to hang and completed stores to retain
blocked threads. `shutdown_background` initiates shutdown without waiting for
the current task. Work already running in blocking tasks can finish afterward;
this change does not add a synchronous thread-join guarantee.

This patch does not change the blob format, import completion, or durability.
Ontography still drains its store worker, explicitly shuts down the database,
and fences content files and metadata before committing ledger references.
Review and remove this patch when adopting an upstream release with corrected
runtime cleanup.

Validation: an isolated macOS probe rejected competing-owner and corrupt-database
initialization promptly. After 24 open/read/write/sync/shutdown/drop cycles,
the process returned to its initial thread count (one thread). This checks
resource cleanup, not hardware power-loss durability.

## Coordinated garbage collection

`src/store/mod.rs` re-exports the existing `gc_run_once` function:

```diff
-pub use gc::{GcConfig, ProtectCb, ProtectOutcome};
+pub use gc::{gc_run_once, GcConfig, ProtectCb, ProtectOutcome};
```

Ontography must serialize collection with publication and retention changes,
validate collection roots before deletion, and report completion to callers.
The upstream background-only entry point does not expose that boundary. This
export lets Ontography call the existing collector while holding its mutation
gate and supplying additional protected hashes. It changes no collection
algorithm, network protocol, or disk format. Graph payloads and committed artifact
dependencies remain pinned; caller-released artifacts can be collected.

The content integration tests exercise release, collection-member retention,
active-reader protection, and committed dependencies surviving collection and
reopen. Review this export when upgrading to an upstream public collection API.
