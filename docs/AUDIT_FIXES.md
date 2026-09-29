# September 2026 audit changes

The audit exposed failures beyond the original debug-only suite. The following
changes retain the existing cleanup and authority model while strengthening its
integrity and ownership boundaries.

Filesystem workspace handling and its regressions now live in the application.
Core retains package composition and independently scoped staged imports; the
workspace-specific rows below describe the historical audit fixes.

| Finding | Change and regression coverage |
| --- | --- |
| Release builds skipped retirement bookkeeping inside `debug_assert!` | The insertion executes in every profile. CI runs debug and release tests and denies `clippy::debug_assert_with_mut_call`. Existing removed-holder rewrites exercise both appliers. |
| Rejected capture released other callers' same-hash content; invalid capture leaked imports | Captures hold independently scoped temporary pins until validation and publication. Failure drops only those pins. Core's `content_retention` covers existing artifacts, independent stages, and dropped package imports followed by GC; filesystem validation is tested in the application. |
| Faulted persistent sessions never resumed | Reopen validates the checkpoint, graph/invocation references, and committed content before clearing a fault. `persistent_recovery` exercises transient SQL failure with live work and refuses corrupted state. |
| Pre-commit object retention leaked after failed SQL publication | Ledger tags are reconciled with all committed graph and invocation references after faults and on every reopen. Ordinary import tags stay independent. `orphan_retention_probe` is enabled; recovery tests cover dependencies and context objects. |
| Forged views bypassed integrity and admission checks | Activation records store the execution node. Sealed activation/transfer transitions carry the exact input records proved during evaluation. Shared verification checks them, join authority, `HolderRemoved`, and surviving `All` routes. `verify_negative` pins rejection and unchanged state. |
| Stale direct plans were treated as corrupt | All direct prepare/commit APIs fence the predecessor first. Rewrite commits check validator identity as extension commits do. `prepared_plans` covers changed definitions and foreign validators. |
| Checkpoints lost definition changes or accepted duplicate retirement stamps | Checkpoints count every rewrite/extension and require exact revision accounting. Explicit retirement stamps are distinct and disjoint from structural stamps. |
| Transfer rejected without detail | `TransferRejection` distinguishes object-type, authority, and contract failure; evidence/storage errors keep their existing separate path. |
| Unicode normalization aliases passed workspace validation | Workspace collision keys normalize lowercase paths to NFC. Filesystem collision tests now live in the application; core's `package_names` pins exact package identities and member names. |
| Rewrite cost and commutation claims were too broad | Candidate edges are indexed and payload reads cached per package; the docs state full definition-admission cost and precise affected-holder independence. `frontier_rewrite` includes two real commuting edits and an overlapping-holder counterexample. |

## Compatibility and costs

Persistent graph stores now use schema **11**. As with previous schema changes,
older stores are refused; there is no automatic migration. The new columns
record activation execution nodes and the definition-change count.

The separately versioned invocation context store now uses schema **2** after
removal of the serialized workspace policy. Version 1 stores are refused by
both session reopening and read-only invocation inspection, without migration.

Direct API users must supply `node_id` to `Activation::new` and
`definition_changes` when constructing a `Checkpoint`. `TransitionKind` includes
input proof witnesses and next `All` routes. `TransferError::Rejected` now has
named `package` and `reason` fields. `ContentStore::stage_imports` provides
temporary retention for callers that validate content before accepting it.

Healthy reopen scans committed reference metadata and owned ledger tags to
recover crash-window orphans, in addition to readiness validation. Faulted
reopen also reads all committed payloads and validates the full checkpoint.
The reference scan grows with the ledger's recorded references and tag count;
routine reopen is therefore not independent of history size. Neither operation
replays historical validator code. Sessions explicitly closed by the caller
remain closed. Regressions inject SQL failures, exercise a failed durable fault
marker, and simulate retained objects before SQL publication with no marker.
An abrupt process kill in that window remains a separate durability experiment.

## Deliberate boundaries

The schema closes node types, object types, and authority tags. Edge types are
open semantic annotations. Package content IDs commit to exact bytes;
`PackageStore::put` writes a canonical encoding, while `get` accepts valid
alternate JSON encodings, so semantically equivalent imported documents can
have different IDs. Tests pin this distinction.

Explicit content import/release retains its per-hash artifact ownership model.
Independent temporary capture pins prevent one rejected capture from releasing
another caller's import; they do not assign a permanent owner to every import.

The edit policy, which has since replaced the rewrite grammar, remains trusted
and decides who may grant roots and authority transitions to added nodes. Cleanup remains non-monotone and aborts atomically when required
evidence or a validator fails. See the [frontier guide](FRONTIER_REWRITING.md)
for the exact conditions. Changing these semantics would require a separate
policy design, not an integrity fix.

Checkpoint restoration is a trusted-store integrity check. Its stored counters
do not independently prove the history; fixed-graph replay remains the path
that re-proves historical admission. Dynamic full-history replay and incremental
replacement-definition admission remain outside this change.
