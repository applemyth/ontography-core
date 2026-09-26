# Core calculus QA research — 24 September 2026

This is a hypothesis register and test plan for the extracted `ontography-core`
snapshot at `87e9600`. It separates **observed behavior**, **source-derived
limits**, and **unexecuted hypotheses**. It does not treat passing examples as a
proof that every reachable state is correct.

## Evidence and scope

The extracted commit has 33 tracked files and originally had no `Cargo.toml`,
integration suite, or mathematical definition. A local manifest, lockfile,
toolchain pin, and vendored dependency were added to the workspace during this
study. The initial temporary Cargo harness used the sibling `ontography-app`
dependency manifest and its vendored `iroh-blobs`, while compiling this
snapshot's `src/lib.rs`. Build output stayed in `/tmp`.

| Test binary (`cargo test --offline --workspace`, 26 September 2026) | Result | Qualification |
| --- | --- | --- |
| In-source unit tests: calculus 9, content 8, runtime 23, workspace 1 | 41 passed | Exhaustive cleanup worlds, fragment-encoding golden bytes, object-store retention and release, session fault classification, corrupt-evidence and context-store fault rules, the canonical retry commitment. |
| [Ported calculus suite](tests/calculus.rs) | 52 passed, 1 ignored | The ignored wide fan-out restoration probe is a scalability run meant for release mode. |
| [Adapter equivalence](tests/adapter_equivalence.rs) | 1 passed | Twelve seeds of 120 random steps comparing the `SQLite` adapter with the in-memory state, including stale plans, node reaping, poisoned outgoing edges (`NoAcceptingEdge`), and rejected rewrites and extensions. |
| [Negative verification](tests/verify_negative.rs) | 4 passed | Forged views drive every evaluator; `State::apply` against the true state rejects with the exact `ApplyError`. |
| [Rule coverage](tests/rule_coverage.rs) and [definition errors](tests/definition_errors.rs) | 10 and 4 passed | Admission rules without a dedicated test elsewhere, and every `DefinitionError` variant pinned by name. |
| [Frontier rewrite](tests/frontier_rewrite.rs) and [outbound admission](tests/outbound_admission.rs), with their helper module | 9 and 6 passed | The sibling suites, now retained in this checkout. |
| [Public API probes](tests/hypothesis_probes.rs) | 7 passed | Retained from the original study. |
| [Application API probes](tests/api_surface_probes.rs) | 4 passed | Root creation, caller scope, rewrite-grammar ownership, and nested JSON duplicate-key behavior. |
| [Application authoring](tests/application_authoring.rs), [lifecycle](tests/application_lifecycle.rs), and [extension](tests/application_extension.rs) | 3, 2, and 1 passed | Format parity, start-failure closure and resume drift, vocabulary extension of a running application. |
| [Content-composition probe](tests/content_composition_probe.rs) | 1 passed | Workspace capture reuses an unchanged file, emits a small package envelope, and commits the declared content closure. |
| [Frontier operation probes](tests/frontier_operations.rs) | 4 passed | Explicit retirement, `All` route removal, disjoint-rewrite commutativity, vocabulary extension. |
| [Persistent frontier probe](tests/persistent_frontier.rs) | 1 passed | Retirement records and an extension survive reopen with an exact snapshot. |
| [Desired orphan-reclamation regression](tests/orphan_retention_probe.rs) | 1 ignored | It asserts reclamation and currently fails if enabled. |

The workspace total is 150 passed, 0 failed, 2 ignored; `cargo fmt --check`,
strict all-target Clippy, and `cargo doc` also pass. The earlier harness
counts (50 native passes, 107 temporary-harness passes) are superseded and
must not be added to this total. The sibling source has diverged, notably in
session triggers and later runtime features. Its [mathematical definition](../ontography-app/MATHEMATICAL_DEFINITION.md)
and [frontier rewrite design](../ontography-app/docs/FRONTIER_REWRITING.md)
are specification candidates, not independent certification of this snapshot.
The mathematical definition expressly limits its restoration theorem to the
fixed-graph sublanguage.

## Hypothesis selection method

I use Bennett's [*The Optimal Choice of Hypothesis Is the Weakest, Not the
Shortest*](https://arxiv.org/html/2301.12987v4) as a way to select new probes.
The paper defines weakness by the size of a hypothesis's semantic extension,
among hypotheses that already fit a known task. It does not define a software
QA algorithm. Its optimality claim assumes a finite language and a uniform
distribution of tasks; production workflows meet neither assumption in full.

For this study, a bounded situation is a graph, its current frontier/history,
an operation sequence, an API layer, and an evidence/storage condition. A
decision is the observable acceptance/rejection, next graph, history, frontier,
error, and durable state. Existing tests are the known child task. To generate a
parent task, remove a context restriction from a claim that fits those examples
and select a held-out situation where the broader claim and a context-bound
rival disagree. Examples:

| Known examples suggest | Broader held-out question | Discriminating case |
| --- | --- | --- |
| Delivered packages survive a rewrite preserving their holder and route. | Does holder survival alone suffice? | Replace the receipt's edge at an `All` node. |
| A local rewrite works with short history. | Is its cost local to the changed graph/frontier? | Keep the live frontier fixed; grow only consumed history. |
| A persistent fixed-graph run can be fully replay-verified. | Is every durable run independently verifiable? | Persist a transfer and rewrite, then request verified reopen. |
| Root authority is checked for a hosted node. | Does the caller's node identity constrain raw submission? | Have node B submit a legal root for entry A. |

The extension comparison is bounded to declared axes. Risk and impact, rather
than the paper's uniform prior, determine test order. Every proposed test must
state its oracle before execution and retain a reduced counterexample if it
fails.

For one deliberately small comparison, hold `phase=In` and `holder=survives`
fixed, and let the receipt's edge be `{unchanged, replaced}`. A model that
requires the edge to remain unchanged covers one context cell; a model that
requires only holder survival covers both. The existing unchanged-edge case
fits both. The replaced-edge probe distinguishes them: holder survival alone suffices at an
`Any` receiver, while an `All` receiver additionally requires the delivery edge
to remain in its incoming set, and the kernel now retires the receipt as
`RouteRemoved` otherwise (O2). These two cells
are an engineering analogue of extension size, not the paper's full semantic
extension or a production probability estimate.

## Capability inventory through several frames

The same kernel can be viewed as a colored-token flow system (packages and
joins), an authority system (root ceilings and transitions), a causal history
(activation DAG), a graph surgery system (L/K/R rewrites and cleanup), and a
durable state machine (session and object store). Each frame exposes different
questions.

| Workflow use | Kernel expression | Boundary to test |
| --- | --- | --- |
| Parallel review and fan-out | One activation emits distinct packages; `Any` receives one and `All` receives one per concrete incoming edge. | Two-of-three quorum, optional reviewers, cancellation, and timeout are not native ingress modes. |
| Gated deployment or release | Carried authority, exact transition rules, edge matching, immutable payload commitments. | A tag is not caller authentication; a rootable `All` node can still root without review inputs. |
| Long-running adaptive routing | Outbound birth, explicit transfer, registered rewrite, frontier cleanup. | Rewrite/transfer order changes fate for overlapping rewrites; a removed route retires an `All` receipt as `RouteRemoved`. |
| Audit and provenance | Unique producer, at most one consumer, activation DAG, fixed-graph verified restoration. | Dynamic rewrite/transfer history has trusted current-state reopen but no full public replay verification. |
| Human or machine work queue | Durable sessions, pending pages, revision notifications, content store. | Scheduling, retries, external effects, and worker identity belong to the host, not the calculus. |
| Multi-tenant or multi-entry workflow | Direct kernel accepts several root rules. | Application authoring declares one entry; caller identity is outside direct admission. |
| Versioned artifact workflow | A content `Collection` refers to prior file packages; `Changes` refers to a base and replacements; a workflow payload can carry a small package envelope. | Composition is explicit and file-granular; historical bases remain retained, and graph-package ancestry alone does not compose payload bytes. |

This inventory is about expressibility, not a claim that each example is a
complete product. For example, an approval workflow needs an application policy
for quorum and an external identity system for people.

### Preliminary API parity

The direct `Kernel` API is public and broad. `SessionHandle` exposes submission,
transfer, and prepared rewrite. `RunningApplication::session()` exposes that
handle to the run owner. The declarative and hosted-component layers have
deliberately narrower control:

| Capability | Direct kernel / session | Builder and application | JSON / concise project |
| --- | --- | --- | --- |
| Several independent roots | Yes | One entry root | One entry root |
| `Any`/`All`, authority rules, exact contracts | Yes | Yes for initially placed graph | Yes for initially declared graph |
| Outbound birth and later transfer | Yes | Component can emit; run owner transfers through session | Depends on implementation code and run owner |
| Rewrite with a grammar | Kernel checks caller-supplied grammar; runtime can hold one | `Application::with_grammar` and run session | No grammar declaration found |
| Automatically launch a newly added node | Host can be launched explicitly | Original bindings alone are launched | No automatic dynamic binding found |
| Reserve unused node types/tags for a future graph | Explicit schema | Schema derived from initial placements | Same builder path |
| Independently verify a dynamic run's full history | No public full replay path found | No additional path found | No additional path found |
| Reuse prior artifact content in a new package | `PackageStore` collection/changes and `submit_with_content` | `WorkspaceStore::capture` and `PreparedWorkspace::finish` | The artifact model is reached through implementation code, not declared directly in these formats |

The hosted API also exposes two different submission contracts. Raw
`ApplicationContext::submit` accepts any proposal the kernel admits, regardless
of which component called it. `begin_invocation` binds the caller's node and
constructs its proposal from that binding. Both are public, so callers must
choose the trust model deliberately.

This matrix is a source-level reachability assessment except for the two root
and isolated-tag rows exercised below. It distinguishes a missing high-level
declaration from a missing calculus operation.

## Confirmed public behavior in this snapshot

**O1 — Cleanup is local to the rewrite** (revised 25 September 2026). An
outbound package born with no accepting route survives an L=K=R rewrite of the
same graph, which retires nothing and advances the revision. It is rechecked,
and retired as `NoAcceptingEdge`, only by a rewrite that changes its holder's
outgoing edge set, whether by removal or addition. Probes:
`identity_graph_rewrite_retains_unroutable_outbound_work` and
`changing_the_holders_outgoing_edges_rechecks_outbound_work`; the operative
code is [cleanup](crates/calculus/src/kernel/frontier.rs) and
[rewrite preparation](crates/calculus/src/kernel/rewrite.rs).

**O2 — A receipt at an `All` receiver is retired when its delivery edge leaves
the incoming set** (revised 25 September 2026). Deliver on `e1` to B, then
rewrite `e1` into fresh `e2` while preserving B. Cleanup retires the `In`
package as `RouteRemoved`, records the retirement, and the frontier is
quiescent. Edge IDs cannot be reused and a surviving node cannot change ingress
mode, so no later operation could have consumed it. An `Any` receiver keeps its
receipt. Probe: `replacing_an_all_join_edge_retires_the_stranded_receipt`.

**O3 — Root expressiveness narrows at the application builder.** A direct
kernel admitted and activated two independent roots. The application builder
installed only its entry root, even when the second placed component carried a
root authority policy. Its API documents the single-entry rule. This is an
API capability difference, not a kernel admission failure.

**O4 — Transfer and rewrite order changes work survival.** Transferring an
outbound package through `e1` before deleting `e1` leaves a live `In` receipt
at its surviving receiver. Deleting the route first retires the `Out` package,
and later transfer rejects. Both traces end with the same graph fingerprint.
The public probe checks both outcomes.

**O5 — The builder cannot reserve a tag for an isolated root.** The direct
kernel admits a root with `route` authority and no initial edge. The application
builder derives schema authority tags from placed edges, so the same isolated
entry returns `RootAuthorityOutsideSchema`. This prevents a builder-authored
application from reserving an unused tag for future rewrites through its current
API.

**O6 — A failed SQL commit can leave unreferenced content retained by ordinary garbage collection.**
In an isolated persistent run, a SQL trigger rejected the mutation revision
update after an activation's result bytes had been written. SQLite contained no
activation afterward. Reopening the run showed the payload was still readable;
`ContentStore::collect_garbage()` left it readable. The diagnostic passed on
this snapshot. The retained regression test asserts the desired absence after
collection and is ignored until reclamation is fixed. The relevant order is
`objects.put_all` before `transaction.commit` in
[SQLite submission](crates/runtime/src/sqlite.rs), persistent named tags in
[object storage](crates/runtime/src/object_store/iroh.rs), and garbage collection
marking every tag in [content.rs](crates/content/src/content.rs). A process crash in that same
window needs its own separate probe; the injected SQL failure establishes the
retention path without simulating a crash. Reconciliation must distinguish
unreferenced activation payload tags from intentionally retained content tags.

**O7 — Application start supplies input but creates no activation itself.** A
no-op entry component left the session's activation history empty. In a second
run, a non-entry worker used raw `ApplicationContext::submit` to create a legal
root at the entry node. That worker could not obtain a root-bound invocation for
itself. This verifies the documented separation between trusted raw submission
and node-bound invocation; it is not a demonstrated privilege escape.

**O8 — Native JSON silently resolved nested duplicate keys; fixed here.** The
native `ApplicationConfig::from_json` previously accepted two `sandbox` keys in
opaque implementation settings and kept the last value. The concise project
parser rejected the same ambiguity. Both now use one recursive uniqueness
check, and the [API regression probe](tests/api_surface_probes.rs) passes. This
intentionally rejects ambiguous native documents that the old parser accepted.

**O9 — Rewrite policy belongs to the caller or runtime, not to `Kernel` alone.**
The direct kernel prepared a rule when the caller supplied its grammar. A default
`ProposalRuntime` rejected that same request as unregistered; a runtime created
with the grammar accepted preparation. Code using `Kernel` directly must control
who supplies the grammar. The runtime supplies a per-instance policy boundary.

**O10 — New content packages can reuse prior content without copying a whole
snapshot.** A workspace capture over a two-file base changed one file and
produced a `Changes` document naming the original base with exactly one path
replacement. The unchanged file retained its original package identity. The
new workflow output carried a small `PackageEnvelope`, and
`SessionHandle::submit_with_content` accepted it with the complete dependency
closure. The [retained probe](tests/content_composition_probe.rs) establishes
semantic reuse and successful workflow publication, not measured physical disk
savings or arbitrary byte-level delta compression. Retaining the changes
package also retains its historical base dependencies.

## Source-derived limits and held-out probes

Each row is a falsifiable hypothesis or an exposed design boundary; H2, H5,
H6, H9, and one part of H11 have executed probes, while the others remain
unexecuted here.
`P0` means correctness, safety, or irreversible work
fate; `P1` means public expressiveness or recovery; `P2` means performance and
capacity. Source locations are starting points for the test.

| ID | Priority | Claim to challenge and discriminating experiment | Oracle |
| --- | --- | --- | --- |
| H1 | P0 | Rewrite-order independence: remove the sole accepting edge, then add a replacement; reverse the order. | **Observed:** rewrites with disjoint footprints commute on graph, frontier, and retirements (`disjoint_rewrites_commute_on_the_frontier`); overlapping rewrites remain order dependent by design. |
| H2 | P0 | **Observed:** transfer on `e1` before deleting it versus delete first. | First trace retains an `In` receipt at the surviving receiver; second retires `Out` work and later transfer rejects. |
| H3 | P0 | Cross-root merge: fork from separate roots, then join at `All`; vary authority, edge identity, and arrival order. | Equal carried authority and one package per current incoming edge; no double consumption; DAG ancestry includes both roots. |
| H4 | P0 | Root bypass of approval: give an `All` node a root rule and no received approvals. | Legal root activation has zero inputs. Application policy must prevent treating `All` alone as approval authorization. |
| H5 | P0 | **Observed:** executable B sends a valid root for A through raw `ApplicationContext::submit`, then tries the node-bound invocation path. | Raw kernel-law admission accepted; node-bound invocation denied root authority for B. Document the distinct trust contracts. |
| H6 | P0 | **Partly observed:** a SQL failure after object-store tag sync leaves an orphan after garbage collection. Repeat with a process kill in the same window and repeated failures. | No activation/revision change; the orphan is retained under injected SQL failure. Measure bytes and decide how provisional tags are reconciled after crash. |
| H7 | P0 | Validator and evidence faults: reject, missing bytes, mismatched digest, panic, and repeated contract/digest in one activation or rewrite. | No partial kernel or durable commit; error class stable; successful proof reuse does not rely on validator invocation count. |
| H8 | P1 | Dynamic audit: activation → outbound → transfer → rewrite → restart, then request full verification. | Ordinary reopen preserves graph, frontier, history, content, and revision. `to_parts` and verified reopen reject dynamic history by current design. |
| H9 | P1 | **Observed:** supply a caller-made rewrite grammar to direct `Kernel::prepare_rewrite`, then attempt the same rule through default and configured runtimes. | Direct kernel accepts the supplied grammar; default runtime rejects the production; configured runtime accepts preparation. |
| H10 | P1 | New worker after rewrite: add a node and deliver it work in an application run. | Kernel/session can hold pending work; `RunningApplication::executions()` has no automatically launched worker for the new node. |
| H11 | P1 | **Partly observed:** future schema vocabulary, starting with an empty-edge application and authority-bearing root; then try a rewrite introducing a new type/tag. | Direct `Kernel::admit` reserves the tag; builder rejects the isolated root. The later rewrite remains untested. |
| H12 | P1 | Authoring parity: express multiple roots, custom edge types, grammar, and dynamic executable binding through direct Rust, native JSON, and concise project forms. | Produce a capability/rejection matrix; distinguish deliberate abstraction from silently dropped semantics. |
| H13 | P1 | Fixed-graph restoration mutation: alter every canonical record field in turn, including producer, consumed edge, authority, digest, and definition fingerprint. | Invalid records reject; valid topological reorder restores the same canonical state and causal DAG. |
| H14 | P1 | Receipt migration policy: replace an `All` node's edge after it receives work, then try every legal subsequent operation. | **Resolved:** the receipt is retired as `RouteRemoved` at the rewrite; see O2. |
| H15 | P2 | Local rewrite cost: hold graph/frontier constant; compare 100 and 10,000 consumed roots with distinct result bytes. | Same semantic result; measure result reads, lock wait, latency, and peak memory. Source suggests full-history materialization. |
| H16 | P2 | Width, depth, and session count: wide fan-out, deep static cycle, many tiny sessions, many concurrent readers/writers. | No overflow or state divergence; record throughput, p95 latency, peak RSS, thread/FD count, and failure threshold. |

Routine reopen (`ProposalRuntime::open_persistent`) checks the derived
readiness indexes at O(frontier) cost and trusts the rows otherwise; the
invariants I1–I7 of [docs/TRANSITIONS.md](docs/TRANSITIONS.md) are checked
through `Kernel::restore_checkpoint` whenever the session exports its exact
state (`snapshot`, `try_snapshot`, and the verified reopen), which the
adapter-equivalence test does after every step.

Two additional static seams should be checked during H12. The concise project
compiler lowers connection types to `Connection` in
[project.rs](crates/application/src/project.rs), while direct edge definitions allow other types.
The JSON application configuration has no grammar field, although
`Application::with_grammar` does. These are expressiveness questions with
straightforward before/after admission tests.

## Test machinery that would make these answers durable

1. **A small independent model.** Enumerate or generate bounded graphs with
   parallel edges, self-loops, cycles, forks, joins, `Any`/`All`, and two or
   three authority tags. Model `(G, F, H)` separately from the Rust kernel.
   Generate root, emit, transfer, consume, rewrite, and rejected operations;
   compare normalized states after every step. Normalize random activation IDs
   by producer and emission ordinal, not by lexical order.
2. **State-machine properties.** Check rejection atomicity, unique production,
   at-most-once consumption, causal acyclicity, digest integrity, authority
   derivation, cleanup partition, no identity reuse, and stale-plan rejection.
   Shrink every failing sequence to a short replayable trace. Metamorphic checks
   should permute independent activations and canonical input ordering.
3. **Layer parity fixtures.** Define one workflow in direct kernel terms, then
   attempt it through session, builder, JSON, and project APIs. Record whether
   each layer can construct the graph, submit operations, observe outcomes, and
   resume it. Use compile tests for missing methods and runtime tests for
   silently narrowed meanings.
4. **Durability and fault injection.** Place failpoints before/after object-store
   sync and SQLite commit for activation, transfer, rewrite, and context receipt.
   Reopen in a new process; compare a logical SQL dump, content tags, and all
   public state views. Distinguish an unknown commit outcome from rejection.
5. **Capacity with explicit targets.** Benchmark cost against live frontier,
   historical activation count, graph size, payload size, and session count as
   independent axes. Set acceptable latency and memory limits before declaring
   a capacity regression; a 50,000-package success alone does not establish a
   throughput or long-duration guarantee.

The direct calculus trusts contract purity and stable contract-ID meanings;
`DefinitionFingerprint` cannot inspect validator code. The runtime trusts its
owned dynamic ledger on routine reopen. Tests can establish behavior under
these assumptions and expose failures at their boundaries. They cannot prove
opaque external executables, caller authentication, or arbitrary future
workflows correct without additional contracts and evidence.

## Workspace split

The single crate is now a Cargo workspace: `ontography-calculus` holds the
graph law and the storage adapter contract, `ontography-content`,
`ontography-runtime`, `ontography-workspace`, and `ontography-application`
build on it in that order, and the root package `ontography-core` is a facade
that re-exports the same names as before, plus `ontography::storage`. The
split came with reductions that did change behavior and public API, each
listed in its round's report. The kernel's dynamics are one transition model
(`Transition`, `Transition::verify`, `State::apply`) shared by the in-memory
state and the `SQLite` adapter, whose parity the differential test pins, and
`restore_checkpoint` verifies I1–I7 plus the definition binding. The session
reports failure through one `SessionError` set and one fault ladder, treats
missing or corrupt payload evidence for a package it has a row for as a
`Storage` failure rather than a kernel rejection, applies the same fault rule
to the invocation store, and recognizes an accepted retry by a canonical
encoding of the submission's facts. The application narrows the content handle
it gives components, shares one DTO set and one duplicate-key mechanism
between its two authoring formats, closes a fresh run on every start failure,
and fails a drifted resume closed unless partial resume is requested;
`ContentStore::release` makes a rejected workspace capture's imports
collectable; and the workspace crate declares its Unix posture once at the
crate root. The calculus crate compiles alone against 20 third-party
packages, all in the transitive closure of `serde`, `sha2`, `thiserror`, and
`uuid`, so the law can be checked without building any storage or networking
code.
