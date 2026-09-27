# Ontography calculus in Lean

This directory states the Ontography calculus in Lean 4 and proves its invariants. The model
is the normative law: [MATHEMATICAL_DEFINITION.md](../MATHEMATICAL_DEFINITION.md) is its
readable companion and names the definitions below. The Rust kernel is checked against the
model by a differential test, described under [Checking the kernel](#checking-the-kernel).

Build and audit:

```sh
cd formal
lake build                   # the model, its proofs, and the executable examples
lake build Ontography.Audit  # fails unless every headline theorem uses only standard axioms
```

The toolchain is pinned in `lean-toolchain`, and the model uses Lean's core library only.

## Layout

| File | Contents |
| --- | --- |
| `Basic.lean` | Identifiers, payloads, authorities, and list-as-set equality. |
| `Definition.lean` | Schema, contracts, graph, annotations, policies, and `Definition.Admitted` (§1). |
| `State.lean` | Package records, activations, and states (§2). |
| `Step.lean` | The law under a fixed definition: `activate`, `transfer`, `retire`, and `step` (§3–§4). |
| `Invariants.lean` | `WF`, the invariants I1–I7 with causal acyclicity; `Frame`; `Reachable`. |
| `Rewrite.lean` | Productions, matches, `structural?`, the cleanup table `cleanup?`, `rewrite`, and `extend` (§5–§6). |
| `System.lean` | Running workflows: `sysStep` over definition and state, and `SysReachable`. |
| `Theorems.lean` | Theorems of the fixed-definition calculus. |
| `SystemTheorems.lean` | Theorems of rewriting, extension, and whole runs. |
| `Commutation.lean`, `Runs.lean`, `Checkpoint.lean`, `Replay.lean` | Definitions the metatheory needs. |
| `Metatheory.lean` | T4, T6 over runs, checkpoint restoration, and T5. |
| `Examples.lean` | Kernel rewrite tests replayed as build-time `#guard`s. |
| `Proofs/` | The proofs. Reviewing the calculus means reading the statement files above, not these. |
| `Audit.lean` | Fails the build if a headline theorem depends on `sorryAx` or any non-standard axiom. |

## Headline theorems

Each holds for every validator, commitment function, and rewrite grammar.

- `wf_initial`, `wf_step`, `wf_of_reachable`: every state reachable under an admitted
  definition satisfies `WF`.
- `wf_rewrite`, `wf_extend`, `wf_sysStep`, `wf_of_sysReachable`: rewrites and extensions keep
  the definition admitted and the state well formed.
- `rewrite_spec`, `extend_spec`: the rewrite and extension rules exactly, including the
  cleanup table and its successor-revision stamp.
- `step_revision`, `sysStep_revision`: each transition advances the revision once.
- `step_frame`, `sysStep_frame`, `sysStep_fresh`: transitions never change accepted
  activations, immutable package facts, deliveries once made, or settled statuses, and a new
  definition introduces only identities never used before.
- `causal_acyclic`: the causal history is acyclic.
- `sysStep_delivery`: each delivery is made over an edge of the definition in force when it
  is made, the timing that I3 states and a single state cannot record.
- `rewrite_local`, `rewrite_commute` (T4): a rewrite changes only packages at holders it
  affects; when both orders of two rewrites apply, they yield the same definition, and if
  their affected holders are disjoint across both application orders they commute on every
  package up to retirement stamps.
- `sysSteps_frame`, `activation_persists`, `accepted_not_reaccepted`, `sysStep_newborn`,
  `removed_node_never_returns`, `removed_edge_never_returns` (T6): no activation, package,
  node, or edge identity is ever reused.
- `checkpoint_exact`, with `checkpoint_of_wf` and `checkpoint_sound`: checkpoint
  restoration checks exactly the invariants — a checkpoint passes if and only if some
  well-formed state records it, up to the order of its identity lists.
- `replay_history`, `replay_causal`, `replay_sound`, `activationRun_of_revision` (T5):
  replay accepts only faithful histories and, in any causal order, reproduces a state
  reached by activations alone, which `revision = |A|` identifies.

## What is trusted

The theorems assume nothing about these, so they hold for every choice:

- **Validators.** The rules take `accepts : ContractId → Bytes → Bool`. A contract identity
  names one predicate for the model's lifetime, which the kernel's shared-validator check
  enforces.
- **The payload commitment.** The rules take `H : Bytes → Digest`. Where the kernel relies on
  SHA-256 being collision-free, the model says so: validation caching (Step.lean) and replay
  evidence (`replay_history`).
- **Fresh identities.** The kernel draws activation identities at random; the model takes them
  as inputs, and admission requires them to be fresh.

Outside the model:

- the Rust kernel's transitions, checked against the model by the differential test below;
- the kernel's restorations `restore_state` and `restore_checkpoint`, which the replay and
  checkpoint theorems describe through a correspondence established by review and pinned by
  the kernel's own tests, not by the differential test;
- the oracle's trace codec in `Oracle/`, which is ordinary unproved Lean;
- the SQLite adapter, checked against the in-memory kernel by
  `tests/adapter_equivalence.rs`;
- and Lean's kernel, which checks the proofs.

## Representation choices

The model differs from the kernel's data structures in ways that do not change the law:

- Lists stand for sets: the rules compare authorities and vocabularies as sets. Two
  structural checks compare lists exactly — a record's authority against its output's, and
  replay's reconstruction of `Carry` — which agrees with the kernel because its authorities
  are sorted, duplicate-free sets.
- The order of `activationIds` and `packageIds` is the model's; the kernel's maps record
  none, which is why the checkpoint and replay results hold up to permutation.
- A package trigger's inputs are a duplicate-free list; a kernel proposal is a set.
- Output `i` of activation `a` is package `(a, i)`, as live evaluation numbers them. The
  kernel's restorations accept any distinct numbering, so the model describes them up to
  renumbering.
- Revisions are unbounded naturals, so the kernel's `u64` headroom check has no counterpart.
- Rejection is `none`: which premise failed is not part of the law.
- The fingerprint, binding, and nonce are implementation fences and are not modeled.
- `edgeLog` keeps every admitted edge with its incidence and `changeLog` the revision of each
  definition change. The kernel stores only their identities and length; the richer records
  make I3 and the stamp rules properties of one state.

## Stronger invariants not yet stated

`WF` is not the strongest decidable invariant of reachable states. Because a surviving
identity keeps its annotations and policies and a delivery never changes, reachable states
also satisfy these, which neither `WF` nor checkpoint restoration checks yet:

- a `RouteRemoved` receipt's delivery edge is no longer a current incoming edge of its holder;
- a root activation at a current node is permitted by that node's current root rule;
- the inputs of an activation have distinct delivery edges;
- an output born over a current edge satisfies that edge's authority condition, and one whose
  authority differs from its activation's governing authority has a current transition rule.

Each is preserved by every transition. Adding them to `WF`, `CheckpointValid`, and the
kernel's `restore_checkpoint` would make restoration reject the corresponding tampered
checkpoints, which it accepts today.

## Checking the kernel

`tests/lean_oracle.rs` drives the Rust kernel with random activations, transfers,
retirements, rewrites, and extensions over a fixed grammar menu, and writes each run as a
JSON trace ([TRACE_FORMAT.md](TRACE_FORMAT.md)). The `oracle` executable built from this
directory replays the trace through the model's `sysStep`, and the test fails on any
disagreement in acceptance or in the resulting state, which includes the current definition.
A required prefix pins the rule cases and the kernel scenarios of `Examples.lean`; stale
prepared plans have no model counterpart and are checked against the kernel alone. Build the
oracle with `lake build oracle`; `ONTOGRAPHY_LEAN_ORACLE_SEEDS` adds seeds.
