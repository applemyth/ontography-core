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
- `rewrite_local`, `rewrite_commute` (T4): a rewrite changes only packages at holders it
  affects, and rewrites with disjoint affected holders commute up to retirement stamps.
- `activation_persists`, `removed_node_never_returns`, `removed_edge_never_returns` (T6).
- `checkpoint_of_wf`, `checkpoint_gap`: checkpoint restoration accepts every well-formed
  state, and its checks are strictly weaker than `WF`.
- `replay_history` (T5): fixed-graph replay reproduces a state reached by activations alone.

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

Outside the model: the SQLite adapter, checked against the in-memory kernel by
`tests/adapter_equivalence.rs`; the Rust kernel, checked against the model by the
differential test; and Lean's kernel, which checks the proofs.

## Representation choices

The model differs from the kernel's data structures in ways that do not change the law:

- Lists stand for sets, and authorities and vocabularies are compared as sets.
- A package trigger's inputs are a duplicate-free list; a kernel proposal is a set.
- Output `i` of activation `a` is package `(a, i)`, as live evaluation numbers them.
- Revisions are unbounded naturals, so the kernel's `u64` headroom check has no counterpart.
- Rejection is `none`: which premise failed is not part of the law.
- The fingerprint, binding, and nonce are implementation fences and are not modeled.
- `edgeLog` keeps every admitted edge with its incidence and `changeLog` the revision of each
  definition change. The kernel stores only their identities and length; the richer records
  make I3 and the stamp rules properties of one state.

## Checking the kernel

`tests/lean_oracle.rs` drives the Rust kernel with random operations and writes each run as
a JSON trace ([TRACE_FORMAT.md](TRACE_FORMAT.md)). The `oracle` executable built from this
directory replays the trace through the model, and the test fails on any disagreement in
acceptance or in the resulting state. Build the oracle with `lake build oracle`.
