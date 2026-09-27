# Kernel state, transitions, and storage adapters

This document is the normative specification for the dynamic state model of
the kernel: the package record, the state, the transition relation, the views a
storage adapter must supply, and the theorems that tests pin. The separate
[mathematical definition](../MATHEMATICAL_DEFINITION.md) specifies graph
admission and the activation, transfer, retirement, rewriting, and vocabulary
extension rules for this checkout.

Here `A` and `P` denote the identity sets of the mathematical definition's
activation and package maps, `Δ` the admitted definition with graph `G = (V, E)`,
and `H` the activation history. `producer(p)` and `O_a` are the producing
activation and its output map, as defined there.

## 1. Package record

Every package `p ∈ P` has exactly one record:

```
PackageRecord = (
  object_type,           immutable, from the accepting contract or the birth type
  authority,             immutable carried authority cap(p)
  digest,                immutable content commitment
  producer_node,         immutable, node(producer(p))
  delivery,              Option<(edge, receiver)>, set at most once
  status,                Live | Consumed(a) | Retired(r)
)
```

with `r = (reason, revision, evidence)` and `reason ∈ {HolderRemoved,
NoAcceptingEdge, RouteRemoved, Explicit}`. The birth edge is not a record
field: the producing activation's output record already states it, and
`apply` rejects an activation whose output names an edge that disagrees with
the record's delivery. The delivery's source is not stored either; it is the
record's `producer_node` by construction.

Derived, never stored twice:

```
holder(p) = delivery.receiver     if delivery is Some
          = producer_node         otherwise
phase(p)  = In                    if delivery is Some
          = Out                   otherwise
F         = { p ∈ P : status(p) = Live }          the live frontier
```

The three statuses are a sum type. A package is exactly one of live,
consumed, or retired by construction, not by convention.

### Invariants

Every reachable state satisfies:

- **I1 Ownership.** `producer(p) ∈ A` and `p ∈ dom(O_producer(p))`.
- **I2 Consumption.** `status(p) = Consumed(a)` implies `p ∈ inputs(a)`,
  `delivery(p)` is `Some`, and `a ∈ A`. All inputs of `a` carry one authority
  and have the holder recorded as `a.node_id`. A root's recorded node equals
  its trigger node.
- **I3 Delivery.** `delivery(p) = Some(e, v)` implies `e` was an admitted edge
  with `s(e) = producer_node(p)` and `t(e) = v` at the revision of delivery.
  If the producing activation's output for `p` names an edge `e`, then
  `delivery(p) = Some(e, _)`. The first clause refers to a past graph, which a
  state does not record; for an edge still in the graph it reduces to that
  edge's current incidence.
- **I4 Retirement.** `status(p) = Retired(r)` implies: `reason = NoAcceptingEdge`
  only if `phase(p) = Out`; `reason = RouteRemoved` only if `phase(p) = In`;
  `evidence` is `Some` only if `reason = Explicit`; `evidence = Some(a)` implies
  `a ∈ A`; `1 ≤ r.revision ≤ revision(S)`. `HolderRemoved` implies the holder
  is absent from the current graph. Explicit retirements have distinct stamps,
  disjoint from structural retirement stamps.
- **I5 Custody.** `status(p) = Live` implies `holder(p) ∈ V` in the current
  graph. A live `In` receipt at an `All` holder names a current incoming edge.
- **I6 Revision.** `revision(S) = |A| + |{p : delivery(p) is Some and the
  producer's output for p names no edge}| + |{p : reason(p) = Explicit}| +
  definition_changes`. Every transition advances the revision by exactly one,
  and each kind accounts for
  exactly one term: an activation, a transfer, an explicit retirement, or a
  definition change. `definition_changes` counts all rewrites and extensions,
  including identity rewrites. The number of distinct structural retirement
  stamps cannot exceed this count.
- **I7 Identity.** `used_node_ids ⊇ V` and `used_edge_ids ⊇ E`, and no fresh
  identity ever re-enters either set.

## 2. State

```
State = (
  definition_id, definition_fingerprint,
  activations: A → Activation,
  packages:    P → PackageRecord,
  live:        BTreeSet<PackageId>,       derived index of F, maintained by apply
  used_node_ids, used_edge_ids,
  definition_changes: u64,
  revision: u64,
  nonce: u128,                            fresh on every apply
)
```

The nonce is the exact-state fence for the direct API, where `State` is
cloneable and two clones can share a revision. It is assigned from the same
randomness source as activation identities and changes on every applied
transition. It is a fence, not a fact: `State` equality ignores it, so two
states with equal facts compare equal. Storage adapters that own their state
exclusively fence on revision alone and report a constant nonce.

`positions`, `deliveries`, and `retirements` are not stored. They are derived
on demand from the records; only `live` is a stored index, and restoration
rebuilds it.

Every activation records `(node_id, trigger, result, outputs)`, including an
outputless package-triggered activation. The execution node is part of the
accepted fact, checked against input custody during apply and restoration.

## 3. Transitions

A transition is a base binding plus exactly one kind:

```
Transition = (base: (definition_id, definition_fingerprint, revision, nonce), kind)

TransitionKind =
  | Activation { id, activation, outputs: [(p, PackageRecord)],
                 inputs: {p → PackageRecord} }
        inserts the activation and its outputs live; consumes the inputs
        named by the activation's trigger
  | Transfer   { package, delivery, source: PackageRecord }
        Live, delivery None → delivery Some
  | Retire     { package, retirement }          Live → Retired, reason Explicit
  | Rewrite    { retirements: [(p, Retirement)], fresh_node_ids, fresh_edge_ids,
                 next_nodes, next_all_routes, next_fingerprint }
        Live → Retired for each, structural reasons only; admits the fresh
        identities; installs the replacement definition
  | Extension  { next_fingerprint }             installs the extended definition
```

What a transition may contain is a fact of the type: one activation, one
transfer, one explicit retirement, or one graph replacement per transition.
Multiplicity is therefore not something an evaluator can get wrong.

`verify(τ, kernel, view)` checks, mutating nothing:

1. `τ.base` names the applying kernel's definition and version, and equals
   the view's binding.
2. The kind's preconditions, including I1 through I7 restricted to what the
   transition touches and the record witnesses used for admission:
   - *Activation*: the identity is fresh; the consumed inputs are all live,
     delivered, carry equal authority, and are held at the recorded executing
     node (I2); each input exactly matches its evaluated record witness; each
     output record is owned by the activation, live, and agrees with the
     output on type, authority, digest, producer node, and birth edge; a birth
     delivery names an admitted edge from the executing node to its receiver
     (I1, I3).
   - *Transfer*: the package is live, undelivered, and exactly matches the
     source record whose admission was proved; the delivery names an
     admitted edge from the record's producer node to the receiver (I3).
   - *Retire*: the package is live; the retirement admits the package's
     phase; if present, its evidence is an accepted activation (I4).
   - *Rewrite*: every fresh identity is non-empty and unused (I7); every
     retired package is live and its retirement admits its phase (I4);
     `HolderRemoved` names a holder absent from `next_nodes`; every
     package still live afterwards is held by a node of the replacement graph
     and every surviving `All` receipt keeps a current incoming route (I5).
   - *Extension*: nothing beyond the binding.

Every evaluator checks the view's binding against its kernel and the revision's
headroom before constructing a transition, so its base never names
another definition or an exhausted revision. Facts an evaluator establishes by
construction of the sealed transition, namely one record per output, one
retirement per package, the successor revision on every retirement stamp, the
reason each kind admits, the replacement graph's node set, and the executing
node's presence in the graph, are asserted in debug builds and are not part of
`ApplyError`.

`apply(S, kernel, τ)` runs `verify` against `S` itself, then mutates: performs
the kind, sets `definition_fingerprint` and increments `definition_changes`
for a rewrite or extension, sets `revision := revision + 1`, and refreshes the
nonce.

`verify` does not rerun payload validators. Whether a transition is *lawful*, that is
whether an evaluator would have produced it from the true state, is decided by
the evaluators. Whether its result is *well-formed* is decided by `verify`,
for any view, faithful or not. Every rule of the calculus lives in the
evaluators. Activation evaluation snapshots each input once; its admission
proof and sealed transition use those same records. Verification binds that
proof to the records actually being mutated, covering ingress, result-contract,
and authority decisions even for outputless activations. Evaluators are pure
functions from a view and a request to a transition:

| Evaluator | Reads | Produces |
| --- | --- | --- |
| `evaluate_activation(view, id, proposal)` | records of the proposal's inputs; graph | `Activation` |
| `evaluate_transfer(view, p, edge, payload_for)` | record of `p`; graph and schema; bytes on demand | `Transfer` |
| `evaluate_retire(view, p, evidence)` | record of `p`; graph; whether evidence ∈ A | `Retire` |
| `evaluate_rewrite(frontier, grammar, request, payload_for)` | every live record; used ids; graph; bytes on demand | `Rewrite`, plus the next kernel |
| `evaluate_extension_transition(view, next)` | binding | `Extension` |

The public single-shot operations, `Kernel::activate` and `Kernel::retire`,
are `evaluate` followed by `apply` on the in-memory state. Rewrite, transfer,
and extension keep a prepare/commit pair so the caller can review the
transition before committing; the prepared value holds the transition, plus
the next kernel for a rewrite or extension and the delivery for a transfer,
never a copy of the state.

Every direct commit checks the prepared base against the current state before
checking admission, so intervening rewrites and extensions report `Stale`.
Rewrite and extension commits also require the existing contract validators to
be shared with the prepared next kernel; a structural fingerprint cannot
identify executable validator code.

## 4. Views

A storage adapter supplies read views and one applier. These are the whole
contract between the kernel and its storage; no adapter constructs kernel
records except through `apply`.

```
trait PackageView {
  fn record(&self, p) -> Option<PackageRecord>;
  fn activation_known(&self, a) -> bool;
  fn binding(&self) -> Binding;          // definition id, fingerprint, revision, nonce
}

trait FrontierView: PackageView {
  fn live(&self) -> Vec<(PackageId, PackageRecord)>;
  fn used_node_ids(&self) -> BTreeSet<Arc<str>>;
  fn used_edge_ids(&self) -> BTreeSet<Arc<str>>;
}
```

The in-memory `State` implements both views and `apply`. The SQLite adapter
implements both views over rows, runs the same `verify` over the rows of the
applying transaction, and then writes the kind's facts with a changed-row
guard per write. The two appliers therefore reject exactly the same
transitions. `ApplyError` distinguishes stale bindings, record-witness
mismatches, authority or execution-node mismatches, invalid custody and
retirements, obsolete `All` routes, and defensive checks on evaluator outputs.

Views are trusted for liveness, not for integrity. A forged view can make an
evaluator produce a lawful-looking transition that differs from what the true
state would have produced, for example one that omits a `NoAcceptingEdge`
retirement. It cannot bypass input admission by changing the records used for
the proof, leave a live package at a removed holder or obsolete `All` route,
or stamp `HolderRemoved` on a surviving holder. `verify` runs against the
state being mutated; it enforces structural integrity without replaying
payload-dependent cleanup. Adapters must use the same trusted validator
registry for evaluation and verification.

Rewrite preparation reads the frontier, graph and rule structure, and lifetime
identity sets. The frontier scan costs `O(|F|)`, but constructing and re-admitting
the replacement definition also traverses the full graph. Outgoing edges are
indexed once; each rechecked package tests only its holder's candidate edges
and fetches its payload at most once. Hashing and validator costs depend on
payload sizes and the candidates attempted. There is no `O(|F|)` bound on the
whole operation; activation history and result payloads are not read. An
adapter fencing on revision alone reports a constant nonce and
the kernel accepts it as such only through the adapter's own applier.

Checkpoint restoration takes `(definition_id, definition_fingerprint, A, P,
used_node_ids, used_edge_ids, definition_changes, revision)`, requires the
definition binding to name the restoring kernel, and verifies I1 through I7 and
causal acyclicity, plus consequences of admission and cleanup that a trusted store cannot
legitimately violate: some node identity is allocated whenever an edge
identity is, the inputs of a join carry one authority, every root
authority, object type, and carried authority is in the schema, every
delivery on a current edge matches that edge's incidence, a holder-removed
retirement never names a current node, and a live receipt at an `All`
receiver always names a current incoming edge. Its error names the invariant
family that failed. It does not rerun contracts or cleanup; it is a
trusted-store integrity check, not a proof of reachability. I3 is verified
only as far as a state records it: a delivery on a removed edge must name a
used edge identity and a used receiver and agree with every other delivery
over that edge on its endpoints, but its incidence at the revision of delivery
is not recorded and is trusted. With these checks restoration checks exactly
I1–I7: `checkpoint_exact` proves that a checkpoint passes if and only if some
well-formed state records it, up to the order of its identity lists. I1–I7 are
not the strongest decidable invariants; the model's README lists consequences
of admission that reachable states also satisfy and restoration does not yet
check. Fixed-graph
restoration (`restore_state`) replays every rule from the activation records
alone. Export through `to_parts` is available only when there have been no
definition changes, transfers, or retirements; exact revision accounting then
gives `revision = |A|`. Checkpoint counters describe recorded operations; they
do not independently authenticate an omitted or altered history.

## 5. Theorems

T1–T3 are properties of this implementation and are pinned by tests. T4–T6 are
properties of the calculus: the Lean model in [formal/](../formal/README.md)
proves them for every validator and grammar. A differential test checks the
kernel's transitions of every kind against the model; the replay and checkpoint
results describe `restore_state` and `restore_checkpoint` through a reviewed
correspondence pinned by the kernel's own tests. The model proves the
invariants I1–I7 themselves as `wf_of_sysReachable`, with I3's timing, that a
delivery is made over an edge of the definition in force, as
`sysStep_delivery`.

- **T1 Partition and shape.** The status partition and the one-kind-per-
  transition shape hold by type. Tests pin that every evaluator's output
  verifies against the state it was evaluated over.
- **T2 Atomicity.** `evaluate` is pure; `apply` mutates only after every
  precondition is checked, so a rejected transition leaves `S` unchanged.
- **T3 Adapter equivalence.** For any state `S`, any transition `τ` produced by
  an evaluator over a view of `S`, and rows `R(S)` in the SQLite adapter:
  `R(apply_mem(S, τ)) = apply_sql(R(S), τ)`, and both reject the same `τ`.
  Pinned by a differential test over random operation sequences, including
  stale plans, node creation and deletion with fresh identities, and rejected
  rewrites and extensions, that compares the adapter snapshot, every rejection,
  and the readiness projection of every receiver and edge with the in-memory
  state after every step.
- **T4 Locality.** Rewrites commute on graph, live frontier, and retirement
  records projected without revision stamps when both conditions hold:
  (1) their graph edits are independent, both residual matches remain valid,
  fresh allocations are distinct, and both orders yield the same admitted
  definition; (2) their affected-holder sets are disjoint. For a rewrite
  `G → G'`, this set is the deleted node IDs, surviving sources whose outgoing
  edge identity sets change, and surviving `All` receivers whose incoming edge
  identity sets change. Admitted rewrites preserve the annotations and incidence
  of retained edge identities. Compute each rewrite's affected-holder set as
  the union for its initial and residual applications, then require those two
  unions to be disjoint.
  Payload evidence is immutable and validators are pure in both orders.
  Graph independence alone does not suffice: adding two distinct edges from
  the same holder can retire an `Out` package in only one order. The regression
  pairs two real rewrites and also pins this overlapping-holder counterexample.
  Proven as `rewrite_commute`, with `rewrite_local` for locality. The model
  also proves that whenever both orders apply they yield the same definition,
  so that part of condition (1) is a consequence rather than a hypothesis.
  The model's `Examples.lean` replays both pairs.
- **T5 Restoration.** Fixed-graph replay of `to_parts(S)` reproduces `S`
  whenever `revision(S) = |A|`, and checkpoint restoration of any reachable
  state reproduces it exactly. The model proves replay: `replay_history` and
  `replay_causal` (in any causal order, as `consumption_order` replays),
  `replay_sound` (replay accepts only faithful histories), and
  `activationRun_of_revision` (`revision = |A|` means only activations
  happened). It proves that restoration checks exactly I1–I7:
  `checkpoint_of_wf` and `checkpoint_sound`. That the restored state equals
  the checkpointed one is pinned by tests.
- **T6 Freshness.** No node, edge, activation, or package identity is ever
  reused within one state's lifetime. Proven as `sysStep_fresh`,
  `sysSteps_frame`, `sysStep_newborn`, `accepted_not_reaccepted`,
  `removed_node_never_returns`, and `removed_edge_never_returns`.

## 6. Persisted definition encoding

The current definition is persisted through explicit, versioned data-transfer
types owned by the storage module. Graph and annotation types carry no derived
`Serialize`; the encoding is a documented format with a version field, and
decoding passes through the checked constructors. Renaming a private field can
never change the on-disk format.
