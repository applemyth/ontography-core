# Ontography calculus

This document specifies the workflow calculus implemented in this checkout.
Its basic objects are nodes, edges, and package occurrences. Activations record
their interaction; transitions change the graph or its occurrence state. The
[README](README.md) explains the concepts and the surrounding execution APIs.
The [transition specification](docs/TRANSITIONS.md) gives the concrete storage
records, verifier obligations, and adapter interface.

The normative statement of the calculus is the Lean model in
[formal/](formal/README.md). This document is its readable companion: each
section names the definitions and theorems that state it. The model's theorems
are machine-checked, and the Rust kernel is checked against the model by a
differential test over random operation sequences.

## 1. Admitted definition

Let the schema be `Σ = (N, O, U)`, where `N` is the vocabulary of node types,
`O` the vocabulary of object types, and `U` the vocabulary of authority tags.
An authority is any subset `α ⊆ U`, including the empty set.

A contract registry `C` maps each contract identity `c` to:

```
C(c) = (object_type(c), accepts_c)
object_type(c) ∈ O
accepts_c : Bytes → {accept, reject}
```

Validators are trusted, pure, deterministic predicates with stable meanings.
The mathematical relation assumes they terminate normally. A validator panic
is an operational failure handled by the API layer that invokes it.

The topology is a finite directed multigraph `G = (V, E, s, t)` with unique node
and edge identities and `s, t : E → V`. Empty graphs, self-loops, parallel edges,
and cycles are permitted. Identifiers must be nonempty.

Every node `v ∈ V` has exactly one definition:

```
node(v) = (types_v, result_contract_v, ingress_v)
∅ ≠ types_v ⊆ N
result_contract_v ∈ dom(C)
ingress_v ∈ {Any, All}
```

Every edge `e ∈ E` has exactly one definition:

```
edge(e) = (types_e, source_requirements_e, target_requirements_e,
           package_contract_e, tags_e, match_e)
source_requirements_e ⊆ types_s(e)
target_requirements_e ⊆ types_t(e)
package_contract_e ∈ dom(C)
∅ ≠ tags_e ⊆ U
match_e ∈ {AnyOf, AllOf}
```

Edge types form a nonempty set of nonempty semantic labels; they are outside
the schema's closed vocabularies. Endpoint requirements may be empty.

Root policy is a partial map `ρ : V ⇀ P(U)`, where `P(U)` is the set of subsets
of `U`. A node outside `dom(ρ)` cannot originate a root activation. Authority
transition policy is a relation `T ⊆ V × P(U) × P(U)`.

Together, the graph, annotations, schema, contracts, and policies form an
admitted definition `Δ`. Its definition identity names the workflow; its
fingerprint commits to the canonical static structure. The fingerprint does
not identify executable validator code. A rewrite policy is a separate trusted
predicate supplied to the kernel or configured on the runtime (§5).

Implementation: [graph declarations](crates/calculus/src/graph.rs) and
[definition admission](crates/calculus/src/kernel/definition.rs). Model:
`Definition` and `Definition.Admitted` in
[Definition.lean](formal/Ontography/Definition.lean).

## 2. Packages, activations, and state

A package occurrence has identity `p = (a, i)`, where `a = producer(p)` is its
unique producing activation and `i` distinguishes that activation's outputs.
Live evaluation numbers an activation's outputs `0, 1, …` in the order they were
requested. Its record is:

```
P(p) = (type_p, authority_p, digest_p, producer_node_p, delivery_p, status_p)
delivery_p = None | (edge, receiver)
status_p = Live | Consumed(activation) | Retired(reason, revision, evidence)
```

Type, authority, digest, and producer node are immutable. Delivery is assigned
at most once, either at birth or by a later transfer. The payload commitment
`digest_p = H(bytes_p)` is computed from exact bytes using the kernel's
domain-separated SHA-256 scheme. Equal payloads do not identify equal package
occurrences. Bytes are supplied to admission and retained separately from the
package record by storage owners.

An accepted activation is:

```
A(a) = (node_a, trigger_a, result_a, O_a)
trigger_a = Orig(v, α) | Pkgs(I)
```

Here `O_a` maps the activation's output package identities to their birth
metadata, including an optional birth delivery edge. `result_a` is separate
from its output payloads. A package trigger has a nonempty set of input package
identities `I`; a root trigger has no package inputs.

State `S` contains the current definition binding, accepted activation map `A`,
package map `P`, lifetime node and edge identity sets, definition-change count
`d`, and revision `r`. The in-memory API also carries a nonce to distinguish
divergent states with equal revisions.

The frontier, holder, and phase are derived:

```
F(S) = {p ∈ dom(P) | status_p = Live}
holder(p) = producer_node_p          if delivery_p = None
          = receiver                if delivery_p = (edge, receiver)
phase(p) = Out                      if delivery_p = None
         = In                       otherwise
```

The causal history `H_S` has arcs `a → p` for each `p ∈ dom(O_a)` and `p → b`
when `status_p = Consumed(b)`. It is acyclic even when the workflow topology
contains cycles: each new accepted activation consumes existing packages and
creates fresh output occurrences.

Model: `PackageRecord`, `Activation`, and `State` in
[State.lean](formal/Ontography/State.lean). A model state also records each
admitted edge's incidence and the revision of each definition change, so that
I3 and the retirement-stamp rules below are properties of a single state.

## 3. Activation admission

Write `Δ; S ⊢ proposal ⇓ τ` when evaluation accepts a proposal and constructs
a transition. Here `S` is a well-formed state bound to `Δ`. Evaluation reads the
state and does not mutate it. Every accepted transition is bound to the evaluated
definition identity, fingerprint, revision, and nonce; the revision must have
room for one increment.

A proposal is a trigger, result bytes, and a list of requested outputs. Each
output names a destination, either a delivery edge or an object type for an
outbound birth, an authority operation, and payload bytes. The inputs of a
package trigger form a set.

### Trigger and result

For `Orig(v, α)`, admission requires:

```
v ∈ dom(ρ)
α ⊆ ρ(v)
```

The governing authority is `α`. Root admission is independent of the node's
package ingress mode and may occur repeatedly.

For `Pkgs(I)`, admission requires `I ≠ ∅`, all inputs live and delivered, one
common receiver `v`, and one common authority `α`. Delivery edge identities
must be distinct across the inputs. Let:

```
edges(I) = {e | ∃p ∈ I, delivery_p = (e, v)}
incoming_Δ(v) = {e ∈ E | t(e) = v}
```

Then:

```
ingress_v = Any  ⇒ |I| = 1
ingress_v = All  ⇒ edges(I) = incoming_Δ(v)
```

Thus an `All` node with no incoming edges has no package trigger; it may still
have root permission. There is no additional same-root or business-request
correlation premise. An `Any` receiver can consume a retained receipt whose
delivery edge has since been removed. An `All` receiver uses its current
incoming edge set.

For either trigger, the result must satisfy
`accepts_result_contract_v(result) = accept`.

### Output authority and destination

An activation may request any finite number of outputs, including zero. Each
output obtains authority independently:

```
Carry           ⇒ β = α
Transition(β)   ⇒ (v, α, β) ∈ T
```

An explicit transition requires the exact rule even if `β = α`. A rule may
reduce, preserve, or amplify authority. All output authority remains within
the schema vocabulary.

Define the edge authority condition:

```
allows(e, β) = tags_e ∩ β ≠ ∅       if match_e = AnyOf
            = tags_e ⊆ β           if match_e = AllOf
```

A delivered output `(e, β, bytes)` requires:

```
e ∈ E ∧ s(e) = v
allows(e, β)
accepts_package_contract_e(bytes) = accept
```

It receives the edge contract's object type and delivery `(e, t(e))`. An
outbound output `(o, β, bytes)` requires only `o ∈ O` in addition to the output
authority rules; it has no delivery and no edge-specific payload contract yet.
Both forms commit to their supplied bytes. Multiple outputs may use the same
edge, and one activation may mix delivered and outbound births.

### Effect

After verification against the state being mutated, acceptance records the
activation under its fresh identity, records its result and outputs, marks each
input `Consumed(a)`, and inserts every fresh output as `Live`. These changes
occur together. Rejection changes none of the accepted state. Preparation and
observation alone do not reserve inputs. Which premise failed is not part of the
calculus: the kernel's rejection variants are diagnostics.

Model: `activate`, with `rootTrigger?`, `packageTrigger?`, and `emission?`, in
[Step.lean](formal/Ontography/Step.lean). Implementation and coverage: [admission](crates/calculus/src/kernel/admission.rs),
[calculus tests](tests/calculus.rs), and [rule coverage](tests/rule_coverage.rs).

## 4. Transfer and retirement

Transfer of package `p` over edge `e` requires:

```
p ∈ F(S) ∧ delivery_p = None
e ∈ E ∧ s(e) = producer_node_p
type_p = object_type(package_contract_e)
allows(e, authority_p)
H(bytes) = digest_p
accepts_package_contract_e(bytes) = accept
```

Its effect is to set `delivery_p = (e, t(e))`. The package keeps its identity,
immutable fields, and live status. Transfer neither creates a new activation
nor changes carried authority.

Explicit retirement requires a live package. Optional evidence must name an
accepted activation in the same state. Its effect is
`status_p = Retired(Explicit, r + 1, evidence)`; it preserves the package and
its history. Evidence existence is checked, but no additional causal relation
between the evidence and retired package is required.

Model: `transfer` and `retire` in [Step.lean](formal/Ontography/Step.lean).

## 5. Graph rewriting

A rewrite applies an explicit edit `ε = (V⁻, E⁻, F)` on behalf of a principal
`π`. `V⁻` and `E⁻` are the node and edge identities it removes. `F` is an
annotated fragment, with nodes, edges, node definitions, edge annotations,
transition rules, and root rules, that names the identities the edit allocates.
An added edge may end at a surviving node as well as an added one. The edit
applies when:

- `V⁻` and `E⁻` are distinct current identities, and every edge of `Δ`
  incident to a node of `V⁻` is in `E⁻`: a rewrite never leaves an edge
  dangling.
- Every node and edge identity of `F` is fresh: it never appeared in the
  state's lifetime identity sets. An identity that leaves the definition,
  including one this edit removes, is never allocated again.
- `F` defines only what it adds: every node definition, transition rule, and
  root rule in `F` belongs to a node of `F`, and every edge annotation to an
  edge of `F`. A surviving node or edge keeps its definition and policies;
  changing one means replacing it under a fresh identity.
- The replacement `Δ'` is admitted. It is `Δ` without the nodes of `V⁻`, with
  their definitions, transition rules, and root rules, and without the edges of
  `E⁻`, with their annotations, plus `F`.

Admission of `Δ'` also makes the allocated identities distinct and nonempty
and places every added edge between nodes of `Δ'`. An edit may introduce root
rules and authority transitions on new nodes. The empty edit is an identity
rewrite.

Existing consumed or retired records remain historical facts. Live packages are
cleaned up under `Δ'` by these rules:

| Condition | Effect |
| --- | --- |
| Holder is deleted | Retire as `HolderRemoved`. |
| `Out`, holder survives with unchanged outgoing edge identities | Keep. |
| `Out`, outgoing edge identities change | Keep iff some outgoing edge accepts its type, authority, and committed bytes; otherwise retire as `NoAcceptingEdge`. |
| `In`, surviving holder has `Any` ingress | Keep. |
| `In`, surviving holder has `All` ingress | Keep iff the delivery edge remains incoming; otherwise retire as `RouteRemoved`. |

All structural retirements use the rewrite's successor revision and have no
explicit evidence. A missing or mismatched required payload, or a failing
evaluation, aborts the whole preparation. Contract rejection makes a candidate
route unacceptable; a validator panic aborts evaluation.

Finally the rewrite policy decides. The rewrite takes effect only if
`permits(π, Δ, ε, Δ', R)` holds, where `R` is the set of retirements the
cleanup makes. The policy is a trusted predicate supplied to the kernel or
configured on the runtime, like the validators, and every theorem holds for
every policy. It can refuse an admissible edit but cannot make an inadmissible
one admissible. Graph replacement, identity allocation, and cleanup commit
together; a refusal, like any other rejection, leaves the state unchanged.

The rewrite does not deliver packages or launch executables. Adding a rejecting
route can retire previously waiting work, so adding edges does not generally
preserve the frontier. Sufficient conditions for commutation, ignoring retirement
revision stamps, are independent graph changes and disjoint affected-holder
sets across both application orders; the precise conditions are in the
[transition specification](docs/TRANSITIONS.md).

Implementation: [rewriting](crates/calculus/src/kernel/rewrite.rs) and
[cleanup](crates/calculus/src/kernel/frontier.rs). Model: `structuralEdit?`,
`cleanup?`, and `rewrite` in [Rewrite.lean](formal/Ontography/Rewrite.lean).
`rewrite_spec` states the rule exactly, `wf_rewrite` that it preserves every
invariant, `rewrite_local` that it changes only packages at affected holders,
and `rewrite_commute` the commutation condition (T4).

## 6. Vocabulary extension

An extension replaces `Δ` with `Δ'` under the same definition identity, with
componentwise schema inclusion `Σ ⊆ Σ'` and contract-registry inclusion
`C ⊆ C'`. At least one vocabulary item or contract must be added. The graph,
node and edge annotations, root rules, authority transitions, and existing
contracts remain unchanged.

The implementation additionally requires each existing contract to share its
validator with the replacement registry. Equal names or structural fingerprints
alone do not establish equal executable predicates. Extension changes the
definition binding and revision, leaving packages and activations untouched.

Model: `extend` in [Rewrite.lean](formal/Ontography/Rewrite.lean), stated
exactly by `extend_spec`.

## 7. Transition application and invariants

The five transition kinds are activation, transfer, explicit retirement,
rewrite, and extension. Each successful application advances `r` exactly once;
rewrites and extensions also increment `d`. The in-memory applier refreshes its
nonce. Prepared transitions cannot be applied to a different predecessor.

For reachable states, revision accounting is:

```
r = |A| + explicit_transfers(P) + explicit_retirements(P) + d
```

An explicit transfer is recognized by a package with a delivery whose producing
output had no birth edge. An explicit retirement has reason `Explicit`.
Structural cleanup contributes through its rewrite, even if many packages
retire together. Identity rewrites still increment `r` and `d`.

Every reachable state satisfies the invariants I1–I7 of the
[transition specification](docs/TRANSITIONS.md), together with causal
acyclicity:

- I1: every package belongs to exactly one producer's output map and carries
  its birth metadata.
- I2: every package is exactly one of live, consumed, or retired. Only live,
  delivered packages can be consumed, at most once, and consumed inputs share
  their activation's recorded node and governing authority.
- I3: every delivery names an edge from the producer's node to the receiver
  that was admitted in the state's lifetime, and each delivery is made over an
  edge of the definition in force when it is made.
- I4: a retirement's reason admits the package's phase, only an explicit
  retirement carries evidence, and every stamp is a past revision: distinct for
  explicit retirements, a definition change for structural ones. A removed
  holder is absent from the current graph.
- I5: every live holder exists in the current graph. A live receipt at an `All`
  node names a current incoming edge.
- I6: revision accounting is exact.
- I7: lifetime identities include the current graph's and are never reused.
- The producer-to-consumer history is acyclic.

These are properties of one state. Two other kinds of property constrain how
states change. Each transition keeps every accepted activation, every package's
immutable facts, a delivery once made, and a status once no longer live. Across
a run, an identity that leaves the graph never returns.

Model: `WF` and `Frame` in [Invariants.lean](formal/Ontography/Invariants.lean).
`wf_of_sysReachable` proves the invariants of every reachable workflow and
`causal_acyclic` its acyclicity, and `sysStep_delivery` the timing in I3;
`step_frame` and `sysStep_frame` prove the
per-transition properties; `activation_persists`, `removed_node_never_returns`,
and `removed_edge_never_returns` prove the run properties.

These are properties of admitted transitions over faithful state. Storage
adapters evaluate against views and verify against their actual records before
writing. Verification binds exact evaluated inputs to those records and checks
structural integrity; it does not rerun payload validators or independently
recompute every payload-dependent cleanup decision. The concrete obligations
are detailed in [TRANSITIONS.md](docs/TRANSITIONS.md).

## 8. Restoration and execution boundary

For states containing only activations under one fixed definition,
`restore_state` can replay the occurrence history with external package payload
evidence, rechecking contracts, authority, ingress, and content commitments.
Outbound births are included in this sublanguage. Explicit transfers,
retirements, rewrites, and extensions are outside that replay format.

Checkpoint restoration validates the current dynamic state's invariants and
definition binding without replaying historical contracts or graph changes.
Because a state keeps no past graphs, a delivery over an edge that has since
been removed is checked only against the lifetime identity sets and against
every other delivery over that edge. Acceptance of
a checkpoint is an integrity check for a trusted store; it does not
independently prove reachability from an empty state.

Executable behavior, scheduling, external effects, invocation access policies,
artifact storage, and filesystem workspaces belong to the layers surrounding
the calculus. Kernel admission governs proposed workflow facts. Atomicity of
those facts does not make a worker's external side effects transactional.

Model: `replay_history` and `replay_causal` prove that replaying the history
of a state reached by activations alone, in any causal order, reproduces it up
to the order of acceptance; `replay_sound` that replay accepts only faithful
histories; and `activationRun_of_revision` that a reachable workflow with
`r = |A|` was reached by activations alone. `checkpoint_exact` proves that
checkpoint restoration checks exactly the invariants: a checkpoint passes if and
only if some well-formed state records it, up to the order of its identity
lists. See
[restoration](crates/calculus/src/kernel/checkpoint.rs),
[prepared-plan tests](tests/prepared_plans.rs),
[negative verification tests](tests/verify_negative.rs), and
[adapter equivalence tests](tests/adapter_equivalence.rs).
