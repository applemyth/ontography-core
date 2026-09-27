# Ontography calculus

This document specifies the workflow calculus implemented in this checkout.
Its basic objects are nodes, edges, and package occurrences. Activations record
their interaction; transitions change the graph or its occurrence state. The
[README](README.md) explains the concepts and the surrounding execution APIs.
The [transition specification](docs/TRANSITIONS.md) gives the concrete storage
records, verifier obligations, and adapter interface.

This is an implementation-aligned specification. The linked tests exercise its
rules; they are not a machine-checked proof of every possible execution.

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
not identify executable validator code. A rewrite grammar is a separate trusted
policy supplied to the kernel or configured on the runtime.

Implementation: [graph declarations](crates/calculus/src/graph.rs) and
[definition admission](crates/calculus/src/kernel/definition.rs).

## 2. Packages, activations, and state

A package occurrence has identity `p = (a, i)`, where `a = producer(p)` is its
unique producing activation and `i` distinguishes that activation's outputs.
Its record is:

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

## 3. Activation admission

Write `Δ; S ⊢ proposal ⇓ τ` when evaluation accepts a proposal and constructs
a transition. Here `S` is a well-formed state bound to `Δ`. Evaluation reads the
state and does not mutate it. Every accepted transition is bound to the evaluated
definition identity, fingerprint, revision, and nonce; the revision must have
room for one increment.

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
observation alone do not reserve inputs.

Implementation and coverage: [admission](crates/calculus/src/kernel/admission.rs),
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

## 5. Graph rewriting

A grammar contains permitted productions `L ← K → R`. `L` and `R` are annotated
graph fragments admitted under the current schema and contracts; `K` identifies
the preserved interface. A request provides an injective match of `L` into the
current graph and fresh node and edge identities for `R` outside `K`.

Admission requires preservation of matched topology and annotations. A preserved
node keeps its types, result contract, ingress, root ceiling, and authority
transitions; a preserved edge keeps its endpoints and annotations. Deleting a
node requires deleting every incident edge. Fresh identities must never have
appeared in that state's lifetime identity sets. The complete replacement
definition `Δ'` is admitted before the change is committed.

A production may introduce new root rules and authority transitions on new
nodes, including when `L` is empty. Existing consumed or retired records remain
historical facts. Live packages are cleaned up under `Δ'` by these rules:

| Condition | Effect |
| --- | --- |
| Holder is deleted | Retire as `HolderRemoved`. |
| `Out`, holder survives with unchanged outgoing edge identities | Keep. |
| `Out`, outgoing edge identities change | Keep iff some outgoing edge accepts its type, authority, and committed bytes; otherwise retire as `NoAcceptingEdge`. |
| `In`, surviving holder has `Any` ingress | Keep. |
| `In`, surviving holder has `All` ingress | Keep iff the delivery edge remains incoming; otherwise retire as `RouteRemoved`. |

All structural retirements use the rewrite's successor revision and have no
explicit evidence. Graph replacement, identity allocation, and cleanup commit
together. A missing or mismatched required payload, or a failing evaluation,
aborts the whole preparation. Contract rejection makes a candidate route
unacceptable; a validator panic aborts evaluation.

The rewrite does not deliver packages or launch executables. Adding a rejecting
route can retire previously waiting work, so adding edges does not generally
preserve the frontier. Sufficient conditions for commutation, ignoring retirement
revision stamps, are independent graph changes and disjoint affected-holder
sets across both application orders; the precise conditions are in the
[transition specification](docs/TRANSITIONS.md).

Implementation: [rewriting](crates/calculus/src/kernel/rewrite.rs) and
[cleanup](crates/calculus/src/kernel/frontier.rs).

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

The rules preserve these properties:

- Every package belongs to exactly one producer's output map.
- Every package is exactly one of live, consumed, or retired. Only live,
  delivered packages can be consumed, at most once.
- Consumed inputs share their activation's recorded node and governing authority.
- Delivery happens at most once, over a route admitted when it occurred.
- Every live holder exists in the current graph. A live receipt at an `All`
  node names a current incoming edge.
- Immutable package facts remain unchanged, and deleted graph identities are
  never reused within the state's lifetime.
- The producer-to-consumer history is acyclic and revision accounting is exact.

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
Acceptance of a checkpoint is an integrity check for a trusted store; it does
not independently prove reachability from an empty state.

Executable behavior, scheduling, external effects, invocation access policies,
artifact storage, and filesystem workspaces belong to the layers surrounding
the calculus. Kernel admission governs proposed workflow facts. Atomicity of
those facts does not make a worker's external side effects transactional.

See [restoration](crates/calculus/src/kernel/checkpoint.rs),
[prepared-plan tests](tests/prepared_plans.rs),
[negative verification tests](tests/verify_negative.rs), and
[adapter equivalence tests](tests/adapter_equivalence.rs).
