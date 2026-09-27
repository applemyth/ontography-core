# Kernel traces for the Lean oracle

A trace records one run of the kernel: the initial definition, the parameters
the law takes for the whole run (the validators, the payload commitment `H`,
and the rewrite grammar), and the operations in the order they ran. The Rust
test `tests/lean_oracle.rs` records traces and fills in the kernel's outcome
after every operation. The Lean oracle (`Oracle/Main.lean`) replays a trace
with the model's `sysStep`, threading the definition through rewrites and
extensions, and prints the model's outcome after every operation in the same
canonical form, so the two can be compared step by step.

Build and run the oracle by hand:

```
cd formal && lake build oracle
.lake/build/bin/oracle < trace.json
```

This document is the format's specification. Version: `ontography-lean-trace/2`.
Version 1 carried each contract's validator inside the contract and had no
grammar, rewrites, or extensions.

## Encodings

| Value | Encoding |
| --- | --- |
| Activation identity | The kernel's `u128` as a decimal string of digits only, such as `"42"`. The model reads it as a `Nat`. |
| Package identity | `[producer, output]`: the producer's activation identity, then the output ordinal as a JSON number. |
| Bytes | Hexadecimal, two digits per byte. Traces are written lowercase; the oracle also reads uppercase in operations. |
| Digest | The 64 lowercase hex digits of a `ContentDigest`. The model treats it as an opaque string. |
| Authority | An array of tag strings. It denotes a set: in a trace, order and repeats carry no meaning. |
| Identifier sets | Arrays of strings, likewise sets (node types, requirements, edge tags, edge types, interfaces). |

## Trace

A trace is one JSON object:

| Field | Meaning |
| --- | --- |
| `format` | `"ontography-lean-trace/2"`. |
| `name` | A name for reports. |
| `seed` | Optional. The seed of a random run. |
| `known_disagreement` | Optional. `{"step": n, "summary": text}` marks a trace whose first disagreement is at step `n`; see [Committed traces](#committed-traces). |
| `validators` | The validator each contract identity names: the model's `accepts`. |
| `digests` | The payload commitment `H`. |
| `grammar` | The rewrite grammar: a list of productions. |
| `definition` | The initial definition `Δ`. |
| `ops` | The operations, in order. |

Any other field is refused by the Rust decoder and ignored by the oracle.

### Validators

`validators` maps each contract identity to one of a fixed menu that both
sides implement:

| Validator | Accepts |
| --- | --- |
| `"accept_all"` | every payload |
| `"reject_all"` | no payload |
| `"first_byte_even"` | a nonempty payload whose first byte is even |
| `{"bytes_equal": hex}` | exactly the given bytes |

The model's `accepts c bytes` is the validator of `c` applied to `bytes`, for
the whole run: a contract identity names one predicate for the workflow's
lifetime, which is what the kernel's shared-validator requirement on
extensions and rewrites enforces. Every contract the definition or an
extension registers must have a validator, or the trace is malformed. The
table may name contracts nothing registers.

### Payload commitment

`digests` maps the lowercase hex of a payload to the lowercase hex of
`ContentDigest::compute` of those bytes. The model's `H bytes` is the table's
entry for `bytes`. Every payload an operation commits to, checks, or offers as
evidence (each emission's payload, each transfer's payload, each evidence
value) must have an entry, or the trace is malformed. Activation results are
never committed and need none. The table may hold entries no operation uses.

### Definition

```json
{
  "schema": {"node_types": ["n"], "object_types": ["t"], "tags": ["run"]},
  "contracts": [{"id": "c", "object_type": "t"}],
  "nodes": ["a", "b"],
  "edges": [{"id": "ab", "source": "a", "target": "b"}],
  "node_definitions": [
    {"node": "a", "types": ["n"], "result_contract": "c", "ingress": "any"}
  ],
  "edge_definitions": [
    {"edge": "ab", "types": ["flow"], "source_requirements": ["n"],
     "target_requirements": [], "package_contract": "c", "tags": ["run"],
     "authority_match": "any_of"}
  ],
  "transitions": [{"node": "a", "source": ["run"], "target": []}],
  "roots": [{"node": "a", "ceiling": ["run"]}]
}
```

`ingress` is `"any"` or `"all"`; `authority_match` is `"any_of"` or `"all_of"`.
Each field decodes to the field of `Ontography.Definition` of the same meaning.
The definition must be one the kernel admits. The oracle does not check
admission; the Rust test admits every definition with `Kernel::admit` before
running it, so the model's `Admitted` hypotheses hold of every trace it writes.

### Grammar

Each production is `L ← K → R`, with `K` given by its node and edge symbols:

```json
{"id": "stage:ab",
 "left": {fragment},
 "interface_nodes": ["X", "Y"],
 "interface_edges": [],
 "right": {fragment}}
```

A fragment has the six graph fields of a definition (`nodes`, `edges`,
`node_definitions`, `edge_definitions`, `transitions`, `roots`), naming
rule-local symbols; it decodes to `Ontography.Fragment`. Every production must
be one the kernel registers with `RewriteProduction::new`, and their
identities must be distinct, as `RewriteGrammar::new` requires. The grammar is
fixed for the run.

### Operations

Each operation is an object whose `op` names its kind. Each may carry an
`expect` field, written by the kernel; the oracle ignores it. The first three
kinds are `SysOp.step`, and the last two replace the definition.

**Activation**, `Op.activate id proposal`:

```json
{"op": "activate", "id": "42",
 "trigger": {"orig": {"node": "a", "authority": ["run"]}},
 "result": "72",
 "emissions": [
   {"destination": {"delivered": "ab"}, "authority": "carry", "payload": "6f6b"},
   {"destination": {"outbound": "t"}, "authority": {"transition": []}, "payload": ""}
 ]}
```

The trigger is `{"orig": {"node", "authority"}}` for `Trigger.orig` or
`{"pkgs": [package, ...]}` for `Trigger.pkgs`. A package trigger names a set:
its inputs are distinct, because the kernel's proposal holds a set of inputs
and the model's list is read as that set. The recorder writes the inputs in
ascending order. An emission's destination is `{"delivered": edge}` or
`{"outbound": object_type}`, and its authority is `"carry"` or
`{"transition": authority}`.

The kernel's `Kernel::activate` draws a fresh identity. For an accepted
activation the recorder writes the identity drawn. A rejected proposal
discloses none, so the recorder writes a fresh identity absent from the
state, which the model's freshness premise treats as the kernel's draw would
be treated. Replaying a committed trace evaluates each activation under its
recorded identity with `Kernel::evaluate_activation` and `State::apply`, which
is what `activate` does with the identity it draws; a reused identity is
rejected by `apply` and by the model's `S.activations a = none` premise.

**Transfer**, `Op.transfer package edge payload`, run through
`Kernel::prepare_transfer` and `Kernel::commit_transfer`:

```json
{"op": "transfer", "package": ["42", 3], "edge": "ab", "payload": "6f6b"}
```

**Explicit retirement**, `Op.retire package evidence`, run through
`Kernel::retire`:

```json
{"op": "retire", "package": ["42", 3], "evidence": null}
```

`evidence` is required: `null` or an activation identity.

**Rewrite**, `SysOp.rewrite request evidence`, run through
`Kernel::prepare_rewrite` and `Kernel::commit_rewrite`:

```json
{"op": "rewrite", "production": "stage:ab",
 "match": {"nodes": [["X", "a"], ["Y", "b"]], "edges": [["E", "ab"]],
           "fresh_nodes": [["Z", "z1"]], "fresh_edges": [["F", "f1"], ["G", "g1"]]},
 "evidence": {"<digest>": "6f6b"}}
```

`match` holds the four bindings of `Ontography.Match` as `[symbol, identity]`
pairs: `L`'s symbols to current identities, and those of `R ∖ K` to fresh
ones. Each binding names a symbol at most once, since the kernel's
`RewriteMatch` holds maps. `evidence` maps a digest to the bytes offered for
it: the model's evidence list and the kernel's evidence map. The offered bytes
need not match the digest; a mismatch is the kernel's and the model's to find.

**Extension**, `SysOp.extend schema contracts`, run through
`Kernel::prepare_extension` and `Kernel::commit_extension`:

```json
{"op": "extend",
 "schema": {"node_types": ["n"], "object_types": ["t"], "tags": ["run", "extra"]},
 "contracts": [{"id": "c", "object_type": "t"}, {"id": "late", "object_type": "t"}]}
```

`schema` and `contracts` are the whole new vocabulary and registry, not the
additions. The kernel's replacement is the current graph and annotations under
them, admitted with `Kernel::admit`; a replacement the kernel does not admit
is a rejected extension, as the model's `next.Admitted` premise makes it.

**Expectation.** `expect` is `{"accepted": bool, "state": state}`, where
`state` is the canonical state after the operation and may be omitted. A
hand-written trace may state only `accepted`; the Rust test then requires the
kernel to decide as stated, and fills in the state itself.

### Plans

The kernel prepares a rewrite, extension, or transfer against one exact state
and refuses to commit it after the state changes. The model has no plans: its
transitions are functions of the current definition and state. So the Rust
test checks stale rewrite and extension plans against the kernel alone: a
plan committed after an accepted operation must be refused as stale and leave
the state unchanged, and the refused commit is not in the trace. A plan
committed with no change since its preparation is recorded as an ordinary
operation at the point of its commit.

## Oracle output

The oracle starts from the trace's definition and `State.initial` of it, and
applies `sysStep accepts H grammar` to each operation in turn. After each it
writes one line of JSON:

```json
{"step": 0, "accepted": true, "state": {...}}
```

`accepted` is whether `sysStep` returned a successor, and `state` is the
canonical encoding of the definition and state after the operation: the
successor's, or the unchanged predecessor's after a rejection. It writes one
line per operation and exits with status 0, or writes a message to standard
error and exits with status 2 for a malformed trace. The oracle has no rule of
its own: it decodes the trace, calls `sysStep`, and encodes the result.

## Canonical state

Both sides encode a running workflow the same way, the kernel from its
current `Kernel` and `State::checkpoint`, and the model from its `Definition`
and `State`:

```json
{
  "definition": {
    "schema": {"node_types": ["n"], "object_types": ["t"], "tags": ["run"]},
    "contracts": [{"id": "c", "object_type": "t"}],
    "nodes": ["a", "b"],
    "edges": [{"id": "ab", "source": "a", "target": "b"}],
    "node_definitions": [...],
    "edge_definitions": [...],
    "transitions": [...],
    "roots": [...]
  },
  "activations": [
    {"id": "42", "node": "a",
     "trigger": {"orig": {"node": "a", "authority": ["run"]}},
     "result": "72",
     "outputs": [
       {"package": ["42", 0], "edge": "ab", "object_type": "t",
        "authority": ["run"], "digest": "c8c3...2797"}
     ]}
  ],
  "packages": [
    {"id": ["42", 0], "object_type": "t", "authority": ["run"],
     "digest": "c8c3...2797", "producer_node": "a",
     "delivery": {"edge": "ab", "receiver": "b"}, "status": "live"}
  ],
  "used_nodes": ["a", "b"],
  "used_edges": ["ab"],
  "definition_changes": 0,
  "revision": 1
}
```

- `definition` is the current definition, each component a canonical set:
  the schema's three lists sorted and deduplicated; `contracts`, `edges`,
  `node_definitions`, `edge_definitions`, and `roots` sorted by their
  identity; `transitions` sorted by node, then source, then target, each
  compared as a sorted list; repeated entries removed; and every list inside
  an entry sorted and deduplicated. Two definitions encode alike exactly when
  they are equal as sets, component by component. Validators are not part of
  a definition; they are the run's `validators`.
- `activations` lists every accepted activation in ascending numeric order of
  identity. An activation's `outputs` list output `i` as package `[id, i]`, in
  ascending order of `i`; `edge` is the birth delivery edge or `null`.
- A package `trigger` lists its inputs in ascending order.
- `packages` lists every package record in ascending order of producer, then
  output. `delivery` is `null` or `{"edge", "receiver"}`. `status` is
  `"live"`, `{"consumed": activation}`, or
  `{"retired": {"reason", "revision", "evidence"}}`, with `reason` one of
  `"holder_removed"`, `"no_accepting_edge"`, `"route_removed"`, and
  `"explicit"`, and `evidence` `null` or an activation identity.
- Every authority, `used_nodes`, and `used_edges` is sorted and deduplicated.
  Strings sort by their UTF-8 bytes.
- `definition_changes` and `revision` are numbers.

The model's fields map to it as follows. The domains of `A` and `P` are read
from `activationIds` and `packageIds`; an identity listed there without a
record would encode as `null`, which a well-formed state never produces. The
ghost field `edgeLog` contributes only its identities, as `used_edges`
(the kernel's `used_edge_ids`), and `changeLog` only its length, as
`definition_changes`. Fields the kernel does not record are not encoded: the
incidence of `edgeLog`, the revisions in `changeLog`, and the order of
`activationIds` and `packageIds`. The checkpoint's `definition_id` and
`definition_fingerprint` have no counterpart in the model and are not
encoded either.

The test compares `accepted` and the canonical state, definition included, at
every step. It does not compare rejection reasons, which the model does not
have.

## Committed traces

`tests/lean_traces/*.json` are hand-written regression traces, replayed on
every test run. Each states the kernel's expected acceptance of every
operation, and its digest table is checked against `ContentDigest::compute`.

`tests/lean_traces/disagreements/*.json` are minimized traces on which the
kernel and the model are known to disagree, each marked with
`known_disagreement`. The test requires each to still disagree first at the
stated step, so a fix on either side is noticed and the trace moved.

A disagreement found by random exploration is written, with the kernel's
outcome and state after every operation, to `target/lean-oracle/<seed>.json`.
