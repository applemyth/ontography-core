# Kernel traces for the Lean oracle

A trace records one run of the kernel under a fixed definition: the
definition, the parameters the law takes (the validators and the payload
commitment `H`), and the operations in the order they ran. The Rust test
`tests/lean_oracle.rs` records traces and fills in the kernel's outcome after
every operation. The Lean oracle (`Oracle/Main.lean`) replays a trace with the
model's `step` and prints the model's outcome after every operation, in the
same canonical form, so the two can be compared step by step.

Build and run the oracle by hand:

```
cd formal && lake build oracle
.lake/build/bin/oracle < trace.json
```

This document is the format's specification. Version: `ontography-lean-trace/1`.

## Encodings

| Value | Encoding |
| --- | --- |
| Activation identity | The kernel's `u128` as a decimal string of digits only, such as `"42"`. The model reads it as a `Nat`. |
| Package identity | `[producer, output]`: the producer's activation identity, then the output ordinal as a JSON number. |
| Bytes | Hexadecimal, two digits per byte. Traces are written lowercase; the oracle also reads uppercase in operations. |
| Authority | An array of tag strings. It denotes a set: in a trace, order and repeats carry no meaning. |
| Identifier sets | Arrays of strings, likewise sets (node types, requirements, edge tags, edge types). |

## Trace

A trace is one JSON object:

| Field | Meaning |
| --- | --- |
| `format` | `"ontography-lean-trace/1"`. |
| `name` | A name for reports. |
| `seed` | Optional. The seed of a random run. |
| `known_disagreement` | Optional. `{"step": n, "summary": text}` marks a trace whose first disagreement is at step `n`; see [Committed traces](#committed-traces). |
| `definition` | The definition `Δ`. |
| `digests` | The payload commitment `H`. |
| `ops` | The operations, in order. |

Any other field is refused by the Rust decoder and ignored by the oracle.

### Definition

```json
{
  "schema": {"node_types": ["n"], "object_types": ["t"], "tags": ["run"]},
  "contracts": [{"id": "c", "object_type": "t", "validator": "accept_all"}],
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

A contract's `validator` is one of a fixed menu that both sides implement:

| Validator | Accepts |
| --- | --- |
| `"accept_all"` | every payload |
| `"reject_all"` | no payload |
| `"first_byte_even"` | a nonempty payload whose first byte is even |
| `{"bytes_equal": hex}` | exactly the given bytes |

The model's `accepts c bytes` is the validator of contract `c` applied to
`bytes`. An identity outside the registry accepts nothing; an admitted
definition never asks for one.

### Payload commitment

`digests` maps the lowercase hex of a payload to the lowercase hex of
`ContentDigest::compute` of those bytes (64 digits). The model's `H bytes` is
the table's entry for `bytes`, an opaque `Digest` string. Every payload an
operation commits to or checks (each emission's payload, each transfer's
payload) must have an entry, or the trace is malformed. Activation results
are never committed and need none. The table may hold entries no operation
uses.

### Operations

Each operation is an object whose `op` names its kind. Each may carry an
`expect` field, written by the kernel; the oracle ignores it.

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

**Expectation.** `expect` is `{"accepted": bool, "state": state}`, where
`state` is the canonical state after the operation and may be omitted. A
hand-written trace may state only `accepted`; the Rust test then requires the
kernel to decide as stated, and fills in the state itself.

## Oracle output

The oracle starts from `State.initial Δ` and applies `step accepts H Δ` to
each operation in turn. After each it writes one line of JSON:

```json
{"step": 0, "accepted": true, "state": {...}}
```

`accepted` is whether `step` returned a successor, and `state` is the
canonical state after the operation: the successor, or the unchanged
predecessor after a rejection. It writes one line per operation and exits
with status 0, or writes a message to standard error and exits with status 2
for a malformed trace. The oracle has no rule of its own: it decodes the
trace, calls `step`, and encodes the result.

## Canonical state

Both sides encode a state the same way, the kernel from `State::checkpoint`
and the model from its `State`:

```json
{
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

The test compares `accepted` and the canonical state at every step. It does
not compare rejection reasons, which the model does not have.

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
