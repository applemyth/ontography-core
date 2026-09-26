# Frontier rewriting in this checkout

This guide accompanies the normative [transition specification](TRANSITIONS.md).
The sibling application's older guide does not specify this checkout.

A package records immutable type, authority, payload commitment, and producer
node, plus one optional delivery and one status: live, consumed, or retired.
An undelivered (`Out`) package is held by its producer; a delivered (`In`)
receipt is held by its receiver. Only live packages participate in cleanup.

## Preparation and commit

A grammar permits annotated productions `L ← K → R`. A match binds `L` to the
current graph and allocates unused identities for `R \ K`. Preserved interface
elements keep their incidence and annotations; deleting a node requires the
matching deletion of its incident edges. The replacement definition is admitted
against the current schema and contract registry before cleanup runs.

The prepared transition carries its exact predecessor binding and proposed
retirements. Both the in-memory state and SQLite rows run the same verifier
before mutation. Intervening operations make the plan stale. A successful rewrite
advances the revision and definition-change count once, even for an identity
rewrite or when it retires several packages.

## Cleanup policy

| Live package | Fate |
| --- | --- |
| Its holder is removed | Retire as `HolderRemoved`. |
| `Out`, surviving holder's outgoing edges unchanged | Keep without reading its payload. |
| `Out`, outgoing edges changed | Keep if an edge accepts its type, authority, and bytes; otherwise retire as `NoAcceptingEdge`. |
| `In`, surviving `All` holder loses its delivery edge | Retire as `RouteRemoved`. |
| `In`, surviving `Any` holder | Keep, including a receipt on an old edge. |

Cleanup is intentionally non-monotone in outgoing edges. An outbound package
may be born without any route. Adding only a rejecting edge touches its holder,
rechecks it, and retires it; an identity rewrite leaves it waiting. This is a
policy consequence, not a guarantee that adding routes preserves work. Explicit
transfer is a separate operation; rewrites never automatically deliver packages.

Graph independence alone does not imply commutation. Two edge additions from
the same holder overlap for cleanup. One rejecting addition can retire waiting
work before another accepting addition arrives. T4 defines sufficient graph
and affected-holder independence; tests cover both independent real rewrites
and this counterexample, ignoring only retirement revision stamps.

## Trust, evidence, and cost

A grammar is an authority grant. Productions can introduce root rules and
authority transitions, including from an empty left side, within the schema.
The direct kernel accepts the caller's grammar; the runtime owns its configured
grammar. Constructing a production checks identity, topology, and interface;
grammar registration rejects duplicate production identities. Kernel-specific
annotation and schema validation occurs when a production is used.

Evidence is required only when a changed holder has a candidate edge whose
metadata accepts the package. A missing or mismatched required payload, or a
validator that panics when invoked, aborts that whole preparation atomically.
Candidate checks stop at the first accepting edge. Unchanged holders,
deleted holders, receipts, and candidates rejected on metadata need no bytes.
Validators must be pure. Transfer and rewrite catch validator panics as typed
errors; direct activation and replay propagate them. Session activation catches
them before publication.

Preparation scans the live frontier, lifetime identity sets, and graph/rule
structure. It re-admits the whole replacement definition; total cost is not
`O(|F|)`. An outgoing-edge index avoids a whole-graph edge scan per package, and
each rechecked package fetches its bytes at most once across candidate edges.
Hashing and predicate work still depend on candidate count and payload size.
No consumed activation history or activation-result payload is needed.
