# Ontography core

Ontography is a calculus for workflows whose structure can evolve as they run.
It defines where work may happen, how data and authority may move, and how the
workflow itself may change. It can express pipelines, branching decisions,
parallel work, joins, feedback loops, and the creation or removal of stages
through permitted graph rewrites.

A workflow is built from three core pieces:

- **Nodes** are identified positions where work may happen. Executable behavior
  can be attached to them.
- **Edges** define permitted directed routes between nodes, with conditions on
  the packages they accept.
- **Packages** are distinct units of data and authority that work produces,
  transfers, and consumes. A package can be delivered along an edge when it is
  produced or remain at its producer awaiting later transfer.

**Activations** describe how these pieces interact. An accepted occurrence of
work at a node consumes its package inputs, records a result, and may produce
new packages. **Root activations** originate work without input packages. Nodes
can split work into several outputs, join incoming packages, and participate in
feedback loops.

Contracts define acceptable results and package payloads. Authority rules govern
permitted routes, root activations, and changes to the authority carried by
outputs. Graph edits replace nodes and edges while accounting for affected live
packages, and a trusted edit policy decides who may make them. Application code performs the work and
proposes its outcomes; the **kernel** checks and applies admissible changes.

The workflow's state records accepted history and outstanding work. Its
**frontier** is the set of live packages awaiting delivery or consumption. The
surrounding runtime and application layers provide execution hosting, durable
sessions, invocation context, and stored content packages.

The chapters below expand on these pieces, what each can do, and how they
interact.

1. [Nodes](#nodes)
2. [Edges](#edges)
3. [Packages](#packages)
4. [Activations](#activations)
5. [Types, Contracts, and Authority](#types-contracts-and-authority)
6. [Kernel, State, and Frontier](#kernel-state-and-frontier)
7. [Rewriting and Extension](#rewriting-and-extension)
8. [Runtime](#runtime)
9. [Content Packages](#content-packages)
10. [Application Composition](#application-composition)

The [mathematical definition](MATHEMATICAL_DEFINITION.md) specifies the calculus
separately, and the Lean model in [formal/](formal/README.md) states it
normatively, with machine-checked proofs of its invariants.

## Nodes

A node is a graph position; its attached executable performs work. Some
capabilities come from the node interface, while others require session, host,
or application-run access supplied by the application.

The graph gives each node a unique identity. Its `NodeDefinition` supplies a
nonempty set of semantic types, a result contract, and an ingress mode (`Any`
by default, or `All`). The admitted workflow may also give it a root authority
ceiling and permitted authority transitions. These rules determine which
activations it can accept; its implementation decides what work to perform.

Node types describe roles, the result contract checks outcomes, and ingress
determines how package inputs form a trigger. A node can exist without any
executable attached. Attaching one does not create an activation: an execution
can perform work and submit many outcomes over its lifetime. A reusable
[component](#application-composition) combines node semantics with executable
behavior for placement in an application.

Within the workflow, a node can:

1. **Originate root activations.** With a root rule, activate without input
   packages, using authority within its ceiling. This can happen repeatedly,
   including at an `All` node.
2. **Consume individual inputs.** With `Any` ingress, consume one live delivered
   package per activation.
3. **Join inputs.** With `All` ingress, consume exactly one package from every
   current incoming edge, with equal authority across inputs. Different edges
   can carry different object types.
4. **Act as both an origin and a consumer.** Root permission and package ingress
   can coexist.
5. **Compute results.** Attached code can transform data, make decisions, call
   services, run tools or models, or obtain human input. Results must satisfy
   the node's result contract.
6. **Choose downstream routes.** Select outputs and edges according to
   application logic, subject to each edge's contract and authority requirements.
7. **Split or replicate work.** Emit multiple distinct packages to different
   destinations—or multiple packages along the same edge.
8. **Finish a branch.** Consume inputs and record a result while emitting no
   packages.
9. **Produce work for later delivery.** Create outbound packages without an
   existing route. One activation can mix outbound packages and immediate
   deliveries.
10. **Change output authority.** Carry authority unchanged or use permitted
    transitions to reduce, preserve, or amplify it. Each output chooses
    independently.
11. **Participate in feedback loops.** Send new packages to itself through
    self-loops, or revisit other nodes through graph cycles.
12. **Use multiple relationships with the same neighbor.** Parallel edges have
    separate identities, contracts, and authority conditions. An `All` join
    counts each edge separately.
13. **Serve multiple semantic roles.** Carry several node types, satisfying
    different edges' endpoint requirements.

Through its executable and context interfaces, it can:

14. **Run independently of activations.** Start before packages arrive, remain
    alive, submit many proposals, or exit without producing any activation.
15. **Perform concurrent internal work.** Spawn and coordinate its own tasks.
    The execution host also permits multiple different executable definitions
    at one node.
16. **Inspect the current workflow.** Read the kernel definition, inspect
    outgoing edges, and find routes by authority tag.
17. **Inspect outstanding inputs.** Page through pending packages, find a
    complete trigger, or inspect the next package on a particular incoming edge.
18. **Inspect provenance.** Read package records and their producers' inputs,
    following causal ancestry.
19. **Read and import content.** Inspect metadata, read verified payloads or byte
    ranges, use content readers, and import new artifacts.
20. **Prepare or explore context.** Receive configured initial context—none,
    received inputs, or permitted ancestry—and optionally describe packages,
    traverse parents, list collection members, and read their contents.
21. **Begin durable invocations.** Bind an attempt to a node and trigger, with
    context permissions and resource limits. Beginning an invocation does not
    reserve or consume its inputs.
22. **Record what happened during an attempt.** Retain initial input and tool
    responses, record transport-send and acknowledgement evidence, and record
    interruption or failure.
23. **Publish through a bound invocation.** Submit results and emissions tied
    to that invocation. Exact retries of an accepted submission return its
    original activation while submission custody remains valid.
24. **Submit trusted raw proposals.** Submit any activation proposal the kernel
    permits, including one targeting another node. This interface has broader
    scope than invocation-bound publication.
25. **Work with composed artifacts.** Reuse existing content through collections
    and changes packages, representing additions, replacements, and deletions
    while retaining earlier versions.
26. **Keep local persistent state.** Use its node directory across application
    restarts. Application resume relaunches the executable with that directory.
27. **Observe and report execution lifecycle.** Wait for workflow changes,
    report current activity, respond to stop requests, exit, or report failure.

As a reusable component, it can:

28. **Be placed at multiple nodes.** Reuse implementation behavior with different
    identities, configuration, and connections.
29. **Expose named input and output ports.** Declare contracts and supported
    ingress modes, allow additional port names, and bind a port to multiple
    concrete edges.
30. **Describe and validate its configuration.** Provide discoverable component
    metadata and validate configuration and graph placement before execution.

With session, execution-host, or application-run access supplied by the
application, its code can additionally:

31. **Transfer waiting outbound packages** through currently accepting edges.
32. **Retire live packages**, optionally citing an accepted activation as evidence.
33. **Rewrite the graph.** Install an explicit edit that removes and adds nodes
    and edges in one transition, inspecting the admitted replacement and package
    retirements before committing.
34. **Introduce new root and authority policies** on the nodes an edit adds.
35. **Extend the workflow vocabulary** with additional types, authority tags,
    and contracts while preserving existing definitions.
36. **Launch and supervise executables**, including implementations at newly
    created nodes; observe, stop, or abort those executions.
37. **Manage workflow runs.** Create independent sessions, inspect snapshots,
    suspend/resume applications, and use the core's checkpoint or supported
    replay facilities.

Graph rewrites and executable lifecycle require explicit coordination: adding
a node does not automatically launch its implementation. The core's root model
also supports several root-enabled nodes, while the application builder exposes
one entry root.

See [node definitions](crates/calculus/src/graph.rs),
[execution interfaces](crates/runtime/src/hosting.rs), and
[application components](crates/application/src/application.rs).

## Edges

An edge is an identified, directed route from one node to another. It states
which deliveries the workflow permits. Application code chooses when to use
that route and which package to send.

Its topology consists of an identity, a source node, and a target node. Its
semantic definition supplies:

| Part | Meaning |
|---|---|
| Edge types | One or more semantic labels describing the relationship. |
| Source requirements | Node types that the source must possess. |
| Target requirements | Node types that the target must possess. |
| Package contract | The object type and payload validator for deliveries. |
| Authority tags | A nonempty set of tags against which package authority is checked. |
| Authority match | `AnyOf`, requiring at least one listed tag, or `AllOf`, requiring all of them. |

The kernel checks endpoint requirements when admitting the definition. A node
may have additional types beyond those required. Edge types are descriptive
annotations; contracts and authority conditions determine whether a particular
package can travel along the edge.

An edge can deliver a newly created package as part of an activation, or accept
an existing outbound package through an explicit transfer. Both require the
producer to be the edge's source and the package to satisfy its contract and
authority condition. Transfer preserves the package's identity, payload
commitment, and authority. Delivery gives custody to the target node, where the
package becomes available for a later activation.

The graph supports parallel edges, self-loops, and cycles. Two edges connecting
the same nodes are separate routes and may impose different contracts. Each
counts separately toward an `All` join. A self-loop lets a node produce input
for a later activation at itself.

An edge can carry many distinct packages, including several emitted in one
activation. Fan-out produces separate package occurrences for the chosen
routes. Application code selects emissions and pending inputs; adding an edge
does not itself perform a delivery or start an executable.

Edges can be added or removed through [rewriting](#rewriting-and-extension).
Changing routes also affects outstanding packages, particularly receipts at
`All` joins. Accepted history retains the delivery facts that were valid when
they occurred.

See the [graph definitions](crates/calculus/src/graph.rs),
[delivery admission](crates/calculus/src/kernel/admission.rs), and
[graph and edge tests](tests/calculus.rs).

## Packages

A workflow package is one output occurrence created by an accepted activation.
It carries a typed payload and authority from its producer toward one receiver.
Its identity combines the producing activation's identity with an identity for
that particular output. Identical bytes, authority, and destination can therefore
belong to several distinct packages, each independently consumable.

The immutable facts are the producer node, object type, authority, and a digest
committing to the exact payload bytes. The package also records its delivery,
when present, and its lifecycle status. The kernel retains the payload
commitment in the occurrence record; storage of the bytes belongs to the
surrounding layers.

An activation can create packages in two forms:

- **Delivered.** Birth and delivery happen together through a chosen outgoing
  edge. The edge contract determines the object type and validates the bytes.
- **Outbound.** Birth names an object type and leaves the package at its
  producer. No route is required yet. A later transfer chooses an accepting
  edge, checks the payload against its contract, and delivers that same package.

Delivery is recorded at most once. An outbound package has phase `Out` and is
held by its producer; a delivered package has phase `In` and is held by its
receiver. Phase describes delivery, while status describes availability:

| Status | What can happen next |
|---|---|
| Live, outbound | Transfer through an accepting edge, or retirement. |
| Live, delivered | Consumption in an activation at its receiver, or retirement. |
| Consumed | Remains in history, identifying its single consuming activation. |
| Retired | Remains in history with the reason and revision of retirement. |

Consumption happens at most once. Continuing a workflow creates new output
packages, even when their bytes equal an input's bytes. This gives each stage
its own provenance while allowing content storage to reuse identical content.

Retirement explicitly removes outstanding work without inventing a consumer.
It can be requested directly, optionally citing an accepted activation as
evidence, or follow from a graph rewrite. Neither retirement nor consumption
erases the producer or delivery record.

The [frontier](#kernel-state-and-frontier) contains all live packages. The
separate [content packages](#content-packages) chapter explains
immutable artifact packages that workflow payloads can reference: a workflow
occurrence tracks work, while a content package describes stored data.

See [package records](crates/calculus/src/kernel/occurrence.rs),
[birth and transfer tests](tests/outbound_admission.rs), and
[retirement](crates/calculus/src/kernel/retire.rs).

## Activations

An activation is one accepted occurrence of work at a node. It records an
identity, the executing node, a trigger, result bytes, and zero or more output
packages. A node can have many activations over time. Executable startup and an
[invocation attempt](#runtime) are separate events; the activation exists when
the kernel accepts the proposed outcome.

There are two trigger forms:

- **Root activation.** Names a node and initial authority, consumes no input
  packages, and requires a root rule at that node. The chosen authority must
  fit within the rule's ceiling. Roots can occur repeatedly, and several nodes
  can have root permission. Root activation is independent of ingress, so an
  `All` node with a root rule can originate work without completing a join.
- **Package-triggered activation.** Names a nonempty set of live, delivered
  packages held by the same node. Every input must carry exactly the same
  authority, which governs the activation.

For package triggers, the node's ingress determines the required set:

| Ingress | Inputs consumed by one activation |
|---|---|
| `Any` (default) | Exactly one delivered package. |
| `All` | Exactly one delivered package from every current incoming edge. |

An `All` join cannot substitute two packages from one edge for a missing edge.
Parallel edges count separately. Their packages may have different object
types, because each route has its own contract. The application selects a
compatible set and determines how to combine its contents. The kernel's join
rule checks routes and authority; correlating inputs to the same request or
root occurrence requires application policy. An empty incoming-edge set does
not make an empty package trigger legal.

Every activation validates its result against the node's result contract.
The result and package payloads are separate values: the application chooses
both. It may emit nothing, choose one branch, emit along several edges, emit
several packages along the same edge, or combine delivered and outbound
packages. Each output independently carries the governing authority or applies
a permitted authority transition.

Acceptance consumes all inputs, records the activation, and creates every
output together. Rejection leaves kernel state unchanged. A prepared trigger
describes inputs that were valid when checked; it does not reserve them, and
admission checks their availability again. External computation and service
effects remain under application control.

For example, a root emits work to two branches. Each branch consumes its input
and sends a new package to an `All` receiver. The receiver consumes one package
from each branch in a single activation and records the combined result. If
the workflow loops back, later activations create new occurrences, so the
causal history remains acyclic even when the workflow graph has cycles.

See [proposal types](crates/calculus/src/kernel/admission_api.rs),
[admission rules](crates/calculus/src/kernel/admission.rs), and
[root, join, and history tests](tests/calculus.rs).

## Types, Contracts, and Authority

These rules give nodes, edges, and packages their permitted meanings and
interactions. The kernel first admits a consistent definition, then checks
proposed work against it.

A **schema** declares the available node types, object types, and authority
tags. Node types describe roles: one node can possess several, and an edge can
require a set at each endpoint. Object types classify package payloads and
activation results through contracts. These are explicit identifiers; payload
bytes do not infer their type. Edge types are open semantic annotations rather
than members of the schema. Vocabulary can grow through
[extension](#rewriting-and-extension).

A **contract** associates an identity and object type with a validator over
payload bytes. The validator can enforce a data format or an application
predicate. Different contracts can use the same object type while accepting
different payloads.

- A node's contract validates each activation result.
- An edge's contract validates each delivered package payload.
- An outbound package declares a schema object type at birth; its selected
  edge's exact type and payload contract are checked on transfer.

Validators are trusted, pure, deterministic functions. Their accepted payload
set must remain stable when the same contract identity is reconstructed. The
kernel may reuse a successful check for identical content under the same
contract within an operation, so validation cannot depend on invocation counts
or mutable external state.

**Authority** is a set of declared tags. An edge uses `AnyOf` matching by
default, accepting authority containing at least one of its configured tags;
`AllOf` requires every configured tag. Both allow additional tags. This edge
test is independent of the node's `Any`/`All` ingress rule.

A **root rule** sets the maximum initial authority for one node. A root
activation chooses any subset of that ceiling, including the empty set.
Package-triggered activations derive their authority from their inputs, whose
tag sets must be equal; joining inputs does not union their authority.

Each output chooses one of two authority operations:

| Operation | Required permission |
|---|---|
| `Carry` | Preserve the activation's governing authority unchanged. |
| `Transition(target)` | An exact rule for this node, the full governing authority, and the full target authority. |

A transition can remove, retain, add, or replace tags. Removing tags also
requires a rule, and explicitly requesting a preserving transition requires a
matching rule even though `Carry` is available. Rules are applied per output;
one output cannot chain several transitions. Delivery still has to satisfy the
edge's authority condition. Existing packages keep their original authority.

These permissions govern workflow facts. The host application controls who
can submit proposals and which external capabilities executable code receives.

See [schema and policy definitions](crates/calculus/src/graph.rs),
[definition admission](crates/calculus/src/kernel/definition.rs), and
[authority and contract tests](tests/calculus.rs).

## Kernel, State, and Frontier

The **kernel** is an admitted workflow definition and its rule checker. It owns
an immutable graph, schema, contracts, node and edge definitions, root rules, and
authority transitions. Definition admission checks that these agree: every node
and edge has a definition, referenced contracts exist, endpoint types satisfy
edge requirements, and authority policies use the declared vocabulary. One
kernel can govern multiple independent runs.

A **state** records one run: accepted [activations](#activations), all package
records, the current definition binding, identities used over its lifetime, and
revision counters. It exposes producers, consumers, deliveries, and retirements
for inspection. Consumed and retired packages remain in history. The workflow
may contain cycles; its accepted causal history stays acyclic because each
activation creates new output occurrences.

The **frontier** contains exactly the live [packages](#packages). An undelivered
package is held at its producer in phase `Out`; a delivered package is held at
its receiver in phase `In`. Delivery changes phase while keeping the package
live. Consumption or retirement removes it from the frontier. Live does not
mean immediately runnable: an outbound package may lack a route, and an input
at an `All` node may await the rest of its join.

There are five kinds of accepted state change:

| Transition | Effect |
| --- | --- |
| Activation | Records a result, consumes its inputs if any, and creates outputs. |
| Transfer | Delivers one live outbound package through an accepting edge. |
| Retirement | Removes one live package from outstanding work without consuming it. |
| Rewrite | Installs a replacement graph and retires affected live packages. |
| Extension | Adds vocabulary and contracts while preserving graph and frontier. |

An **evaluator** checks a proposal against the current definition and state,
including any required payload validation, and constructs a transition without
mutation. **Verification** checks that the transition still applies to the
actual records and preserves their structural integrity. **Application** verifies
first, then writes all changes together. Verification does not rerun payload
validators. The in-memory state and durable storage use the same verifier;
rejection leaves the state unchanged.

Each accepted transition advances the revision once, even an identity rewrite.
Plans bind to the definition identity, its structural fingerprint, revision,
and a nonce refreshed after application. The nonce distinguishes diverged
in-memory states at equal revisions; exclusively owned storage can fence on
revision. Any intervening transition makes a prepared plan stale. Fingerprints
do not identify executable validator code, so definition changes also preserve
existing validator instances.

States can be cloned for independent exploration. A **checkpoint** captures the
whole state for restoration under its current kernel; restoration checks
ownership, custody, causality, identities, and revision accounting. It is an
integrity check for trusted storage and does not replay historical contracts or
rewrites. For histories containing only activations under a fixed definition,
`to_parts` and `restore_state` support full admission replay with payload
evidence. Transfer, retirement, rewrite, or extension makes that smaller format
insufficient. [Runtime](#runtime) provides durable session ownership and recovery.

The [transition implementation](crates/calculus/src/kernel/transition.rs),
[checkpoint implementation](crates/calculus/src/kernel/checkpoint.rs), and
[adapter equivalence tests](tests/adapter_equivalence.rs) define and exercise
these boundaries.

## Rewriting and Extension

A **rewrite** changes a running workflow's graph while accounting for its live
packages. It can insert a stage, replace a subgraph, remove a branch, or introduce
new places where work originates, all in one atomic transition.

A rewrite carries an explicit **graph edit** and the **principal** asking for it.
The edit names existing nodes and edges to remove and a fragment of new ones to
add. Every edge touching a removed node must be removed too, so an edit never
drops an edge implicitly. Added nodes and edges carry identities never used
before in the workflow, and removed identities never return. Definitions, root
rules, and authority transitions may be given only to added elements: surviving
nodes keep their types, result contracts, ingress, root rules, and authority
transitions, and surviving edges keep their endpoints and annotations. Changing a
definition means replacing the element with a fresh identity, in the same edit.
Added edges may connect surviving and added nodes. New vocabulary must already
exist in the schema.

Preparation admits the complete replacement definition and computes its cleanup.
Then the workflow's **edit policy** decides whether the principal may make the
edit. The policy is trusted, deterministic application code, like a contract
validator: it sees the principal, the edit, the current and admitted next
definitions, and the exact retirements, and its denial leaves the state
unchanged. Sessions accept no edits unless a policy is configured. The resulting
plan exposes the next kernel and exact retirements for inspection before
commitment. Because cleanup sees only the final graph, replacing a route in one
edit keeps work that removing the route first would strand.

Cleanup applies only to live packages:

| Package after the structural change | Effect |
| --- | --- |
| Its holder was removed | Retire as `HolderRemoved`. |
| `Out`, with its holder's outgoing edge identities unchanged | Keep waiting, without checking its payload. |
| `Out`, with outgoing edge identities changed | Keep if any resulting outgoing edge accepts its type, authority, and exact bytes; otherwise retire as `NoAcceptingEdge`. |
| `In`, at a surviving `All` receiver, with its delivery edge removed | Retire as `RouteRemoved`. |
| `In`, at a surviving `Any` receiver | Keep, including receipts on removed edges. |
| Other `In` packages at surviving receivers | Keep. |

Required payload evidence is requested only after a candidate passes metadata
checks. Missing or mismatched required bytes abort preparation; a rejecting
contract simply rules out that candidate. Cleanup inspects the frontier without
replaying consumed history. Retained packages keep their positions, and rewriting
never automatically transfers them or launches executables at new nodes.

Adding routes can remove outstanding work: an outbound package may initially
have no route, then retire when a rewrite adds only a rejecting route. Consequently,
two graph edits can yield the same graph but different frontiers when they affect
the same holder. Sufficient conditions for order independence are independent
graph edits and disjoint affected-holder sets across both orders, ignoring
retirement revision stamps. The
[rewrite tests](tests/frontier_rewrite.rs) cover this case and the
[frontier operation tests](tests/frontier_operations.rs) cover `All` cleanup.

An **extension** strictly adds schema node types, object types, authority tags,
or contracts. It preserves every existing definition and contract, including its
validator instance, and leaves graph, history, and frontier unchanged. It cannot
remove vocabulary, replace a validator, or add nothing. A later rewrite can use
the added vocabulary.

Both operations advance the definition binding and revision. Direct callers
must install the returned kernel together with the state change; a
[runtime session](#runtime) coordinates this. Reopening a session after extension
requires supplying the extended vocabulary and contract registry. The
[rewrite](crates/calculus/src/kernel/rewrite.rs) and
[extension](crates/calculus/src/kernel/extension.rs) APIs expose these checks;
[application extension tests](tests/application_extension.rs) demonstrate resume.

## Runtime

The runtime makes the calculus available to running programs. A
`ProposalRuntime` creates independent **sessions**; each session owns its current
kernel, accepted state, stored payloads, and invocation records. A
`SessionHandle` submits activations, transfers and retires packages, prepares and
commits rewrites, extends vocabulary, and reads the current graph, frontier, and
history. The kernel still decides which changes are admissible.

### Executions, invocations, and activations

These represent different stages of work:

| Concept | Meaning |
| --- | --- |
| **Execution** | A running instance of an executable attached to a graph node. |
| **Invocation** | A recorded work attempt bound to a node, trigger, and context policy. |
| **Activation** | An accepted occurrence in the workflow's causal history. |

An `ExecutionHost` launches opaque Rust async tasks. Several executions can share
a node; one execution can remain alive, perform concurrent work, originate roots,
submit many proposals, or exit without an activation. Its context provides graph
and pending-input observations, payload access, provenance, activity reporting,
and change/stop signals. Notifications can coalesce several revisions; consumers
read the current state after waking. Pending queries and activity reports do not
reserve work or establish a FIFO processing guarantee.

A trusted execution can submit a raw proposal for any node the kernel permits.
An `InvocationHandle` instead fixes the node and trigger for publication. Beginning
an invocation does not consume or reserve its inputs: another accepted operation
can make them unavailable. Acceptance links the invocation to its activation
atomically. An exact retry of an accepted submission returns that activation
while its submission custody remains valid; changing the retry's output fails.
This protects publication retries, while external service calls still require
application-managed retry and effect policies. See [Activations](#activations).

Sessions serialize mutations. Concurrent executions can compute independently,
but each proposal is checked against the state at admission. Termination or
forced abort revokes the execution's submission custody, including handles
retained by detached tasks. A cooperative stop request signals the executable
while allowing it to finish. The host observes exit, failure, panic, and abort,
and interrupts unfinished invocations when their owner ends. Native tasks and
any processes they start need application supervision.

### Context and evidence

An invocation's `ContextPolicy` selects initially prepared inputs: none, received
packages or explicit root input, or permitted causal ancestry. Optional
exploration uses invocation-local opaque handles to describe packages, follow
parents, list collection members, and read bounded payload ranges. Ancestor
metadata and ancestor payload access are separate grants. Cumulative package,
member, byte, and event budgets bound these operations.

The runtime retains exact context and tool-response bytes with **receipts**.
Receipts distinguish preparation, a host-observed transport send, and a worker
acknowledgement; acknowledgement does not prove the worker used that information.
Rejected, interrupted, and failed attempts retain their evidence. Grants control
this context interface; operating-system, filesystem, and network isolation must
come from the host adapter. [Content Packages](#content-packages) explains
artifact grants and retention.

### Persistence and recovery

Sessions can be ephemeral or persistent. Persistent runs store indexed facts in
SQLite and payloads in a sibling object store, with exclusive ownership of the
run. Closing a session stops admission while preserving coherent read access.
A kernel rejection leaves accepted state unchanged. A failure before any write
can leave the session usable; failure after writing begins faults it because
commit acknowledgement is uncertain. Reopening resolves durable state and
performs the required integrity checks before admission can resume.

The graph store uses schema version 11 and the invocation context store uses
version 2. Each version is checked independently; incompatible stores are
rejected without migration. Context version 2 removes the former workspace
policy from stored invocation records, so runs using context version 1 cannot
be reopened by this version.

Ordinary reopening loads the stored current graph and indexed state, including runs
changed by rewrites and other dynamic transitions. It trusts the store owned by
this implementation and does not replay all historical contracts or graph edits.
`open_persistent_verified` provides full replay for fixed-graph activation
histories; histories containing rewrites, transfers, retirements, or vocabulary
extensions need ordinary current-state loading. Exported `StateParts` alone does
not contain an entire session's artifact dependencies or invocation evidence.

Application suspension stops executions while leaving the persistent session
open. Resumption launches fresh executable instances against that state and
interrupts unfinished old invocations; it does not restore an async task's stack.
Application shutdown closes admission permanently. Details of application launch
and binding appear in [Application Composition](#application-composition).

See [session operations](crates/runtime/src/session.rs),
[execution hosting](crates/runtime/src/hosting.rs),
[invocation context](crates/runtime/src/context.rs), and the
[recovery tests](tests/persistent_recovery.rs).

## Content Packages

A workflow [package](#packages) is one occurrence of work with a producer and
lifecycle. A **content package** is an immutable artifact, identified by its
stored content. Many workflow occurrences can refer to the same artifact without
sharing delivery or consumption state.

`ContentStore` imports bytes, returns content identities, verifies stored bytes,
reads ranges or streams, and exports files. `PackageStore` composes those bytes
into four kinds of `PackageDocument`:

| Document | What it represents |
| --- | --- |
| **File** | Immutable file bytes and executable intent. |
| **Collection** | Named members, each referring to another content package. |
| **Changes** | Path replacements or deletions applied to a base collection view. |
| **Symlink** | A recorded target string, which package resolution does not follow. |

Collections can nest. A changes package can reuse a base and unchanged members
without copying them, preserving previous versions. Resolution computes the
current visible tree under limits on depth, document count, entries, and metadata
size. Invalid paths, ambiguous overlapping changes, and cycles are rejected.
Content identity commits to exact representation bytes; different compositions
can describe equivalent visible trees while retaining different identities.

A `PackageEnvelope` names the artifact inside ordinary workflow payload bytes.
The kernel still sees a payload and its contract. At invocation publication, the
runtime checks that an emitted envelope's document and full dependency closure
are declared and retained. Trusted raw submissions carry explicit dependencies;
ordinary arbitrary bytes do not implicitly declare referenced artifacts.

**Retention and access are separate.** A changes package must retain its base and
hidden historical dependencies to preserve its representation. An invocation's
grants expose its resolved visible view; retained old files are not automatically
readable or eligible for republication by a worker. Staged imports keep
tentative content alive until the caller accepts it, and release their own
retention on failure without discarding another operation's content.

Applications own filesystem workspaces: importing directories, creating and
cleaning up checkouts, capturing edits, and deciding when and where to publish
them. Adapters use core's content and package APIs to construct artifacts,
ordinary invocation receipts to record their operations, and submission APIs
to publish the resulting packages with their dependency closures.

See [content composition](crates/content/src/package.rs),
[staged retention tests](tests/content_retention.rs),
and the [composition example](tests/content_composition_probe.rs).

## Application Composition

The application layer connects a workflow definition to reusable implementations
and launch policy. A **component** bundles node semantics with executable
behavior. A **placement** gives it a concrete node identity and connections in an
application. The same component can be placed repeatedly; each placement launches
its own execution and has its own node identity.

`NodeComponent` combines a `NodeConfig`, executable factory, optional entry-root
authority ceiling, and permitted authority transitions. Node configuration carries
semantic types, a result contract, ingress mode, and invocation context policy.
`EdgeConfig` supplies semantic types, endpoint requirements, payload contract,
authority tags, and the authority matching rule.

`ApplicationBuilder` places components, connects them, collects vocabulary and
contracts, and admits the resulting kernel. It requires exactly one entry with an
explicit root ceiling, which may be empty. Only entry placement installs a root
rule; placing the same root-capable component elsewhere does not. The calculus
itself supports several root-enabled nodes. Declarative formats reject explicit
root-authority declarations on non-entry placements. A compiled application can
also carry an edit policy or be extended with additional vocabulary.

### Declarative composition

Applications can be authored in Rust or through JSON resolved by a trusted
`ApplicationRegistry`. The registry supplies contract validators, implementation
factories, and configuration/placement validation. The higher-level project
format adds providers and named ports:

- A **provider** loads a family of component specifications and registers their
  implementations and contracts.
- A **description** exposes a component's identity, purpose, semantic types,
  result contract, named input/output contracts, supported ingress modes, and
  optional configuration schema.
- A **binding** connects those named ports to concrete edge identities and turns
  user configuration into implementation configuration. A port can bind several
  edges; components can support additional dynamic port names.

Declared port contracts must agree. A connection between two dynamic ports needs
an explicit contract. Authority policy is explicit; preparation does not infer
grants. Preparation produces an admitted application, expanded native JSON,
component descriptions, and retained specifications without launching workloads
or installing dependencies. Optional JSON schemas describe configuration; the
registered validators remain authoritative. Provider identity and specifications
are references rather than guaranteed version pins.

### Launching and resuming

`start` creates a persistent run under `.ontography/runs`; `start_in` selects the
state root, and `start_ephemeral` opens an in-memory session. Every declared node
launches. The host schedules non-entry executions before the entry; this order
does not guarantee that their initialization finishes first. Only the fresh
entry receives the initial input and compiled root authority. Its executable
decides when to propose the root activation.

Each execution receives an `ApplicationContext` with runtime observations,
content access, invocation facilities, and lifecycle signals.
Persistent runs also provide a per-node state directory, reused on resume.
A `RunningApplication` exposes executions, the session, snapshots, waiting,
suspension, and shutdown. Waiting for idle means no hosted execution remains; live
packages may still exist.

Resumption supplies no new entry input or root authority. By default, retained
component bindings must match the current graph's node identities. Graph rewrites
can remove bound nodes or introduce unbound ones, causing resume to fail with
binding drift. Explicit `resume_partial` launches only surviving bindings and
leaves new unbound nodes without executables. Adding a graph node does not itself
launch its implementation; orchestration must coordinate those changes.

See [application APIs](crates/application/src/application.rs),
[project composition](crates/application/src/project.rs),
[authoring tests](tests/application_authoring.rs), and
[lifecycle tests](tests/application_lifecycle.rs).

### Using the library

The root package re-exports all layers as the Rust crate `ontography`. From a
sibling project:

```toml
[dependencies]
ontography = { package = "ontography-core", path = "../ontography-core" }
```

For narrower dependencies, use `ontography-calculus`, `ontography-content`,
`ontography-runtime`, or `ontography-application` directly.
The [integration tests](tests) provide executable examples. Run the workspace
suite from this repository with:

```sh
cargo test --workspace
cargo test --release --workspace
```

The [mathematical definition](MATHEMATICAL_DEFINITION.md),
[storage transition specification](docs/TRANSITIONS.md),
[frontier rewriting guide](docs/FRONTIER_REWRITING.md), and
[Lean model](formal/README.md) provide further detail.
The [previous README](docs/archive/README-2026-09-26.md) is preserved in the archive.
