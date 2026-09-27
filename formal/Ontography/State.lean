import Ontography.Definition

/-!
# Packages, activations, and state

MATHEMATICAL_DEFINITION §2 and TRANSITIONS §1–§2. A state carries the accepted
activation map `A`, the package map `P`, the lifetime identity sets, the
definition-change count, and the revision `r`. The nonce and the definition
binding are implementation fences and are not modeled.

Two fields record strictly more than the kernel's `State` does, so that every
invariant is a property of one state rather than of its history:

* `edgeLog` keeps each edge ever admitted together with its incidence. Its
  identities are the kernel's `used_edge_ids`, and it lets I3's incidence claim be
  checked on a state; `sysStep_delivery` proves that each delivery is made over an
  edge of the definition in force.
* `changeLog` keeps the revision of each definition change. Its length is the
  kernel's `definition_changes`, and it states exactly which revisions
  structural retirements may carry.

`activationIds` and `packageIds` list the domains of `A` and `P` in acceptance
and birth order. They make `|A|` and the revision-accounting counts finite, and
their order witnesses causal acyclicity.
-/

namespace Ontography

structure Delivery where
  edge : EdgeId
  receiver : NodeId
  deriving DecidableEq, Repr

inductive Reason where
  | holderRemoved
  | noAcceptingEdge
  | routeRemoved
  | explicit
  deriving DecidableEq, Repr

structure Retirement where
  reason : Reason
  revision : Nat
  evidence : Option ActivationId
  deriving DecidableEq, Repr

inductive Status where
  | live
  | consumed (consumer : ActivationId)
  | retired (retirement : Retirement)
  deriving DecidableEq, Repr

/-- `P(p) = (type, authority, digest, producer_node, delivery, status)`. -/
structure PackageRecord where
  objectType : ObjectType
  authority : Authority
  digest : Digest
  producerNode : NodeId
  delivery : Option Delivery
  status : Status
  deriving DecidableEq, Repr

namespace PackageRecord

/-- `holder(p)`: the receiver once delivered, otherwise the producer's node. -/
def holder (r : PackageRecord) : NodeId :=
  match r.delivery with
  | some d => d.receiver
  | none => r.producerNode

/-- The retirement of a retired package. -/
def retirement? (r : PackageRecord) : Option Retirement :=
  match r.status with
  | .retired ret => some ret
  | _ => none

end PackageRecord

inductive Trigger where
  | orig (node : NodeId) (authority : Authority)
  | pkgs (inputs : List PackageId)
  deriving DecidableEq, Repr

/-- The consumed inputs `I` of a trigger; a root has none. -/
def Trigger.inputs : Trigger → List PackageId
  | .orig .. => []
  | .pkgs inputs => inputs

/-- Birth metadata of one output, including its birth delivery edge, if any. -/
structure Output where
  edge : Option EdgeId
  objectType : ObjectType
  authority : Authority
  digest : Digest
  deriving DecidableEq, Repr

/-- `A(a) = (node_a, trigger_a, result_a, O_a)`, where output `i` of `a` is package `(a, i)`. -/
structure Activation where
  node : NodeId
  trigger : Trigger
  result : Bytes
  outputs : List Output
  deriving DecidableEq, Repr

structure State where
  activations : ActivationId → Option Activation
  packages : PackageId → Option PackageRecord
  activationIds : List ActivationId
  packageIds : List PackageId
  usedNodes : List NodeId
  edgeLog : List Edge
  changeLog : List Nat
  revision : Nat

namespace State

/-- The empty state bound to `Δ`. -/
def initial (Δ : Definition) : State where
  activations _ := none
  packages _ := none
  activationIds := []
  packageIds := []
  usedNodes := Δ.nodes
  edgeLog := Δ.edges
  changeLog := []
  revision := 0

variable (S : State)

/-- `d`, the number of definition changes. -/
def definitionChanges : Nat := S.changeLog.length

/-- The kernel's `used_edge_ids`. -/
def usedEdges : List EdgeId := S.edgeLog.map (·.id)

/-- `O_producer(p)(p)`: the birth metadata of `p`. -/
def output? (p : PackageId) : Option Output :=
  (S.activations p.producer).bind (·.outputs[p.output]?)

/-- A package delivered by a later transfer: delivered, though born with no edge. -/
def isExplicitTransfer (p : PackageId) : Bool :=
  match S.packages p, S.output? p with
  | some r, some o => r.delivery.isSome && o.edge.isNone
  | _, _ => false

/-- A package retired by an explicit retirement. -/
def isExplicitRetirement (p : PackageId) : Bool :=
  match S.packages p with
  | some r =>
    match r.retirement? with
    | some ret => ret.reason == .explicit
    | none => false
  | none => false

def explicitTransfers : Nat := S.packageIds.countP S.isExplicitTransfer

def explicitRetirements : Nat := S.packageIds.countP S.isExplicitRetirement

end State

end Ontography
