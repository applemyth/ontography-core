import Ontography.Basic

/-!
# Admitted definitions

A definition `Δ` bundles the schema `Σ = (N, O, U)`, the contract registry, the
topology `G = (V, E, s, t)`, the node and edge annotations, the root policy `ρ`,
and the authority-transition policy `T` (MATHEMATICAL_DEFINITION §1).

Validators are not data. The rules take them as a parameter
`accepts : ContractId → Bytes → Bool`, so every theorem holds for every
validator, and a contract here records only its identity and object type. A
contract identity names one predicate for the model's whole lifetime, which is
what the kernel's shared-validator requirement enforces.

`Admitted` is the conjunction of the checks `Kernel::admit`, `Graph::new`, and
the annotation constructors perform.
-/

namespace Ontography

inductive Ingress where
  | any
  | all
  deriving DecidableEq, Repr

inductive AuthorityMatch where
  | anyOf
  | allOf
  deriving DecidableEq, Repr

structure Schema where
  nodeTypes : List NodeType
  objectTypes : List ObjectType
  tags : List Tag
  deriving DecidableEq, Repr

structure Contract where
  id : ContractId
  objectType : ObjectType
  deriving DecidableEq, Repr

structure Edge where
  id : EdgeId
  source : NodeId
  target : NodeId
  deriving DecidableEq, Repr

structure NodeDef where
  node : NodeId
  types : List NodeType
  resultContract : ContractId
  ingress : Ingress
  deriving DecidableEq, Repr

structure EdgeDef where
  edge : EdgeId
  types : List String
  sourceRequirements : List NodeType
  targetRequirements : List NodeType
  packageContract : ContractId
  tags : List Tag
  authorityMatch : AuthorityMatch
  deriving DecidableEq, Repr

/-- `(node, source, target) ∈ T`. -/
structure TransitionRule where
  node : NodeId
  source : Authority
  target : Authority
  deriving DecidableEq, Repr

/-- `ρ(node) = ceiling`. -/
structure RootRule where
  node : NodeId
  ceiling : Authority
  deriving DecidableEq, Repr

structure Definition where
  schema : Schema
  contracts : List Contract
  nodes : List NodeId
  edges : List Edge
  nodeDefs : List NodeDef
  edgeDefs : List EdgeDef
  transitions : List TransitionRule
  roots : List RootRule
  deriving DecidableEq, Repr

namespace EdgeDef

/-- `allows(e, β)`: `tags_e ∩ β ≠ ∅` for `AnyOf`, `tags_e ⊆ β` for `AllOf`. -/
def Allows (d : EdgeDef) (β : Authority) : Prop :=
  match d.authorityMatch with
  | .anyOf => ∃ t ∈ d.tags, t ∈ β
  | .allOf => d.tags ⊆ β

instance (d : EdgeDef) (β : Authority) : Decidable (d.Allows β) := by
  unfold Allows; split <;> infer_instance

end EdgeDef

namespace Definition

variable (Δ : Definition)

def edge? (e : EdgeId) : Option Edge := Δ.edges.find? (·.id == e)

def nodeDef? (v : NodeId) : Option NodeDef := Δ.nodeDefs.find? (·.node == v)

def edgeDef? (e : EdgeId) : Option EdgeDef := Δ.edgeDefs.find? (·.edge == e)

def contract? (c : ContractId) : Option Contract := Δ.contracts.find? (·.id == c)

/-- `ρ(v)`, when `v ∈ dom(ρ)`. -/
def ceiling? (v : NodeId) : Option Authority := (Δ.roots.find? (·.node == v)).map (·.ceiling)

/-- `incoming_Δ(v) = {e ∈ E | t(e) = v}`. -/
def incoming (v : NodeId) : List EdgeId := (Δ.edges.filter (·.target == v)).map (·.id)

/-- `(v, α, β) ∈ T`, comparing authorities as sets. -/
def AllowsTransition (v : NodeId) (α β : Authority) : Prop :=
  ∃ r ∈ Δ.transitions, r.node = v ∧ SetEq r.source α ∧ SetEq r.target β

instance (v : NodeId) (α β : Authority) : Decidable (Δ.AllowsTransition v α β) := by
  unfold AllowsTransition; infer_instance

/-- An admitted definition (MATHEMATICAL_DEFINITION §1). -/
structure Admitted : Prop where
  /-- Node identities are nonempty and unique. -/
  nodes_nonempty : ∀ v ∈ Δ.nodes, v ≠ ""
  nodes_nodup : Δ.nodes.Nodup
  /-- Edge identities are nonempty and unique, and every endpoint is a node. -/
  edges_nonempty : ∀ e ∈ Δ.edges, e.id ≠ ""
  edges_nodup : (Δ.edges.map (·.id)).Nodup
  endpoints : ∀ e ∈ Δ.edges, e.source ∈ Δ.nodes ∧ e.target ∈ Δ.nodes
  /-- The schema's closed vocabularies have nonempty entries. -/
  vocabulary_nonempty :
    (∀ t ∈ Δ.schema.nodeTypes, t ≠ "") ∧ (∀ o ∈ Δ.schema.objectTypes, o ≠ "") ∧
      ∀ t ∈ Δ.schema.tags, t ≠ ""
  /-- Contract identities are nonempty and unique; object types are in `O`. -/
  contracts_nodup : (Δ.contracts.map (·.id)).Nodup
  contracts_wf : ∀ c ∈ Δ.contracts, c.id ≠ "" ∧ c.objectType ∈ Δ.schema.objectTypes
  /-- Every node has exactly one definition, and every definition names a node. -/
  nodeDefs_nodup : (Δ.nodeDefs.map (·.node)).Nodup
  nodeDefs_nodes : ∀ d ∈ Δ.nodeDefs, d.node ∈ Δ.nodes
  nodes_defined : ∀ v ∈ Δ.nodes, ∃ d ∈ Δ.nodeDefs, d.node = v
  /-- `∅ ≠ types_v ⊆ N` and `result_contract_v ∈ dom(C)`. -/
  nodeDefs_wf : ∀ d ∈ Δ.nodeDefs,
    d.types ≠ [] ∧ d.types ⊆ Δ.schema.nodeTypes ∧ ∃ c ∈ Δ.contracts, c.id = d.resultContract
  /-- Every edge has exactly one definition, and every definition names an edge. -/
  edgeDefs_nodup : (Δ.edgeDefs.map (·.edge)).Nodup
  edgeDefs_edges : ∀ d ∈ Δ.edgeDefs, ∃ e ∈ Δ.edges, e.id = d.edge
  edges_defined : ∀ e ∈ Δ.edges, ∃ d ∈ Δ.edgeDefs, d.edge = e.id
  /-- Nonempty labels, `∅ ≠ tags_e ⊆ U`, and `package_contract_e ∈ dom(C)`. -/
  edgeDefs_wf : ∀ d ∈ Δ.edgeDefs,
    d.types ≠ [] ∧ (∀ t ∈ d.types, t ≠ "") ∧ d.tags ≠ [] ∧ d.tags ⊆ Δ.schema.tags ∧
      ∃ c ∈ Δ.contracts, c.id = d.packageContract
  /-- Endpoint requirements are among the endpoints' node types. -/
  requirements : ∀ e ∈ Δ.edges, ∀ d ∈ Δ.edgeDefs, d.edge = e.id →
    ∀ s ∈ Δ.nodeDefs, s.node = e.source → ∀ t ∈ Δ.nodeDefs, t.node = e.target →
      d.sourceRequirements ⊆ s.types ∧ d.targetRequirements ⊆ t.types
  /-- `T ⊆ V × P(U) × P(U)`. -/
  transitions_wf : ∀ r ∈ Δ.transitions,
    r.node ∈ Δ.nodes ∧ r.source ⊆ Δ.schema.tags ∧ r.target ⊆ Δ.schema.tags
  /-- `ρ : V ⇀ P(U)`. -/
  roots_nodup : (Δ.roots.map (·.node)).Nodup
  roots_wf : ∀ r ∈ Δ.roots, r.node ∈ Δ.nodes ∧ r.ceiling ⊆ Δ.schema.tags

end Definition

end Ontography
