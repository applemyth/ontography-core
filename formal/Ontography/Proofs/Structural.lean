import Ontography.Rewrite
import Ontography.Proofs.Basic

/-!
# The structural step of a rewrite

`structuralEdit?_eq_some` inverts `structuralEdit?` once into its premises, collected as
`Valid`, and its result, which is determined by the edit: the replacement is `e.apply Δ`, the
deleted nodes are the removed ones, and the fresh allocations are the added nodes and edges.
The rewrite proofs read every structural fact from this lemma.
-/

namespace Ontography.Proofs.Structural

open Common

/-- The premises `structuralEdit? Δ S e` checks (§5). -/
structure Valid (Δ : Definition) (S : State) (e : Edit) : Prop where
  removeNodes_nodup : e.removeNodes.Nodup
  removeNodes_current : ∀ v ∈ e.removeNodes, v ∈ Δ.nodes
  removeEdges_nodup : e.removeEdges.Nodup
  removeEdges_current : ∀ x ∈ e.removeEdges, x ∈ Δ.edges.map (·.id)
  no_dangling : ∀ ed ∈ Δ.edges,
    (ed.source ∈ e.removeNodes ∨ ed.target ∈ e.removeNodes) → ed.id ∈ e.removeEdges
  freshNodes : ∀ v ∈ e.add.nodes, v ∉ S.usedNodes
  freshEdges : ∀ ed ∈ e.add.edges, ed.id ∉ S.usedEdges
  definesOnlyAdded : e.DefinesOnlyAdded
  admitted : (e.apply Δ).Admitted

/-- The replacement an edit determines. -/
def replacement (Δ : Definition) (e : Edit) : Replacement :=
  ⟨e.apply Δ, e.removeNodes, e.add.nodes, e.add.edges⟩

/-- `structuralEdit?` succeeds exactly when its premises hold, and then returns the replacement
the edit determines. -/
theorem structuralEdit?_eq_some {Δ : Definition} {S : State} {e : Edit} {rep : Replacement} :
    structuralEdit? Δ S e = some rep ↔ Valid Δ S e ∧ rep = replacement Δ e := by
  simp only [structuralEdit?, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅, h₆, h₇, h₈, h₉, rfl⟩
    exact ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩, rfl⟩
  · rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩, rfl⟩
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅, h₆, h₇, h₈, h₉, rfl⟩

/-- A node of the replacement is a surviving current node or an added one. -/
theorem mem_apply_nodes {Δ : Definition} {e : Edit} {v : NodeId} :
    v ∈ (e.apply Δ).nodes ↔ (v ∈ Δ.nodes ∧ v ∉ e.removeNodes) ∨ v ∈ e.add.nodes := by
  simp [Edit.apply]

/-- An edge of the replacement is a surviving current edge or an added one. -/
theorem mem_apply_edges {Δ : Definition} {e : Edit} {ed : Edge} :
    ed ∈ (e.apply Δ).edges ↔ (ed ∈ Δ.edges ∧ ed.id ∉ e.removeEdges) ∨ ed ∈ e.add.edges := by
  simp [Edit.apply]

end Ontography.Proofs.Structural
