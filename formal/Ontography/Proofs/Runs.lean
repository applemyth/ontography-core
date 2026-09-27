import Ontography.SystemTheorems
import Ontography.Runs

/-!
# Runs (T6)

A run extends one transition at a time, so each fact about runs is an invariant proved by
induction over the run. Every transition keeps the definition admitted and the state well
formed (`wf_sysStep`), which the frame theorem needs, so the induction carries both.

An accepted activation persists by the frame. An identity that has left the definition stays
a lifetime identity, since the lifetime records only grow, and freshness admits to the next
definition only current identities and ones never used, so it stays out.
-/

namespace Ontography.Proofs.Runs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- Induction over a run: a property that every transition from a well-formed state preserves
holds at the end of a run from an admitted, well-formed workflow where it holds, as do
admission and well-formedness. -/
theorem sysSteps_invariant {P : Definition → State → Prop} (hΔ : Δ.Admitted) (hS : WF Δ S)
    (hP : P Δ S)
    (hstep : ∀ {Δ₁ Δ₂ : Definition} {S₁ S₂ : State} {op : SysOp}, WF Δ₁ S₁ → P Δ₁ S₁ →
      sysStep accepts H grammar Δ₁ S₁ op = some (Δ₂, S₂) → P Δ₂ S₂)
    (h : SysSteps accepts H grammar Δ S Δ' S') : Δ'.Admitted ∧ WF Δ' S' ∧ P Δ' S' := by
  induction h with
  | refl => exact ⟨hΔ, hS, hP⟩
  | tail _ _ hop ih =>
    obtain ⟨hΔ₁, hS₁, hP₁⟩ := ih hS hP
    obtain ⟨hΔ₂, hS₂⟩ := Ontography.wf_sysStep hΔ₁ hS₁ hop
    exact ⟨hΔ₂, hS₂, hstep hS₁ hP₁ hop⟩

end Ontography.Proofs.Runs

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- An accepted activation is never replaced, so no activation identity is accepted twice. -/
theorem activation_persists (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {a : ActivationId} {act : Activation}
    (ha : S.activations a = some act) : S'.activations a = some act :=
  (Runs.sysSteps_invariant (P := fun _ S₁ => S₁.activations a = some act) hΔ hS ha
    (fun hS₁ ha₁ hop => (Ontography.sysStep_frame hS₁ hop).activations a act ha₁) h).2.2

/-- A node identity that has left the definition never returns to it. -/
theorem removed_node_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {v : NodeId} (hused : v ∈ S.usedNodes)
    (hgone : v ∉ Δ.nodes) : v ∉ Δ'.nodes :=
  (Runs.sysSteps_invariant (P := fun Δ₁ S₁ => v ∈ S₁.usedNodes ∧ v ∉ Δ₁.nodes) hΔ hS
    ⟨hused, hgone⟩
    (fun hS₁ ⟨hused₁, hgone₁⟩ hop =>
      -- `v` stays used, and freshness admits only current or unused nodes.
      ⟨(Ontography.sysStep_frame hS₁ hop).usedNodes hused₁, fun hv =>
        ((Ontography.sysStep_fresh hop).1 v hv).elim hgone₁ (· hused₁)⟩) h).2.2.2

/-- An edge identity that has left the definition never returns to it. -/
theorem removed_edge_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {e : EdgeId} (hused : e ∈ S.usedEdges)
    (hgone : e ∉ Δ.edges.map (·.id)) : e ∉ Δ'.edges.map (·.id) := by
  refine (Runs.sysSteps_invariant
    (P := fun Δ₁ S₁ => e ∈ S₁.usedEdges ∧ e ∉ Δ₁.edges.map (·.id)) hΔ hS ⟨hused, hgone⟩
    (fun hS₁ ⟨hused₁, hgone₁⟩ hop => ⟨?_, ?_⟩) h).2.2.2
  · -- The edge log only grows, so `e` stays used.
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hused₁
    exact List.mem_map_of_mem ((Ontography.sysStep_frame hS₁ hop).edgeLog hx)
  · -- Freshness admits only current edges or ones with unused identities.
    intro he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    rcases (Ontography.sysStep_fresh hop).2 x hx with hx₁ | hfresh
    · exact hgone₁ (List.mem_map_of_mem hx₁)
    · exact hfresh hused₁

end Ontography.Proofs
