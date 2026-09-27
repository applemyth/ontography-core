import Ontography.System
import Ontography.Theorems

/-!
# Theorems of the dynamic calculus

Rewrites and extensions keep the definition admitted and the state well formed, so every
running workflow reachable from an admitted definition satisfies every invariant. Each result
holds for every validator, commitment function, and grammar.
-/

namespace Ontography

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- A rewrite admits its replacement definition and preserves every invariant under it. -/
theorem wf_rewrite (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) :
    Δ'.Admitted ∧ WF Δ' S' := by
  sorry

/-- An extension admits its replacement definition and preserves every invariant under it. -/
theorem wf_extend (hΔ : Δ.Admitted) (hS : WF Δ S) {schema : Schema}
    {contracts : List Contract} (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ'.Admitted ∧ WF Δ' S' := by
  sorry

/-- Every transition of a running workflow preserves admission and every invariant. -/
theorem wf_sysStep (hΔ : Δ.Admitted) (hS : WF Δ S) {op : SysOp}
    (h : sysStep accepts H grammar Δ S op = some (Δ', S')) : Δ'.Admitted ∧ WF Δ' S' := by
  cases op with
  | step op =>
    simp only [sysStep, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨S'', hstep, rfl, rfl⟩ := h
    exact ⟨hΔ, wf_step hΔ hS hstep⟩
  | rewrite req evidence => exact wf_rewrite hΔ hS h
  | extend schema contracts => exact wf_extend hΔ hS h

/-- Every reachable running workflow is admitted and well formed. -/
theorem wf_of_sysReachable (h : SysReachable accepts H grammar Δ S) :
    Δ.Admitted ∧ WF Δ S := by
  induction h with
  | initial hΔ => exact ⟨hΔ, wf_initial hΔ⟩
  | next op _ hstep ih => exact wf_sysStep ih.1 ih.2 hstep

/-- Every transition of a running workflow advances the revision exactly once. -/
theorem sysStep_revision {op : SysOp} (h : sysStep accepts H grammar Δ S op = some (Δ', S')) :
    S'.revision = S.revision + 1 := by
  sorry

end Ontography
