import Ontography.Invariants

/-!
# Theorems of the fixed-definition calculus

The headline results for activation, transfer, and explicit retirement. Each holds for
every validator `accepts` and every commitment function `H`.
-/

namespace Ontography

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S S' : State}

/-- The empty state of an admitted definition is well formed. -/
theorem wf_initial (hΔ : Δ.Admitted) : WF Δ (State.initial Δ) := by
  sorry

/-- Activation preserves every invariant. -/
theorem wf_activate (hΔ : Δ.Admitted) (hS : WF Δ S) {a : ActivationId} {prop : Proposal}
    (h : activate accepts H Δ S a prop = some S') : WF Δ S' := by
  sorry

/-- Transfer preserves every invariant. -/
theorem wf_transfer (hΔ : Δ.Admitted) (hS : WF Δ S) {p : PackageId} {e : EdgeId}
    {payload : Bytes} (h : transfer accepts H Δ S p e payload = some S') : WF Δ S' := by
  sorry

/-- Explicit retirement preserves every invariant. -/
theorem wf_retire (hΔ : Δ.Admitted) (hS : WF Δ S) {p : PackageId}
    {evidence : Option ActivationId} (h : retire S p evidence = some S') : WF Δ S' := by
  sorry

/-- Every transition preserves every invariant. -/
theorem wf_step (hΔ : Δ.Admitted) (hS : WF Δ S) {op : Op}
    (h : step accepts H Δ S op = some S') : WF Δ S' := by
  cases op with
  | activate a prop => exact wf_activate hΔ hS h
  | transfer p e payload => exact wf_transfer hΔ hS h
  | retire p evidence => exact wf_retire hΔ hS h

/-- Every reachable state is well formed. -/
theorem wf_of_reachable (hΔ : Δ.Admitted) (h : Reachable accepts H Δ S) : WF Δ S := by
  induction h with
  | initial => exact wf_initial hΔ
  | next op _ hstep ih => exact wf_step hΔ ih hstep

/-- Each transition advances the revision exactly once. -/
theorem step_revision {op : Op} (h : step accepts H Δ S op = some S') :
    S'.revision = S.revision + 1 := by
  sorry

/-- The causal history is acyclic, even when the workflow graph has cycles. -/
theorem causal_acyclic (hS : WF Δ S) (b : ActivationId) :
    ¬ Relation.TransGen (DependsOn S) b b := by
  sorry

end Ontography
