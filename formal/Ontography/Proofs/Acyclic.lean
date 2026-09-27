import Ontography.Invariants

/-!
# The causal history is acyclic

`WF.causal_order` places every producer strictly before each consumer of its outputs in
acceptance order. Following consumption backwards therefore strictly decreases the position
in `activationIds`, so no chain of consumptions returns to where it started, whatever cycles
the workflow graph has.
-/

namespace Ontography.Proofs

variable {Δ : Definition} {S : State}

namespace Frame

/-- A causal ancestor was accepted strictly before its descendant. -/
theorem idxOf_lt_of_transGen (hS : WF Δ S) {b a : ActivationId}
    (h : Relation.TransGen (DependsOn S) b a) :
    S.activationIds.idxOf a < S.activationIds.idxOf b := by
  induction h with
  | single hd =>
    obtain ⟨p, r, rfl, hp, hs⟩ := hd
    exact hS.causal_order p r _ hp hs
  | tail _ hd ih =>
    obtain ⟨p, r, rfl, hp, hs⟩ := hd
    exact Nat.lt_trans (hS.causal_order p r _ hp hs) ih

end Frame

/-- The causal history is acyclic, even when the workflow graph has cycles. -/
theorem causal_acyclic (hS : WF Δ S) (b : ActivationId) :
    ¬ Relation.TransGen (DependsOn S) b b :=
  fun h => Nat.lt_irrefl _ (Frame.idxOf_lt_of_transGen hS h)

end Ontography.Proofs
