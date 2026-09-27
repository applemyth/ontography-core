import Ontography.Proofs.Basic

/-!
# Transfer preserves the invariants

Transfer changes one record: a live package with no delivery gains the delivery `⟨e, t(e)⟩`,
and the revision advances. `Common.wf_setRecord` covers everything else, so what remains is the
new delivery. It is an admitted edge leaving the producer's node (I3); its receiver is a node
and the edge is incoming to it (I5); and since the package's output had no birth edge, the
package is one more explicit transfer (I6).
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S S' : State}

namespace Common

/-- The premises of a transfer the invariants rely on, and its successor. -/
theorem transfer_eq_some {p : PackageId} {e : EdgeId} {payload : Bytes}
    (h : transfer accepts H Δ S p e payload = some S') :
    ∃ r edge, S.packages p = some r ∧ r.status = .live ∧ r.delivery = none ∧
      Δ.edge? e = some edge ∧ edge.source = r.producerNode ∧
      S' = setRecord S p { r with delivery := some ⟨e, edge.target⟩ } := by
  simp only [transfer, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨r, hr, hlive, hnone, edge, hedge, hsrc, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact ⟨r, edge, hr, hlive, hnone, hedge, hsrc, rfl⟩

end Common

open Common

/-- Transfer preserves every invariant. -/
theorem wf_transfer (hΔ : Δ.Admitted) (hS : WF Δ S) {p : PackageId} {e : EdgeId}
    {payload : Bytes} (h : transfer accepts H Δ S p e payload = some S') : WF Δ S' := by
  obtain ⟨r, edge, hr, hlive, hnone, hedge, hsrc, rfl⟩ := transfer_eq_some h
  obtain ⟨hmem, rfl⟩ := edge?_mem hedge
  -- The package's output names no birth edge, or the package would already be delivered.
  obtain ⟨act, o, hact, ho, -⟩ := hS.ownership p r hr
  have hout : S.output? p = some o := by simp [State.output?, hact, ho]
  have hborn : o.edge = none := by
    cases he : o.edge with
    | none => rfl
    | some e' =>
      obtain ⟨v, hv⟩ := hS.birth_edge p r o e' hr hout he
      simp [hnone] at hv
  apply wf_setRecord hS hr hlive
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp [hlive]
  · -- I3: the new delivery is an admitted edge from the producer's node.
    intro d hd
    cases hd
    rw [← hsrc]
    exact hS.edge_log hmem
  · -- I3: the output names no birth edge.
    intro o' e' ho' he'
    rw [hout] at ho'
    cases ho'
    simp [hborn] at he'
  · intro ret hs
    simp [hlive] at hs
  · intro ρ hs
    simp [hlive] at hs
  · -- I5: the receiver is the edge's target, a node.
    intro _
    exact (hΔ.endpoints edge hmem).2
  · -- I5: the delivery edge is incoming to its receiver.
    intro d nd _ hd _ _
    cases hd
    exact mem_incoming.2 ⟨edge, hmem, rfl, rfl⟩
  · -- I6: one more explicit transfer, and the same explicit retirements.
    rw [explicitTransfers_setRecord_succ hS hr (by simp [State.isExplicitTransfer, hr, hout, hnone])
        (by simp [State.isExplicitTransfer, hout, hborn]),
      explicitRetirements_setRecord hr (by rfl)]
    omega

end Ontography.Proofs
