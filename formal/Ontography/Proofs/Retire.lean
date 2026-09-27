import Ontography.Proofs.Basic

/-!
# Explicit retirement preserves the invariants

Explicit retirement changes one record: a live package becomes
`retired ⟨.explicit, S.revision + 1, evidence⟩`, and the revision advances.
`Frame.wf_setRecord` covers everything else, so what remains is the new retirement. Its
evidence is an accepted activation, and its stamp is the new revision, which exceeds every
earlier retirement stamp and every recorded definition change (I4). The package is one more
explicit retirement (I6).
-/

namespace Ontography.Proofs

variable {Δ : Definition} {S S' : State}

namespace Frame

/-- The premises of an explicit retirement, and its successor. -/
theorem retire_eq_some {p : PackageId} {evidence : Option ActivationId}
    (h : retire S p evidence = some S') :
    ∃ r, S.packages p = some r ∧ r.status = .live ∧
      (∀ a, evidence = some a → (S.activations a).isSome) ∧
      S' = setRecord S p { r with status := .retired ⟨.explicit, S.revision + 1, evidence⟩ } := by
  simp only [retire, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨r, hr, hlive, hev, rfl⟩ := h
  refine ⟨r, hr, hlive, fun a ha => ?_, rfl⟩
  subst ha
  simpa using hev

end Frame

open Frame

-- Retirement uses no fact about `Δ`: `hΔ` is unused, and kept so that the statement is
-- exactly `Ontography.wf_retire`.
set_option linter.unusedVariables false in
/-- Explicit retirement preserves every invariant. -/
theorem wf_retire (hΔ : Δ.Admitted) (hS : WF Δ S) {p : PackageId}
    {evidence : Option ActivationId} (h : retire S p evidence = some S') : WF Δ S' := by
  obtain ⟨r, hr, hlive, hev, rfl⟩ := retire_eq_some h
  apply wf_setRecord hS hr hlive
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp
  · exact fun d => hS.delivery p r d hr
  · exact fun o e => hS.birth_edge p r o e hr
  · -- I4: the new retirement is explicit, with accepted evidence and a fresh stamp.
    intro ret hs
    cases hs
    refine ⟨by simp, by simp, fun _ => rfl, hev, Nat.le_add_left _ _, Nat.le_refl _, by simp, ?_⟩
    show _ ↔ S.revision + 1 ∉ S.changeLog
    simp only [true_iff]
    intro hmem
    have := (hS.changeLog_le _ hmem).2
    omega
  · -- I4: every earlier stamp is at most `S.revision`.
    intro ρ hs _ q s σ hq hσ _
    cases hs
    have := (hS.retirement q s σ hq hσ).2.2.2.2.2.1
    show σ.revision ≠ S.revision + 1
    omega
  · intro hs
    simp at hs
  · intro d nd hs
    simp at hs
  · -- I6: the same explicit transfers, and one more explicit retirement.
    rw [explicitTransfers_setRecord hr (by rfl),
      explicitRetirements_setRecord_succ hS hr
        (by simp [State.isExplicitRetirement, hr, PackageRecord.retirement?, hlive])
        (by simp [State.isExplicitRetirement, PackageRecord.retirement?])]
    omega

end Ontography.Proofs
