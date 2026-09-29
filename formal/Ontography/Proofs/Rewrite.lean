import Ontography.Proofs.RewriteLemmas

/-!
# Rewriting preserves the invariants

`rewrite_spec` states the rewrite rule exactly: the edit's admitted replacement becomes the
definition, each live package takes its own cleanup decision at the successor revision,
nothing else changes but the lifetime records and the counters, and the policy permitted the
principal the edit with exactly the retirements its cleanup makes. Each package's decision is
its own because every entry of the batch of fates is keyed by its package
(`Rewrite.lookup_fates`).

`wf_rewrite` then follows from `Rewrite.wf_cleaned`. The replacement is admitted by the rule's
own check. A kept live package keeps custody because its holder is not deleted. A removed
holder, old or new, is absent from the replacement: it is not a surviving node, and it is a
lifetime node, which no fresh node is. Structural retirements are stamped with the new
definition change and counted by it, so revision accounting holds.
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {permits : Policy} {Δ Δ' : Definition} {S S' : State}

open Common

/-- The rewrite rule, exactly (§5): the edit's admitted replacement becomes the definition;
each live package is kept or retired at the successor revision by the cleanup table; no other
record changes; the lifetime records grow by the fresh allocations; and the policy permitted
the principal the edit together with exactly the retirements the cleanup makes. -/
theorem rewrite_spec (hS : WF Δ S) {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) :
    ∃ rep, structuralEdit? Δ S req.edit = some rep ∧ Δ' = rep.next ∧
      S'.activations = S.activations ∧ S'.activationIds = S.activationIds ∧
      S'.packageIds = S.packageIds ∧ S'.usedNodes = S.usedNodes ++ rep.freshNodes ∧
      S'.edgeLog = S.edgeLog ++ rep.freshEdges ∧
      S'.changeLog = S.changeLog ++ [S.revision + 1] ∧ S'.revision = S.revision + 1 ∧
      (∀ q, S.packages q = none → S'.packages q = none) ∧
      (∀ q r, S.packages q = some r → r.status ≠ .live → S'.packages q = some r) ∧
      (∀ q r, S.packages q = some r → r.status = .live →
        ∃ fate, cleanup? accepts H Δ rep.next rep.deleted evidence r = some fate ∧
          S'.packages q = some (match fate with
            | none => r
            | some reason => { r with status := .retired ⟨reason, S.revision + 1, none⟩ })) ∧
      ∃ retired, permits req.principal Δ req.edit rep.next retired = true ∧
        ∀ q reason, (q, reason) ∈ retired ↔ ∃ r, S.packages q = some r ∧ r.status = .live ∧
          cleanup? accepts H Δ rep.next rep.deleted evidence r = some (some reason) := by
  simp only [rewrite, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rep, hrep, fates, hfates, hpermit, rfl, rfl⟩ := h
  -- Each fate is keyed by its own package.
  have hkey : ∀ p x, (match S.packages p with
      | some r =>
        if r.status = .live then
          (cleanup? accepts H Δ rep.next rep.deleted evidence r).map ((p, ·))
        else some (p, none)
      | none => some (p, none)) = some x → x.1 = p := fun p x hx => by
    split at hx
    · split at hx
      · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hx
        rfl
      · cases hx
        rfl
    · cases hx
      rfl
  have hlook := Rewrite.lookup_fates hkey hfates
  refine ⟨rep, hrep, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, _, hpermit, ?_⟩
  · -- No package is added.
    intro q hq
    dsimp only
    rw [hq]
    split <;> rfl
  · -- A package that is not live is not retired again.
    intro q r hq hst
    dsimp only
    rw [hlook q]
    simp [hq, hst]
  · -- A live package takes its own cleanup decision.
    intro q r hq hst
    have hmem : q ∈ S.packageIds := (hS.packages_dom q).1 (by simp [hq])
    obtain ⟨y, -, hy⟩ := (Activation.mapM_some hfates).1 q hmem
    simp only [hq, hst, ite_true] at hy
    obtain ⟨fate, hfate, rfl⟩ := Option.map_eq_some_iff.1 hy
    refine ⟨fate, hfate, ?_⟩
    dsimp only
    rw [hlook q, ite_eq_left hmem]
    cases fate <;> simp [hq, hst, hfate]
  · -- The policy saw exactly the retirements the cleanup makes.
    intro q reason
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨p, fate⟩, hf, reason', rfl, rfl, rfl⟩
      obtain ⟨p', -, hp'⟩ := (Activation.mapM_some hfates).2 _ hf
      obtain rfl : p' = p := (hkey p' _ hp').symm
      split at hp'
      · rename_i r hr
        split at hp'
        · rename_i hlive
          obtain ⟨c, hc, hcp⟩ := Option.map_eq_some_iff.1 hp'
          obtain ⟨-, rfl⟩ := Prod.mk.inj hcp
          exact ⟨r, hr, hlive, hc⟩
        · cases hp'
      · cases hp'
    · rintro ⟨r, hr, hlive, hc⟩
      have hmem : q ∈ S.packageIds := (hS.packages_dom q).1 (by simp [hr])
      obtain ⟨y, hy, hfy⟩ := (Activation.mapM_some hfates).1 q hmem
      simp only [hr, hlive, ite_true, hc, Option.map_some, Option.some.injEq] at hfy
      subst hfy
      exact ⟨_, hy, reason, rfl, rfl, rfl⟩

-- Rewriting uses no fact about `Δ` beyond `WF Δ S`: `hΔ` is unused, and kept so that the
-- statement is exactly `Ontography.wf_rewrite`.
set_option linter.unusedVariables false in
/-- A rewrite admits its replacement definition and preserves every invariant under it. -/
theorem wf_rewrite (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) :
    Δ'.Admitted ∧ WF Δ' S' := by
  obtain ⟨rep, hrep, rfl, hacts, hactIds, hpkgIds, hused, hlog, hchange, hrev, habsent,
    hdead, hlive, -⟩ := rewrite_spec hS h
  have hspec := Rewrite.structural_spec hrep
  exact ⟨hspec.admitted, Rewrite.wf_cleaned hS hspec hacts hactIds hpkgIds hused hlog hchange
    hrev ⟨habsent, hdead, hlive⟩⟩

end Ontography.Proofs
