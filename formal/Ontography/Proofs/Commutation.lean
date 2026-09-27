import Ontography.SystemTheorems
import Ontography.Proofs.CommutationLemmas

/-!
# Locality and commutation of rewrites (T4)

Both theorems rest on `rewrite_spec`: a rewrite keeps every record that is not live and
decides each live one by `cleanup?` alone.

Locality is `Commute.cleanup_keep`: cleanup keeps a package whose holder the rewrite does not
affect, since the holder survives, keeps its outgoing edges and its definition, and, as an
`All` receiver, keeps the incoming edge its receipt names.

For commutation, fix a live package with holder `h`. Disjointness leaves some rewrite that
affects `h` in neither order, and by symmetry it is the second one, `ρ₂`. In the order
`ρ₁ ρ₂`, `ρ₁` decides the fate at `Δ ⟶ Δ₁` and `ρ₂` keeps what `ρ₁` kept; in the order
`ρ₂ ρ₁`, `ρ₂` keeps the package and `ρ₁` decides at `Δ₂ ⟶ Δ₂₁`. The two decisions agree by
`Commute.cleanup_eq`, and the retirements they make differ only in their stamps.
-/

namespace Ontography.Proofs

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

namespace Commute

/-- A rewrite records no new package. -/
theorem rewrite_none (hS : WF Δ S) {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) {q : PackageId}
    (hq : S.packages q = none) : S'.packages q = none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnone, -, -⟩ := rewrite_spec hS h
  exact hnone q hq

/-- A rewrite keeps every record that is not live. -/
theorem rewrite_not_live (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) {q : PackageId}
    {r : PackageRecord} (hr : S.packages q = some r) (hlive : r.status ≠ .live) :
    S'.packages q = some r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hnl, -⟩ := rewrite_spec hS h
  exact hnl q r hr hlive

/-- A rewrite keeps a live package whose holder it does not affect. -/
theorem rewrite_keep (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) {q : PackageId}
    {r : PackageRecord} (hr : S.packages q = some r) (hlive : r.status = .live)
    (hna : ¬ Affected Δ Δ' r.holder) : S'.packages q = some r := by
  obtain ⟨pr, rep, -, hrep, rfl, -, -, -, -, -, -, -, -, -, hl⟩ := rewrite_spec hS h
  obtain ⟨fate, hfate, hq⟩ := hl q r hr hlive
  rw [cleanup_keep hΔ hS (shape hrep) hr hlive hna, Option.some.injEq] at hfate
  subst hfate
  exact hq

/-- Commutation at one live package whose holder `ρ₂` affects in neither order. -/
theorem commute_live (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H grammar Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H grammar Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H grammar Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H grammar Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁))
    (hsame : Δ₁₂.Equiv Δ₂₁) {q : PackageId} {r : PackageRecord} (hr : S.packages q = some r)
    (hlive : r.status = .live) (hna₂ : ¬ Affected Δ Δ₂ r.holder)
    (hna₁₂ : ¬ Affected Δ₁ Δ₁₂ r.holder) :
    (S₁₂.packages q).map PackageRecord.unstamped =
      (S₂₁.packages q).map PackageRecord.unstamped := by
  obtain ⟨hΔ₁, hS₁⟩ := wf_rewrite hΔ hS h₁
  obtain ⟨-, hS₂⟩ := wf_rewrite hΔ hS h₂
  have hv := hS.custody q r hr hlive
  -- `ρ₂` keeps the package at `Δ ⟶ Δ₂`.
  have hq₂ := rewrite_keep hΔ hS h₂ hr hlive hna₂
  -- `ρ₁` is one production at one match in both orders.
  obtain ⟨pr₁, rep₁, hpr₁, hrep₁, rfl, -, -, -, -, -, -, -, -, -, hl₁⟩ := rewrite_spec hS h₁
  obtain ⟨pr₁', rep₂₁, hpr₁', hrep₂₁, rfl, -, -, -, -, -, -, -, -, -, hl₂₁⟩ :=
    rewrite_spec hS₂ h₂₁
  rw [hpr₁, Option.some.injEq] at hpr₁'
  subst hpr₁'
  obtain ⟨pr₂, rep₁₂, -, hrep₁₂, rfl, -, -, -, -, -, -, -, -, hnl₁₂, -⟩ := rewrite_spec hS₁ h₁₂
  -- `ρ₁` decides the same fate at `Δ ⟶ Δ₁` and at `Δ₂ ⟶ Δ₂₁`.
  have heq := cleanup_eq (accepts := accepts) (H := H) (evidence := evidence) hS (shape hrep₁)
    (shape hrep₂₁) hS₁ (shape hrep₁₂) hsame hv (not_affected hv hna₂).2.1 hna₁₂
  obtain ⟨fate, hfate, hq₁⟩ := hl₁ q r hr hlive
  obtain ⟨fate', hfate', hq₂₁⟩ := hl₂₁ q r hq₂ hlive
  rw [hfate, hfate', Option.some.injEq] at heq
  subst heq
  cases fate with
  | none =>
    -- Kept by `ρ₁`, and then by `ρ₂` at `Δ₁ ⟶ Δ₁₂`.
    rw [rewrite_keep hΔ₁ hS₁ h₁₂ hq₁ hlive hna₁₂, hq₂₁]
  | some reason =>
    -- Retired by `ρ₁` in both orders, at different revisions.
    rw [hnl₁₂ q _ hq₁ (by simp), hq₂₁]
    simp [PackageRecord.unstamped]

end Commute

/-- Locality: a rewrite changes only live packages whose holder it affects. -/
theorem rewrite_local (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S'))
    {q : PackageId} {r r' : PackageRecord} (hr : S.packages q = some r)
    (hr' : S'.packages q = some r') (hchanged : r' ≠ r) :
    r.status = .live ∧ Affected Δ Δ' r.holder := by
  have hlive : r.status = .live := Classical.byContradiction fun hne => by
    rw [Commute.rewrite_not_live hS h hr hne, Option.some.injEq] at hr'
    exact hchanged hr'.symm
  refine ⟨hlive, Classical.byContradiction fun hna => ?_⟩
  rw [Commute.rewrite_keep hΔ hS h hr hlive hna, Option.some.injEq] at hr'
  exact hchanged hr'.symm

/-- T4: rewrites whose affected holders are disjoint across both orders commute on every
package record, up to retirement stamps, when both orders apply and yield the same
definition. -/
theorem rewrite_commute (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H grammar Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H grammar Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H grammar Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H grammar Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁))
    (hsame : Δ₁₂.Equiv Δ₂₁)
    (hdisjoint : ∀ v, Affected Δ Δ₁ v ∨ Affected Δ₂ Δ₂₁ v →
      ¬ (Affected Δ Δ₂ v ∨ Affected Δ₁ Δ₁₂ v)) (q : PackageId) :
    (S₁₂.packages q).map PackageRecord.unstamped =
      (S₂₁.packages q).map PackageRecord.unstamped := by
  obtain ⟨-, hS₁⟩ := wf_rewrite hΔ hS h₁
  obtain ⟨-, hS₂⟩ := wf_rewrite hΔ hS h₂
  cases hq : S.packages q with
  | none =>
    rw [Commute.rewrite_none hS₁ h₁₂ (Commute.rewrite_none hS h₁ hq),
      Commute.rewrite_none hS₂ h₂₁ (Commute.rewrite_none hS h₂ hq)]
  | some r =>
    by_cases hlive : r.status = .live
    · by_cases h₁a : Affected Δ Δ₁ r.holder ∨ Affected Δ₂ Δ₂₁ r.holder
      · -- `ρ₁` affects the holder, so `ρ₂` affects it in neither order.
        have h₂a := hdisjoint _ h₁a
        exact Commute.commute_live hΔ hS h₁ h₁₂ h₂ h₂₁ hsame hq hlive
          (fun h => h₂a (.inl h)) (fun h => h₂a (.inr h))
      · -- `ρ₁` affects the holder in neither order.
        exact (Commute.commute_live hΔ hS h₂ h₂₁ h₁ h₁₂ (Commute.Equiv.symm hsame) hq hlive
          (fun h => h₁a (.inl h)) (fun h => h₁a (.inr h))).symm
    · rw [Commute.rewrite_not_live hS₁ h₁₂ (Commute.rewrite_not_live hS h₁ hq hlive) hlive,
        Commute.rewrite_not_live hS₂ h₂₁ (Commute.rewrite_not_live hS h₂ hq hlive) hlive]

end

end Ontography.Proofs
