import Ontography.SystemTheorems
import Ontography.Proofs.CommutationLemmas

/-!
# Locality and commutation of rewrites (T4)

Both theorems rest on `rewrite_spec`: a rewrite replaces the definition by its edit's
replacement, keeps every record that is not live, and decides each live one by `cleanup?`
alone.

Locality is `Commute.cleanup_keep`: cleanup keeps a package whose holder the rewrite does not
affect, since the holder survives, keeps its outgoing edges and its definition, and, as an
`All` receiver, keeps the incoming edge its receipt names.

Both orders of two rewrites end in the same definition (`Commute.definitions_commute`). Each
request carries the same edit in both orders, and its replacement is `Edit.apply` of that
edit. An edit applied to `Δ` removes only identities of `Δ`, which are lifetime identities,
and adds only identities unused before it. So neither edit removes what the other adds, and
either order removes both removed parts and adds both added parts (`Commute.apply_comm`).

For the packages, fix a live package with holder `h`. Disjointness leaves some rewrite that
affects `h` in neither order, and by symmetry it is the second one, `ρ₂`. In the order
`ρ₁ ρ₂`, `ρ₁` decides the fate at `Δ ⟶ Δ₁` and `ρ₂` keeps what `ρ₁` kept; in the order
`ρ₂ ρ₁`, `ρ₂` keeps the package and `ρ₁` decides at `Δ₂ ⟶ Δ₂₁`. The two decisions agree by
`Commute.cleanup_eq`, and the retirements they make differ only in their stamps.
-/

namespace Ontography.Proofs

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {permits : Policy} {Δ Δ' : Definition} {S S' : State}

namespace Commute

/-- A rewrite records no new package. -/
theorem rewrite_none (hS : WF Δ S) {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) {q : PackageId}
    (hq : S.packages q = none) : S'.packages q = none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnone, -⟩ := rewrite_spec hS h
  exact hnone q hq

/-- A rewrite keeps every record that is not live. -/
theorem rewrite_not_live (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) {q : PackageId}
    {r : PackageRecord} (hr : S.packages q = some r) (hlive : r.status ≠ .live) :
    S'.packages q = some r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnl, -⟩ := rewrite_spec hS h
  exact hnl q r hr hlive

/-- A rewrite keeps a live package whose holder it does not affect. -/
theorem rewrite_keep (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) {q : PackageId}
    {r : PackageRecord} (hr : S.packages q = some r) (hlive : r.status = .live)
    (hna : ¬ Affected Δ Δ' r.holder) : S'.packages q = some r := by
  obtain ⟨rep, hrep, rfl, -, -, -, -, -, -, -, -, -, hl, -⟩ := rewrite_spec hS h
  obtain ⟨fate, hfate, hq⟩ := hl q r hr hlive
  rw [cleanup_keep hΔ hS (shape hrep) hr hlive hna, Option.some.injEq] at hfate
  subst hfate
  exact hq

/-- Commutation at one live package whose holder `ρ₂` affects in neither order. -/
theorem commute_live (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H permits Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H permits Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H permits Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H permits Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁))
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
  -- `ρ₁` applies one edit in both orders.
  obtain ⟨rep₁, hrep₁, rfl, -, -, -, -, -, -, -, -, -, hl₁, -⟩ := rewrite_spec hS h₁
  obtain ⟨rep₂₁, hrep₂₁, rfl, -, -, -, -, -, -, -, -, -, hl₂₁, -⟩ := rewrite_spec hS₂ h₂₁
  obtain ⟨rep₁₂, hrep₁₂, rfl, -, -, -, -, -, -, -, -, hnl₁₂, -⟩ := rewrite_spec hS₁ h₁₂
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

/-- Rewrites whose affected holders are disjoint across both orders commute on every package
record, up to retirement stamps, when both orders apply and yield the same definition. -/
theorem packages_commute (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H permits Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H permits Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H permits Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H permits Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁))
    (hsame : Δ₁₂.Equiv Δ₂₁)
    (hdisjoint : ∀ v, Affected Δ Δ₁ v ∨ Affected Δ₂ Δ₂₁ v →
      ¬ (Affected Δ Δ₂ v ∨ Affected Δ₁ Δ₁₂ v)) (q : PackageId) :
    (S₁₂.packages q).map PackageRecord.unstamped =
      (S₂₁.packages q).map PackageRecord.unstamped := by
  obtain ⟨-, hS₁⟩ := wf_rewrite hΔ hS h₁
  obtain ⟨-, hS₂⟩ := wf_rewrite hΔ hS h₂
  cases hq : S.packages q with
  | none =>
    rw [rewrite_none hS₁ h₁₂ (rewrite_none hS h₁ hq), rewrite_none hS₂ h₂₁ (rewrite_none hS h₂ hq)]
  | some r =>
    by_cases hlive : r.status = .live
    · by_cases h₁a : Affected Δ Δ₁ r.holder ∨ Affected Δ₂ Δ₂₁ r.holder
      · -- `ρ₁` affects the holder, so `ρ₂` affects it in neither order.
        have h₂a := hdisjoint _ h₁a
        exact commute_live hΔ hS h₁ h₁₂ h₂ h₂₁ hsame hq hlive
          (fun h => h₂a (.inl h)) (fun h => h₂a (.inr h))
      · -- `ρ₁` affects the holder in neither order.
        exact (commute_live hΔ hS h₂ h₂₁ h₁ h₁₂ (Equiv.symm hsame) hq hlive
          (fun h => h₁a (.inl h)) (fun h => h₁a (.inr h))).symm
    · rw [rewrite_not_live hS₁ h₁₂ (rewrite_not_live hS h₁ hq hlive) hlive,
        rewrite_not_live hS₂ h₂₁ (rewrite_not_live hS h₂ hq hlive) hlive]

/-- Both orders of two rewrites yield the same definition. Applied to `Δ`, each edit removes
only identities of `Δ` and allocates only identities `S` has never used, and `S` has used
every identity of `Δ`, so neither removes what the other adds. -/
theorem definitions_commute (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H permits Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H permits Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H permits Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H permits Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁)) :
    Δ₁₂.Equiv Δ₂₁ := by
  obtain ⟨-, hS₁⟩ := wf_rewrite hΔ hS h₁
  obtain ⟨-, hS₂⟩ := wf_rewrite hΔ hS h₂
  obtain ⟨rep₁, hrep₁, rfl, -⟩ := rewrite_spec hS h₁
  obtain ⟨rep₂, hrep₂, rfl, -⟩ := rewrite_spec hS h₂
  obtain ⟨rep₁₂, hrep₁₂, rfl, -⟩ := rewrite_spec hS₁ h₁₂
  obtain ⟨rep₂₁, hrep₂₁, rfl, -⟩ := rewrite_spec hS₂ h₂₁
  -- Each order applies the same two edits.
  obtain ⟨hv₁, rfl⟩ := Structural.structuralEdit?_eq_some.1 hrep₁
  obtain ⟨hv₂, rfl⟩ := Structural.structuralEdit?_eq_some.1 hrep₂
  obtain ⟨-, rfl⟩ := Structural.structuralEdit?_eq_some.1 hrep₁₂
  obtain ⟨-, rfl⟩ := Structural.structuralEdit?_eq_some.1 hrep₂₁
  -- The identities of `Δ` are lifetime identities, which neither edit allocates.
  have hedges : ∀ x ∈ Δ.edges.map (·.id), x ∈ S.usedEdges := fun x hx => by
    obtain ⟨ed, hed, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map_of_mem (hS.edge_log hed)
  exact apply_comm hv₁.definesOnlyAdded hv₂.definesOnlyAdded
    (fun v hv hd => hv₁.freshNodes v hv (hS.used_nodes (hv₂.removeNodes_current v hd)))
    (fun v hv hd => hv₂.freshNodes v hv (hS.used_nodes (hv₁.removeNodes_current v hd)))
    (fun ed hed hd => hv₁.freshEdges ed hed (hedges _ (hv₂.removeEdges_current _ hd)))
    (fun ed hed hd => hv₂.freshEdges ed hed (hedges _ (hv₁.removeEdges_current _ hd)))

end Commute

/-- Locality: a rewrite changes only live packages whose holder it affects. -/
theorem rewrite_local (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S'))
    {q : PackageId} {r r' : PackageRecord} (hr : S.packages q = some r)
    (hr' : S'.packages q = some r') (hchanged : r' ≠ r) :
    r.status = .live ∧ Affected Δ Δ' r.holder := by
  have hlive : r.status = .live := Classical.byContradiction fun hne => by
    rw [Commute.rewrite_not_live hS h hr hne, Option.some.injEq] at hr'
    exact hchanged hr'.symm
  refine ⟨hlive, Classical.byContradiction fun hna => ?_⟩
  rw [Commute.rewrite_keep hΔ hS h hr hlive hna, Option.some.injEq] at hr'
  exact hchanged hr'.symm

/-- T4: when both orders of two rewrites apply, they yield the same definition; and if their
affected holders are disjoint across both orders, they also commute on every package record,
up to retirement stamps. -/
theorem rewrite_commute (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H permits Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H permits Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H permits Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H permits Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁)) :
    Δ₁₂.Equiv Δ₂₁ ∧
      ((∀ v, Affected Δ Δ₁ v ∨ Affected Δ₂ Δ₂₁ v → ¬ (Affected Δ Δ₂ v ∨ Affected Δ₁ Δ₁₂ v)) →
        ∀ q, (S₁₂.packages q).map PackageRecord.unstamped =
          (S₂₁.packages q).map PackageRecord.unstamped) :=
  have hsame := Commute.definitions_commute hΔ hS h₁ h₁₂ h₂ h₂₁
  ⟨hsame, Commute.packages_commute hΔ hS h₁ h₁₂ h₂ h₂₁ hsame⟩

end

end Ontography.Proofs
