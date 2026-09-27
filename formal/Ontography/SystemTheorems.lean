import Ontography.System
import Ontography.Theorems
import Ontography.Proofs.Extension
import Ontography.Proofs.System
import Ontography.Proofs.Rewrite

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
    Δ'.Admitted ∧ WF Δ' S' :=
  Proofs.wf_rewrite hΔ hS h

/-- An extension admits its replacement definition and preserves every invariant under it. -/
theorem wf_extend (hΔ : Δ.Admitted) (hS : WF Δ S) {schema : Schema}
    {contracts : List Contract} (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ'.Admitted ∧ WF Δ' S' :=
  Proofs.wf_extend hΔ hS h

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
    S'.revision = S.revision + 1 :=
  Proofs.sysStep_revision h

/-- Rewrites and extensions change no accepted activation, no package's immutable facts, no
delivery once made, and no status once no longer live; lifetime records only grow. -/
theorem sysStep_frame (hS : WF Δ S) {op : SysOp}
    (h : sysStep accepts H grammar Δ S op = some (Δ', S')) : Frame S S' :=
  Proofs.sysStep_frame hS h

/-- T6 Freshness: a new definition's nodes and edges are current ones or identities never
used before, so a deleted identity never returns. -/
theorem sysStep_fresh {op : SysOp} (h : sysStep accepts H grammar Δ S op = some (Δ', S')) :
    (∀ v ∈ Δ'.nodes, v ∈ Δ.nodes ∨ v ∉ S.usedNodes) ∧
      ∀ e ∈ Δ'.edges, e ∈ Δ.edges ∨ e.id ∉ S.usedEdges :=
  Proofs.sysStep_fresh h

/-- The rewrite rule, exactly (§5): the registered production's admitted replacement becomes
the definition; each live package is kept or retired at the successor revision by the cleanup
table; no other record changes; and the lifetime records grow by the fresh allocations. -/
theorem rewrite_spec (hS : WF Δ S) {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) :
    ∃ pr rep, grammar.find? (·.id == req.production) = some pr ∧
      structural? Δ S pr req.matching = some rep ∧ Δ' = rep.next ∧
      S'.activations = S.activations ∧ S'.activationIds = S.activationIds ∧
      S'.packageIds = S.packageIds ∧ S'.usedNodes = S.usedNodes ++ rep.freshNodes ∧
      S'.edgeLog = S.edgeLog ++ rep.freshEdges ∧
      S'.changeLog = S.changeLog ++ [S.revision + 1] ∧ S'.revision = S.revision + 1 ∧
      (∀ q, S.packages q = none → S'.packages q = none) ∧
      (∀ q r, S.packages q = some r → r.status ≠ .live → S'.packages q = some r) ∧
      ∀ q r, S.packages q = some r → r.status = .live →
        ∃ fate, cleanup? accepts H Δ rep.next rep.deleted evidence r = some fate ∧
          S'.packages q = some (match fate with
            | none => r
            | some reason => { r with status := .retired ⟨reason, S.revision + 1, none⟩ }) :=
  Proofs.rewrite_spec hS h

/-- The extension rule, exactly (§6): only the vocabulary and the counters change. -/
theorem extend_spec {schema : Schema} {contracts : List Contract}
    (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ' = { Δ with schema := schema, contracts := contracts } ∧
      S' = { S with changeLog := S.changeLog ++ [S.revision + 1], revision := S.revision + 1 } :=
  Proofs.extend_spec h

end Ontography
