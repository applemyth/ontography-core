import Ontography.Commutation
import Ontography.Runs
import Ontography.Checkpoint
import Ontography.Replay
import Ontography.Proofs.Runs
import Ontography.Proofs.Replay
import Ontography.Proofs.Checkpoint
import Ontography.Proofs.Commutation

/-!
# Metatheory

Theorems about the calculus as a whole rather than one transition:
- T4: locality and commutation of rewrites.
- T6: across a run, activations persist and removed identities never return.
- T5: checkpoint restoration accepts every well-formed state but checks strictly less than
  well-formedness, and fixed-graph replay reproduces a state reached by activations alone.
-/

namespace Ontography

/-! ## Locality and commutation (T4) -/

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- Locality: a rewrite changes only live packages whose holder it affects. -/
theorem rewrite_local (hΔ : Δ.Admitted) (hS : WF Δ S) {req : RewriteRequest}
    {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S'))
    {q : PackageId} {r r' : PackageRecord} (hr : S.packages q = some r)
    (hr' : S'.packages q = some r') (hchanged : r' ≠ r) :
    r.status = .live ∧ Affected Δ Δ' r.holder :=
  Proofs.rewrite_local hΔ hS h hr hr' hchanged

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
      (S₂₁.packages q).map PackageRecord.unstamped :=
  Proofs.rewrite_commute hΔ hS h₁ h₁₂ h₂ h₂₁ hsame hdisjoint q

end

/-! ## Runs (T6) -/

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- An accepted activation is never replaced, so no activation identity is accepted twice. -/
theorem activation_persists (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {a : ActivationId} {act : Activation}
    (ha : S.activations a = some act) : S'.activations a = some act :=
  Proofs.activation_persists hΔ hS h ha

/-- A node identity that has left the definition never returns to it. -/
theorem removed_node_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {v : NodeId} (hused : v ∈ S.usedNodes)
    (hgone : v ∉ Δ.nodes) : v ∉ Δ'.nodes :=
  Proofs.removed_node_never_returns hΔ hS h hused hgone

/-- An edge identity that has left the definition never returns to it. -/
theorem removed_edge_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {e : EdgeId} (hused : e ∈ S.usedEdges)
    (hgone : e ∉ Δ.edges.map (·.id)) : e ∉ Δ'.edges.map (·.id) :=
  Proofs.removed_edge_never_returns hΔ hS h hused hgone

end

/-! ## Checkpoint restoration -/

section
variable {Δ : Definition} {S : State}

/-- The checks read only the checkpoint. -/
theorem checkpointValid_congr {S' : State} (hsame : SameCheckpoint S S')
    (h : CheckpointValid Δ S) : CheckpointValid Δ S' :=
  Proofs.checkpointValid_congr hsame h

/-- Restoration accepts every well-formed state, so it never rejects a reachable one. -/
theorem checkpoint_of_wf (hΔ : Δ.Admitted) (hS : WF Δ S) : CheckpointValid Δ S :=
  Proofs.checkpoint_of_wf hΔ hS

/-- The checks are strictly weaker than well-formedness: some admitted definition has a
checkpoint that passes every check yet belongs to no well-formed state, because two receipts
on a removed edge disagree about its endpoints. -/
theorem checkpoint_gap : ∃ (Δ : Definition) (S : State), Δ.Admitted ∧ CheckpointValid Δ S ∧
    ∀ S', SameCheckpoint S S' → ¬ WF Δ S' :=
  Proofs.checkpoint_gap

end

/-! ## Fixed-graph replay (T5) -/

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S : State}

/-- T5: replaying the history of a state reached by activations alone, with evidence for
every payload it used, reproduces the state exactly. -/
theorem replay_history (hΔ : Δ.Admitted) {payloads : List Bytes}
    (hrun : ActivationRun accepts H Δ S payloads) {evidence : Digest → Option Bytes}
    (hevidence : ∀ b ∈ payloads, evidence (H b) = some b) :
    replay accepts H Δ S.history evidence = some S :=
  Proofs.replay_history hΔ hrun hevidence

end

end Ontography
