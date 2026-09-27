import Ontography.Commutation
import Ontography.Runs
import Ontography.Checkpoint
import Ontography.Replay
import Ontography.Proofs.Runs
import Ontography.Proofs.Replay
import Ontography.Proofs.Commutation

/-!
# Metatheory

Theorems about the calculus as a whole rather than one transition:
- T4: locality and commutation of rewrites.
- T6: across a run, activations persist and removed identities never return.
- T5: checkpoint restoration checks exactly the invariants, and fixed-graph replay accepts
  exactly the faithful histories and reproduces the state they record.
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

/-- T4: when both orders of two rewrites apply, they yield the same definition; and if their
affected holders are disjoint across both orders, they also commute on every package record,
up to retirement stamps. -/
theorem rewrite_commute (hΔ : Δ.Admitted) (hS : WF Δ S) {ρ₁ ρ₂ : RewriteRequest}
    {evidence : List (Digest × Bytes)} {Δ₁ Δ₂ Δ₁₂ Δ₂₁ : Definition} {S₁ S₂ S₁₂ S₂₁ : State}
    (h₁ : rewrite accepts H grammar Δ S ρ₁ evidence = some (Δ₁, S₁))
    (h₁₂ : rewrite accepts H grammar Δ₁ S₁ ρ₂ evidence = some (Δ₁₂, S₁₂))
    (h₂ : rewrite accepts H grammar Δ S ρ₂ evidence = some (Δ₂, S₂))
    (h₂₁ : rewrite accepts H grammar Δ₂ S₂ ρ₁ evidence = some (Δ₂₁, S₂₁)) :
    Δ₁₂.Equiv Δ₂₁ ∧
      ((∀ v, Affected Δ Δ₁ v ∨ Affected Δ₂ Δ₂₁ v → ¬ (Affected Δ Δ₂ v ∨ Affected Δ₁ Δ₁₂ v)) →
        ∀ q, (S₁₂.packages q).map PackageRecord.unstamped =
          (S₂₁.packages q).map PackageRecord.unstamped) :=
  Proofs.rewrite_commute hΔ hS h₁ h₁₂ h₂ h₂₁

end

/-! ## Runs (T6) -/

section
variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- Everything a transition may not change, it never changes across a run: accepted
activations, each package's immutable facts, deliveries once made, settled statuses, and the
lifetime records, which only grow. -/
theorem sysSteps_frame (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') : Frame S S' :=
  Proofs.sysSteps_frame hΔ hS h

/-- An accepted activation identity is never accepted again. -/
theorem accepted_not_reaccepted {a : ActivationId} (ha : S.activations a ≠ none)
    {prop : Proposal} : activate accepts H Δ S a prop = none :=
  Proofs.accepted_not_reaccepted ha

/-- A package identity is born only with its producing activation, when that activation is
accepted; together with `sysSteps_frame`, no package identity is born twice. -/
theorem sysStep_newborn {op : SysOp} (h : sysStep accepts H grammar Δ S op = some (Δ', S'))
    {p : PackageId} {r : PackageRecord} (hnone : S.packages p = none)
    (hsome : S'.packages p = some r) :
    S.activations p.producer = none ∧ S'.activations p.producer ≠ none :=
  Proofs.sysStep_newborn h hnone hsome

/-- An accepted activation is never replaced. -/
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
    (h : CheckpointValid Δ S) : CheckpointValid Δ S' := by
  sorry

/-- Restoration accepts every well-formed state, so it never rejects a reachable one. -/
theorem checkpoint_of_wf (hΔ : Δ.Admitted) (hS : WF Δ S) : CheckpointValid Δ S := by
  sorry

/-- Restoration checks exactly the invariants: every checkpoint that passes is recorded by a
well-formed state, which differs from it at most in acceptance order and the ghost logs. -/
theorem checkpoint_sound (hΔ : Δ.Admitted) (h : CheckpointValid Δ S) :
    ∃ S', S'.activations = S.activations ∧ S'.packages = S.packages ∧
      S'.activationIds.Perm S.activationIds ∧ S'.packageIds = S.packageIds ∧
      S'.usedNodes = S.usedNodes ∧ S'.usedEdges = S.usedEdges ∧
      S'.definitionChanges = S.definitionChanges ∧ S'.revision = S.revision ∧ WF Δ S' := by
  sorry

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

/-- Replay accepts only faithful histories: whatever it accepts is the history of the state it
builds, which is reachable. -/
theorem replay_sound {h : List (ActivationId × Activation)} {evidence : Digest → Option Bytes}
    (hreplay : replay accepts H Δ h evidence = some S) :
    S.history = h ∧ Reachable accepts H Δ S :=
  Proofs.replay_sound hreplay

/-- A reachable workflow whose revision counts only its activations was reached by
activations alone, under its current definition. -/
theorem activationRun_of_revision {grammar : List Production}
    (h : SysReachable accepts H grammar Δ S) (hrevision : S.revision = S.activationIds.length) :
    ∃ payloads, ActivationRun accepts H Δ S payloads :=
  Proofs.activationRun_of_revision h hrevision

/-- Replay in any causal order of the history, such as the kernel's consumption order,
reproduces the state up to the order of acceptance. -/
theorem replay_causal (hΔ : Δ.Admitted) {payloads : List Bytes}
    (hrun : ActivationRun accepts H Δ S payloads) {evidence : Digest → Option Bytes}
    (hevidence : ∀ b ∈ payloads, evidence (H b) = some b)
    {h : List (ActivationId × Activation)} (hperm : h.Perm S.history)
    (hcausal : ∀ (i j : Nat) (a b : ActivationId) (act act' : Activation),
      h[i]? = some (a, act) → h[j]? = some (b, act') →
      (∃ p ∈ act'.trigger.inputs, p.producer = a) → i < j) :
    ∃ S', replay accepts H Δ h evidence = some S' ∧ S'.activations = S.activations ∧
      S'.packages = S.packages ∧ S'.activationIds.Perm S.activationIds ∧
      S'.packageIds.Perm S.packageIds ∧ S'.usedNodes = S.usedNodes ∧ S'.edgeLog = S.edgeLog ∧
      S'.changeLog = S.changeLog ∧ S'.revision = S.revision :=
  Proofs.replay_causal hΔ hrun hevidence hperm hcausal

end

end Ontography
