import Ontography.SystemTheorems
import Ontography.Runs

/-!
# Runs (T6)

A run extends one transition at a time, so each fact about runs is an invariant proved by
induction over the run. Every transition keeps the definition admitted and the state well
formed (`wf_sysStep`), which the frame theorem needs, so the induction carries both.

`Frame` is reflexive and transitive, so the frames of the transitions compose into the frame
of the run, and an accepted activation persists by it. An identity that has left the
definition stays a lifetime identity, since the lifetime records only grow, and freshness
admits to the next definition only current identities and ones never used, so it stays out.

Package identities are born only by activation: transfer and explicit retirement replace the
record of a recorded package, a rewrite changes recorded packages only, and an extension keeps
every record. Accepting `a` records new packages only as its outputs `(a, i)`, and `activate`'s
first guard admits `a` only while it is not accepted.
-/

namespace Ontography.Proofs.Runs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- Induction over a run: a property that every transition from a well-formed state preserves
holds at the end of a run from an admitted, well-formed workflow where it holds, as do
admission and well-formedness. -/
theorem sysSteps_invariant {P : Definition → State → Prop} (hΔ : Δ.Admitted) (hS : WF Δ S)
    (hP : P Δ S)
    (hstep : ∀ {Δ₁ Δ₂ : Definition} {S₁ S₂ : State} {op : SysOp}, WF Δ₁ S₁ → P Δ₁ S₁ →
      sysStep accepts H grammar Δ₁ S₁ op = some (Δ₂, S₂) → P Δ₂ S₂)
    (h : SysSteps accepts H grammar Δ S Δ' S') : Δ'.Admitted ∧ WF Δ' S' ∧ P Δ' S' := by
  induction h with
  | refl => exact ⟨hΔ, hS, hP⟩
  | tail _ _ hop ih =>
    obtain ⟨hΔ₁, hS₁, hP₁⟩ := ih hS hP
    obtain ⟨hΔ₂, hS₂⟩ := Ontography.wf_sysStep hΔ₁ hS₁ hop
    exact ⟨hΔ₂, hS₂, hstep hS₁ hP₁ hop⟩

/-- Every state frames itself. -/
theorem Frame.refl (S : State) : Frame S S where
  activations _ _ h := h
  packages _ r h := ⟨r, h, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  usedNodes := List.Subset.refl _
  edgeLog := List.Subset.refl _
  changeLog := List.Subset.refl _

/-- Frames compose: what the first keeps, the second keeps too. -/
theorem Frame.trans {S₁ S₂ S₃ : State} (h₁₂ : Frame S₁ S₂) (h₂₃ : Frame S₂ S₃) :
    Frame S₁ S₃ where
  activations a act h := h₂₃.activations a act (h₁₂.activations a act h)
  packages p r h := by
    obtain ⟨r', h', ho, ha, hd, hn, hdel, hst⟩ := h₁₂.packages p r h
    obtain ⟨r'', h'', ho', ha', hd', hn', hdel', hst'⟩ := h₂₃.packages p r' h'
    refine ⟨r'', h'', ho'.trans ho, ha'.trans ha, hd'.trans hd, hn'.trans hn,
      fun hne => ?_, fun hne => ?_⟩
    · -- A delivery kept by the first is a delivery the second keeps.
      exact (hdel' (by rw [hdel hne]; exact hne)).trans (hdel hne)
    · -- So is a settled status.
      exact (hst' (by rw [hst hne]; exact hne)).trans (hst hne)
  usedNodes := List.Subset.trans h₁₂.usedNodes h₂₃.usedNodes
  edgeLog := List.Subset.trans h₁₂.edgeLog h₂₃.edgeLog
  changeLog := List.Subset.trans h₁₂.changeLog h₂₃.changeLog

/-- A rewrite records no package that was not recorded. -/
theorem rewrite_absent {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H grammar Δ S req evidence = some (Δ', S')) {q : PackageId}
    (hq : S.packages q = none) : S'.packages q = none := by
  simp only [rewrite, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, pr, -, rep, -, fates, -, rfl, rfl⟩ := h
  dsimp only
  rw [hq]
  split <;> rfl

end Ontography.Proofs.Runs

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {grammar : List Production} {Δ Δ' : Definition} {S S' : State}

/-- Everything a transition may not change, it never changes across a run: accepted
activations, each package's immutable facts, deliveries once made, settled statuses, and the
lifetime records, which only grow. -/
theorem sysSteps_frame (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') : Frame S S' :=
  (Runs.sysSteps_invariant (P := fun _ S₁ => Frame S S₁) hΔ hS (Runs.Frame.refl S)
    (fun hS₁ hF hop => Runs.Frame.trans hF (Ontography.sysStep_frame hS₁ hop)) h).2.2

/-- An accepted activation identity is never accepted again. -/
theorem accepted_not_reaccepted {a : ActivationId} (ha : S.activations a ≠ none)
    {prop : Proposal} : activate accepts H Δ S a prop = none := by
  cases h : activate accepts H Δ S a prop with
  | none => rfl
  | some S' =>
    -- The first guard admits only an identity that is not accepted.
    obtain ⟨_, _, _, hfresh, -⟩ := Common.activate_eq_some h
    exact absurd hfresh ha

/-- A package identity is born only with its producing activation, when that activation is
accepted; together with `sysSteps_frame`, no package identity is born twice. -/
theorem sysStep_newborn {op : SysOp} (h : sysStep accepts H grammar Δ S op = some (Δ', S'))
    {p : PackageId} {r : PackageRecord} (hnone : S.packages p = none)
    (hsome : S'.packages p = some r) :
    S.activations p.producer = none ∧ S'.activations p.producer ≠ none := by
  cases op with
  | step op =>
    obtain ⟨-, hstep⟩ := Sys.step_eq_some h
    cases op with
    | activate a prop =>
      obtain ⟨act, -, records, hfresh, -, rfl⟩ := Common.activate_eq_some hstep
      -- Accepting `a` records a new package only as an output `(a, i)`.
      have hpa : p.producer = a := Classical.byContradiction fun hne => by
        rw [Activation.accept_packages, ite_eq_right hne] at hsome
        split at hsome <;> simp [hnone] at hsome
      rw [hpa, Activation.accept_activations, ite_eq_left rfl]
      exact ⟨hfresh, Option.some_ne_none act⟩
    | transfer q e payload =>
      -- Transfer replaces the record of the recorded `q`.
      obtain ⟨r₀, _, hr₀, -, -, -, -, rfl⟩ := Common.transfer_eq_some hstep
      rcases Common.setRecord_packages_eq_some.1 hsome with ⟨rfl, -⟩ | ⟨-, hsome⟩
      · rw [hr₀] at hnone
        cases hnone
      · rw [hnone] at hsome
        cases hsome
    | retire q evidence =>
      -- Explicit retirement replaces the record of the recorded `q`.
      obtain ⟨r₀, hr₀, -, -, rfl⟩ := Common.retire_eq_some hstep
      rcases Common.setRecord_packages_eq_some.1 hsome with ⟨rfl, -⟩ | ⟨-, hsome⟩
      · rw [hr₀] at hnone
        cases hnone
      · rw [hnone] at hsome
        cases hsome
  | rewrite req evidence =>
    rw [Runs.rewrite_absent h hnone] at hsome
    cases hsome
  | extend schema contracts =>
    -- An extension keeps every record.
    obtain ⟨-, rfl⟩ := extend_spec h
    cases hnone.symm.trans hsome

/-- An accepted activation is never replaced, so no activation identity is accepted twice. -/
theorem activation_persists (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {a : ActivationId} {act : Activation}
    (ha : S.activations a = some act) : S'.activations a = some act :=
  (sysSteps_frame hΔ hS h).activations a act ha

/-- A node identity that has left the definition never returns to it. -/
theorem removed_node_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {v : NodeId} (hused : v ∈ S.usedNodes)
    (hgone : v ∉ Δ.nodes) : v ∉ Δ'.nodes :=
  (Runs.sysSteps_invariant (P := fun Δ₁ S₁ => v ∈ S₁.usedNodes ∧ v ∉ Δ₁.nodes) hΔ hS
    ⟨hused, hgone⟩
    (fun hS₁ ⟨hused₁, hgone₁⟩ hop =>
      -- `v` stays used, and freshness admits only current or unused nodes.
      ⟨(Ontography.sysStep_frame hS₁ hop).usedNodes hused₁, fun hv =>
        ((Ontography.sysStep_fresh hop).1 v hv).elim hgone₁ (· hused₁)⟩) h).2.2.2

/-- An edge identity that has left the definition never returns to it. -/
theorem removed_edge_never_returns (hΔ : Δ.Admitted) (hS : WF Δ S)
    (h : SysSteps accepts H grammar Δ S Δ' S') {e : EdgeId} (hused : e ∈ S.usedEdges)
    (hgone : e ∉ Δ.edges.map (·.id)) : e ∉ Δ'.edges.map (·.id) := by
  refine (Runs.sysSteps_invariant
    (P := fun Δ₁ S₁ => e ∈ S₁.usedEdges ∧ e ∉ Δ₁.edges.map (·.id)) hΔ hS ⟨hused, hgone⟩
    (fun hS₁ ⟨hused₁, hgone₁⟩ hop => ⟨?_, ?_⟩) h).2.2.2
  · -- The edge log only grows, so `e` stays used.
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hused₁
    exact List.mem_map_of_mem ((Ontography.sysStep_frame hS₁ hop).edgeLog hx)
  · -- Freshness admits only current edges or ones with unused identities.
    intro he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    rcases (Ontography.sysStep_fresh hop).2 x hx with hx₁ | hfresh
    · exact hgone₁ (List.mem_map_of_mem hx₁)
    · exact hfresh hused₁

end Ontography.Proofs
