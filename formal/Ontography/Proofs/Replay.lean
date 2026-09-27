import Ontography.Replay
import Ontography.Proofs.ActivationLemmas
import Ontography.Proofs.Basic

/-!
# Replay reproduces an activation run (T5)

By induction over the run. Accepting a fresh identity `a` appends `(a, act)` to the history:
`a` is not yet listed, and the update at `a` leaves every listed activation alone. Replay of
the longer history is replay of the old one, which returns the old state by induction, and
then one more activation.

That activation rebuilds the original proposal's effect. The governing authority is the
root's, or the first input's, exactly as trigger admission computes it. Each rebuilt emission
keeps the original destination and, by the evidence for its commitment, the original payload.
Its authority is `Carry` when the recorded authority is the governing one, which needs no
rule, and otherwise the explicit transition the original must also have been. So every
rebuilt emission admits the original output and record, and the successor is the original.
-/

namespace Ontography.Proofs.Replay

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}

/-! ## The history -/

/-- `filterMap` reads its function only on the list's elements. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Accepting a fresh activation appends it to the history. -/
theorem history_accept {S : State} {a : ActivationId} {act : Activation}
    {recs : List PackageRecord} (hS : WF Δ S) (hfresh : S.activations a = none) :
    (S.accept a act recs).history = S.history ++ [(a, act)] := by
  unfold State.history
  show (S.activationIds ++ [a]).filterMap
      (fun b => (update S.activations a act b).map ((b, ·))) = _
  rw [List.filterMap_append]
  congr 1
  · apply filterMap_congr
    intro b hb
    have hba : b ≠ a := fun h => Activation.fresh_not_mem hS hfresh (h ▸ hb)
    rw [Common.update_of_ne hba]
  · simp [update]

/-! ## The governing authority -/

/-- Replay recovers the governing authority an admitted trigger returns. -/
theorem governing_of_trigger {S : State} {t : Trigger} {v : NodeId} {α : Authority}
    (h : trigger? Δ S t = some (v, α)) : governing? S t = some α := by
  cases t with
  | orig w β =>
    simp only [trigger?, rootTrigger?, bind, Option.bind_eq_some_iff, Common.guard_eq_some,
      pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ := h
    rfl
  | pkgs I =>
    simp only [trigger?, packageTrigger?, bind, Option.bind_eq_some_iff,
      Common.guard_eq_some] at h
    obtain ⟨p₀, hp₀, r₀, hr₀, d₀, _, _, _, edges, _, _, _, nd, _, h⟩ := h
    have hα : r₀.authority = α := by
      split at h <;>
        simp only [Option.bind_eq_some_iff, Common.guard_eq_some, exists_const, pure,
          Option.some.injEq, Prod.mk.injEq] at h <;>
        exact h.2.2
    simp [governing?, hp₀, hr₀, hα]

/-! ## Rebuilt emissions -/

/-- The destination an output records: its birth edge, or outbound with its object type. -/
def destinationOf (o : Output) : Destination :=
  match o.edge with
  | some e => .delivered e
  | none => .outbound o.objectType

/-- The authority an output requested with `auth` carries when `α` governs. -/
def carried (α : Authority) : OutputAuthority → Authority
  | .carry => α
  | .transition β => β

/-- The emission replay rebuilds from output `o` of an activation governed by `α`, given its
payload. -/
def emissionOf (α : Authority) (o : Output) (bytes : Bytes) : Emission :=
  ⟨destinationOf o, if o.authority = α then .carry else .transition o.authority, bytes⟩

/-- The map from recorded outputs to emissions inside `Activation.replayProposal`. -/
def replayOutput (α : Authority) (evidence : Digest → Option Bytes) (o : Output) :
    Option Emission := do
  let bytes ← evidence o.digest
  pure (emissionOf α o bytes)

/-- `Activation.replayProposal` rebuilds each output with `replayOutput`. -/
theorem replayProposal_eq {act : Activation} {α : Authority}
    {evidence : Digest → Option Bytes} :
    act.replayProposal α evidence = (do
      let emissions ← act.outputs.mapM (replayOutput α evidence)
      pure ⟨act.trigger, act.result, emissions⟩) := rfl

/-- An admitted output records its emission's destination, carried authority, and payload
commitment. -/
theorem emission_output {v : NodeId} {α : Authority} {dest : Destination}
    {auth : OutputAuthority} {payload : Bytes} {x : Output × PackageRecord}
    (h : emission? accepts H Δ v α ⟨dest, auth, payload⟩ = some x) :
    destinationOf x.1 = dest ∧ x.1.authority = carried α auth ∧ x.1.digest = H payload := by
  cases auth <;> cases dest <;>
    simp only [emission?, bind, Option.bind_eq_some_iff, Common.guard_eq_some, pure,
      Option.some.injEq] at h
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- `Carry` admits whatever the explicit transition to the governing authority admits. -/
theorem emission_carry {v : NodeId} {α : Authority} {dest : Destination} {payload : Bytes}
    {x : Output × PackageRecord}
    (h : emission? accepts H Δ v α ⟨dest, .transition α, payload⟩ = some x) :
    emission? accepts H Δ v α ⟨dest, .carry, payload⟩ = some x := by
  simp only [emission?, bind, Option.bind_eq_some_iff, Common.guard_eq_some] at h ⊢
  obtain ⟨u, hsub, u', -, hrest⟩ := h
  refine ⟨u, hsub, u', fun hc => ?_, hrest⟩
  rcases hc with hc | hc
  · nomatch hc
  · exact absurd ⟨List.Subset.refl α, List.Subset.refl α⟩ hc

/-- The rebuilt emission admits the original output and record. -/
theorem emission_replay {v : NodeId} {α : Authority} {em : Emission}
    {x : Output × PackageRecord} (h : emission? accepts H Δ v α em = some x) :
    x.1.digest = H em.payload ∧
      emission? accepts H Δ v α (emissionOf α x.1 em.payload) = some x := by
  obtain ⟨dest, auth, payload⟩ := em
  obtain ⟨hdest, hauth, hdig⟩ := emission_output h
  refine ⟨hdig, ?_⟩
  rw [emissionOf, hdest, hauth]
  cases auth with
  | carry =>
    rw [carried, ite_eq_left rfl]
    exact h
  | transition β =>
    rw [carried]
    by_cases hβ : β = α
    · subst hβ
      rw [ite_eq_left rfl]
      exact emission_carry h
    · rw [ite_eq_right hβ]
      exact h

/-- Every rebuilt emission of an admitted list of emissions admits the original output. -/
theorem mapM_replay {v : NodeId} {α : Authority} {evidence : Digest → Option Bytes} :
    ∀ {ems : List Emission} {outs : List (Output × PackageRecord)},
      ems.mapM (emission? accepts H Δ v α) = some outs →
      (∀ em ∈ ems, evidence (H em.payload) = some em.payload) →
      ∃ ems', (outs.map Prod.fst).mapM (replayOutput α evidence) = some ems' ∧
        ems'.mapM (emission? accepts H Δ v α) = some outs
  | [], outs, h, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | em :: ems, outs, h, hev => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨ems', h₁, h₂⟩ := mapM_replay hxs fun e he => hev e (List.mem_cons_of_mem _ he)
    obtain ⟨hdig, hx'⟩ := emission_replay hx
    refine ⟨emissionOf α x.1 em.payload :: ems', ?_, ?_⟩
    · simp [List.mapM_cons, replayOutput, hdig, hev em List.mem_cons_self, h₁]
    · simp [List.mapM_cons, hx', h₂]

/-! ## One more activation -/

/-- Replaying an admitted activation from its pre-state, with evidence for its payloads,
reproduces it and appends it to the history. -/
theorem replay_step {S S' : State} {a : ActivationId} {prop : Proposal}
    {evidence : Digest → Option Bytes} (hS : WF Δ S)
    (h : activate accepts H Δ S a prop = some S')
    (hev : ∀ em ∈ prop.emissions, evidence (H em.payload) = some em.payload) :
    ∃ act, S'.history = S.history ++ [(a, act)] ∧
      (do
        let α ← governing? S act.trigger
        let prop' ← act.replayProposal α evidence
        activate accepts H Δ S a prop') = some S' := by
  simp only [activate, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const, pure,
    Option.some.injEq] at h
  obtain ⟨hfresh, ⟨v, α⟩, htrig, nd, hnd, hres, outs, houts, rfl⟩ := h
  obtain ⟨ems', h₁, h₂⟩ := mapM_replay houts hev
  refine ⟨⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩, history_accept hS hfresh, ?_⟩
  simp only [bind, Option.bind_eq_some_iff]
  refine ⟨α, governing_of_trigger htrig, ⟨prop.trigger, prop.result, ems'⟩, ?_, ?_⟩
  · rw [replayProposal_eq]
    simp only [h₁]
    rfl
  · simp only [activate, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
      pure, Option.some.injEq]
    exact ⟨hfresh, (v, α), htrig, nd, hnd, hres, outs, h₂, rfl⟩

/-- A state reached by activations alone is reachable. -/
theorem reachable_of_run {S : State} {payloads : List Bytes}
    (h : ActivationRun accepts H Δ S payloads) : Reachable accepts H Δ S := by
  induction h with
  | initial => exact .initial
  | @activate S S' payloads a prop _ hact ih => exact .next (.activate a prop) ih hact

end Ontography.Proofs.Replay

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S : State}

/-- T5: replaying the history of a state reached by activations alone, with evidence for
every payload it used, reproduces the state exactly. -/
theorem replay_history (hΔ : Δ.Admitted) {payloads : List Bytes}
    (hrun : ActivationRun accepts H Δ S payloads) {evidence : Digest → Option Bytes}
    (hevidence : ∀ b ∈ payloads, evidence (H b) = some b) :
    replay accepts H Δ S.history evidence = some S := by
  induction hrun with
  | initial => rfl
  | @activate S S' payloads a prop hrun hact ih =>
    have hS := wf_of_reachable hΔ (Replay.reachable_of_run hrun)
    obtain ⟨act, hhist, hstep⟩ := Replay.replay_step hS hact fun em hem =>
      hevidence _ (List.mem_append_right _ (List.mem_map_of_mem hem))
    have ih' := ih fun b hb => hevidence b (List.mem_append_left _ hb)
    unfold replay at ih' ⊢
    rw [hhist, List.foldlM_append, ih']
    simpa using hstep

end Ontography.Proofs
