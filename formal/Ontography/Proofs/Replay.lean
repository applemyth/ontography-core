import Ontography.Replay
import Ontography.SystemTheorems
import Ontography.Proofs.ActivationLemmas
import Ontography.Proofs.Basic

/-!
# Fixed-graph replay (T5)

`replay` folds `Replay.replayStep` over a history: re-derive the recorded activation's
proposal, admit it, and check that the accepted activation is the record.

**Completeness.** An admitted activation is replayed from any state that agrees with its
pre-state on the trigger's inputs (`Replay.replayStep_of_activate`). Trigger admission and
the governing authority read the state only there, and each rebuilt emission keeps the
original destination and, by the evidence for its commitment, the original payload. Its
authority is `Carry` when the recorded authority is the governing one, which needs no rule,
and otherwise the explicit transition the original must also have been. So the rebuilt
proposal admits the original outputs and records, and the accepted activation is the record.
`replay_history` applies this to each pre-state of the run.

**Soundness.** Each accepted entry is an activation step whose accepted activation is the
entry, at an identity not yet accepted, so it extends the history by exactly that entry.

**Revision.** `revision - |A|` never decreases along a run, and every transition other than
an activation raises it, so a state whose revision counts only its activations was reached
by activations alone, under a definition that never changed.

**Causal order.** Replaying a causal order of the history simulates the run on the set of
activations replayed so far. That set is closed under producers, and the replayed state is
the final state restricted to it: its activations, their outputs, and each output consumed
only if its consumer was already replayed. Each package is consumed by one activation, so the
inputs of the next activation are live in the restriction exactly as they were in its
pre-state, and the activation replays there with the same outputs.
-/

namespace Ontography.Proofs.Replay

/-- One entry of `replay`: re-derive the recorded activation's proposal, admit it, and check
that the accepted activation is the record. -/
def replayStep (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)
    (evidence : Digest → Option Bytes) (S : State) (entry : ActivationId × Activation) :
    Option State := do
  let α ← governing? S entry.2.trigger
  let prop ← entry.2.replayProposal α H evidence
  let S' ← activate accepts H Δ S entry.1 prop
  guard (S'.activations entry.1 = some entry.2)
  pure S'

section

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}

/-- `replay` folds `replayStep` over the history from the empty state. -/
theorem replay_eq {history : List (ActivationId × Activation)}
    {evidence : Digest → Option Bytes} :
    replay accepts H Δ history evidence =
      history.foldlM (replayStep accepts H Δ evidence) (State.initial Δ) := rfl

/-! ## The history -/

/-- `filterMap` reads its function only on the list's elements. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- `mapM` in `Option` reads its function only on the list's elements. -/
theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons, h x List.mem_cons_self,
      mapM_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Accepting an identity not yet listed appends it to the history. -/
theorem history_accept {S : State} {a : ActivationId} {act : Activation}
    {recs : List PackageRecord} (hfresh : a ∉ S.activationIds) :
    (S.accept a act recs).history = S.history ++ [(a, act)] := by
  unfold State.history
  show (S.activationIds ++ [a]).filterMap
      (fun b => (update S.activations a act b).map ((b, ·))) = _
  rw [List.filterMap_append]
  congr 1
  · apply filterMap_congr
    intro b hb
    have hba : b ≠ a := fun h => hfresh (h ▸ hb)
    rw [Common.update_of_ne hba]
  · simp [update]

/-- The history lists exactly the accepted activations. -/
theorem mem_history {S : State} {a : ActivationId} {act : Activation} :
    (a, act) ∈ S.history ↔ a ∈ S.activationIds ∧ S.activations a = some act := by
  unfold State.history
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨act', h', he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    exact ⟨hb, h'⟩
  · rintro ⟨ha, h⟩
    exact ⟨a, ha, by rw [h]; rfl⟩

/-- Listing accepted identities with their records and forgetting the records lists them. -/
theorem filterMap_fst {f : ActivationId → Option Activation} :
    ∀ {l : List ActivationId}, (∀ a ∈ l, (f a).isSome) →
      (l.filterMap fun a => (f a).map ((a, ·))).map Prod.fst = l
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    rw [List.filterMap_cons, hy, Option.map_some]
    dsimp only
    rw [List.map_cons, filterMap_fst fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- When every listed identity is accepted, the history lists them in order. -/
theorem history_map_fst {S : State} (hdom : ∀ a ∈ S.activationIds, (S.activations a).isSome) :
    S.history.map Prod.fst = S.activationIds :=
  filterMap_fst hdom

/-! ## What replay reads of the state -/

/-- Trigger admission reads the state only at the trigger's inputs. -/
theorem trigger?_congr {S R : State} {t : Trigger}
    (h : ∀ p ∈ t.inputs, R.packages p = S.packages p) : trigger? Δ R t = trigger? Δ S t := by
  cases t with
  | orig v α => rfl
  | pkgs I =>
    have hmap : ∀ v α, I.mapM (inputEdge? R v α) = I.mapM (inputEdge? S v α) := fun v α =>
      mapM_congr fun p hp => by simp only [inputEdge?, h p hp]
    cases I with
    | nil => rfl
    | cons p₀ rest =>
      have h₀ : R.packages p₀ = S.packages p₀ := h p₀ List.mem_cons_self
      simp only [trigger?, packageTrigger?, List.head?_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, h₀, hmap]

/-- The governing authority reads the state only at the trigger's inputs. -/
theorem governing?_congr {S R : State} {t : Trigger}
    (h : ∀ p ∈ t.inputs, R.packages p = S.packages p) : governing? R t = governing? S t := by
  cases t with
  | orig v α => rfl
  | pkgs I =>
    cases I with
    | nil => rfl
    | cons p₀ rest =>
      have h₀ : R.packages p₀ = S.packages p₀ := h p₀ List.mem_cons_self
      simp only [governing?, List.head?_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, h₀]

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
def replayOutput (α : Authority) (H : Bytes → Digest) (evidence : Digest → Option Bytes)
    (o : Output) : Option Emission := do
  let bytes ← evidence o.digest
  guard (H bytes = o.digest)
  pure (emissionOf α o bytes)

/-- `Activation.replayProposal` rebuilds each output with `replayOutput`. -/
theorem replayProposal_eq {act : Activation} {α : Authority}
    {evidence : Digest → Option Bytes} :
    act.replayProposal α H evidence = (do
      let emissions ← act.outputs.mapM (replayOutput α H evidence)
      pure ⟨act.trigger, act.result, emissions⟩) := rfl

/-- An admitted output records its emission's destination, carried authority, and payload
commitment, and its record is live. -/
theorem emission_output {v : NodeId} {α : Authority} {dest : Destination}
    {auth : OutputAuthority} {payload : Bytes} {x : Output × PackageRecord}
    (h : emission? accepts H Δ v α ⟨dest, auth, payload⟩ = some x) :
    destinationOf x.1 = dest ∧ x.1.authority = carried α auth ∧ x.1.digest = H payload ∧
      x.2.status = .live := by
  cases auth <;> cases dest <;>
    simp only [emission?, bind, Option.bind_eq_some_iff, Common.guard_eq_some, pure,
      Option.some.injEq] at h
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩

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
    x.1.digest = H em.payload ∧ x.2.status = .live ∧
      emission? accepts H Δ v α (emissionOf α x.1 em.payload) = some x := by
  obtain ⟨dest, auth, payload⟩ := em
  obtain ⟨hdest, hauth, hdig, hlive⟩ := emission_output h
  refine ⟨hdig, hlive, ?_⟩
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

/-- Every rebuilt emission of an admitted list of emissions admits the original output, and
every admitted record is live. -/
theorem mapM_replay {v : NodeId} {α : Authority} {evidence : Digest → Option Bytes} :
    ∀ {ems : List Emission} {outs : List (Output × PackageRecord)},
      ems.mapM (emission? accepts H Δ v α) = some outs →
      (∀ em ∈ ems, evidence (H em.payload) = some em.payload) →
      (∀ x ∈ outs, x.2.status = .live) ∧
        ∃ ems', (outs.map Prod.fst).mapM (replayOutput α H evidence) = some ems' ∧
          ems'.mapM (emission? accepts H Δ v α) = some outs
  | [], outs, h, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨fun _ hx => (List.not_mem_nil hx).elim, [], rfl, rfl⟩
  | em :: ems, outs, h, hev => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨hlive, ems', h₁, h₂⟩ := mapM_replay hxs fun e he => hev e (List.mem_cons_of_mem _ he)
    obtain ⟨hdig, hxlive, hx'⟩ := emission_replay hx
    refine ⟨fun y hy => ?_, emissionOf α x.1 em.payload :: ems', ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hxlive
      · exact hlive y hy
    · simp [List.mapM_cons, replayOutput, guard, hdig, hev em List.mem_cons_self, h₁]
    · simp [List.mapM_cons, hx', h₂]

/-! ## One more activation -/

/-- An admitted activation accepts a record `act` with output records `recs`, all live, from
live inputs; and it replays, with evidence for its payloads, from every state that has not
accepted its identity and agrees with the pre-state on its inputs. -/
theorem replayStep_of_activate {S S' : State} {a : ActivationId} {prop : Proposal}
    {evidence : Digest → Option Bytes} (h : activate accepts H Δ S a prop = some S')
    (hev : ∀ em ∈ prop.emissions, evidence (H em.payload) = some em.payload) :
    ∃ act recs, S' = S.accept a act recs ∧ S.activations a = none ∧
      (∀ r ∈ recs, r.status = .live) ∧
      (∀ p ∈ act.trigger.inputs, ∃ r, S.packages p = some r ∧ r.status = .live) ∧
      ∀ R : State, R.activations a = none →
        (∀ p ∈ act.trigger.inputs, R.packages p = S.packages p) →
        replayStep accepts H Δ evidence R (a, act) = some (R.accept a act recs) := by
  simp only [activate, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const, pure,
    Option.some.injEq] at h
  obtain ⟨hfresh, ⟨v, α⟩, htrig, nd, hnd, hres, outs, houts, rfl⟩ := h
  obtain ⟨hlive, ems', h₁, h₂⟩ := mapM_replay houts hev
  refine ⟨⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩, outs.map Prod.snd, rfl, hfresh,
    fun r hr => ?_, fun p hp => ?_, fun R hR hpk => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    exact hlive x hx
  · obtain ⟨r, _, hr, hst, _⟩ := (Activation.trigger_spec htrig).inputs p hp
    exact ⟨r, hr, hst⟩
  · have htrig' : trigger? Δ R prop.trigger = some (v, α) := (trigger?_congr hpk).trans htrig
    have hprop : Activation.replayProposal ⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩
        α H evidence = some ⟨prop.trigger, prop.result, ems'⟩ := by
      rw [replayProposal_eq]
      simp only [h₁]
      rfl
    have hact : activate accepts H Δ R a ⟨prop.trigger, prop.result, ems'⟩ =
        some (R.accept a ⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩
          (outs.map Prod.snd)) := by
      simp only [activate, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
        pure, Option.some.injEq]
      exact ⟨hR, (v, α), htrig', nd, hnd, hres, outs, h₂, rfl⟩
    simp only [replayStep, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
      pure, Option.some.injEq]
    exact ⟨α, governing_of_trigger htrig', _, hprop, _, hact, by simp [State.accept, update], rfl⟩

/-- A state reached by activations alone is reachable. -/
theorem reachable_of_run {S : State} {payloads : List Bytes}
    (h : ActivationRun accepts H Δ S payloads) : Reachable accepts H Δ S := by
  induction h with
  | initial => exact .initial
  | @activate S S' payloads a prop _ hact ih => exact .next (.activate a prop) ih hact

/-! ## Soundness -/

/-- The accepted activations are exactly the listed identities. -/
def DomInv (S : State) : Prop := ∀ a, (S.activations a).isSome ↔ a ∈ S.activationIds

/-- Accepting `a` lists it and records it. -/
theorem domInv_accept {S : State} {a : ActivationId} {act : Activation}
    {recs : List PackageRecord} (h : DomInv S) : DomInv (S.accept a act recs) := by
  intro b
  show (update S.activations a act b).isSome ↔ b ∈ S.activationIds ++ [a]
  rw [List.mem_append, List.mem_singleton]
  by_cases hb : b = a
  · subst hb
    simp
  · rw [Common.update_of_ne hb, h b]
    simp [hb]

/-- An accepted replay entry is an activation step at a fresh identity that accepts the entry
itself. -/
theorem replayStep_inv {S S' : State} {entry : ActivationId × Activation}
    {evidence : Digest → Option Bytes}
    (h : replayStep accepts H Δ evidence S entry = some S') :
    ∃ prop recs, activate accepts H Δ S entry.1 prop = some S' ∧
      S.activations entry.1 = none ∧ S' = S.accept entry.1 entry.2 recs := by
  simp only [replayStep, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
    pure, Option.some.injEq] at h
  obtain ⟨-, -, prop, -, S'', hact, hrec, rfl⟩ := h
  obtain ⟨act, -, recs, hfresh, -, rfl⟩ := Common.activate_eq_some hact
  obtain rfl : act = entry.2 := by simpa [State.accept, update] using hrec
  exact ⟨prop, recs, hact, hfresh, rfl⟩

/-- Replaying entries from a reachable state appends them to its history, by activations. -/
theorem foldlM_sound {evidence : Digest → Option Bytes} :
    ∀ {h : List (ActivationId × Activation)} {R S : State}, DomInv R →
      Reachable accepts H Δ R → h.foldlM (replayStep accepts H Δ evidence) R = some S →
      S.history = R.history ++ h ∧ Reachable accepts H Δ S
  | [], R, S, _, hR, hfold => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
    subst hfold
    exact ⟨by simp, hR⟩
  | x :: xs, R, S, hdom, hR, hfold => by
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at hfold
    obtain ⟨R₁, h₁, hfold'⟩ := hfold
    obtain ⟨prop, recs, hact, hfresh, rfl⟩ := replayStep_inv h₁
    have hnot : x.1 ∉ R.activationIds := fun hm => by
      have := (hdom x.1).2 hm
      rw [hfresh] at this
      cases this
    obtain ⟨hhist, hreach⟩ :=
      foldlM_sound (domInv_accept hdom) (.next (.activate x.1 prop) hR hact) hfold'
    refine ⟨?_, hreach⟩
    rw [hhist, history_accept hnot]
    simp

/-! ## Causal replay

Replay in a causal order is compared with the final state `S` of the run. After replaying the
activations `L`, a set closed under producers, the replayed state is `S` restricted to `L`
(`Sim`): the activations of `L`, their outputs, and each output consumed if its consumer is in
`L` and live otherwise (`restore`). -/

/-- A record as it was born. A run of activations changes a record only by consuming it, so
this is the record before its consumption. -/
def born (r : PackageRecord) : PackageRecord := { r with status := .live }

theorem born_of_live {r : PackageRecord} (h : r.status = .live) : born r = r := by
  obtain ⟨_, _, _, _, _, s⟩ := r
  cases h
  rfl

theorem born_consume {r : PackageRecord} {b : ActivationId} (h : r.status = .consumed b) :
    { born r with status := .consumed b } = r := by
  obtain ⟨_, _, _, _, _, s⟩ := r
  cases h
  rfl

/-- `r` with its consumption undone unless its consumer is in `L`: the record of a package
after replaying `L`. -/
def restore (L : List ActivationId) (r : PackageRecord) : PackageRecord :=
  match r.status with
  | .consumed c => if c ∈ L then r else born r
  | _ => r

theorem restore_of_mem {L : List ActivationId} {r : PackageRecord} {c : ActivationId}
    (h : r.status = .consumed c) (hc : c ∈ L) : restore L r = r := by
  simp [restore, h, hc]

theorem restore_of_not_mem {L : List ActivationId} {r : PackageRecord} {c : ActivationId}
    (h : r.status = .consumed c) (hc : c ∉ L) : restore L r = born r := by
  simp [restore, h, hc]

theorem restore_of_live {L : List ActivationId} {r : PackageRecord} (h : r.status = .live) :
    restore L r = r := by
  simp [restore, h]

theorem restore_of_retired {L : List ActivationId} {r : PackageRecord} {ret : Retirement}
    (h : r.status = .retired ret) : restore L r = r := by
  simp [restore, h]

/-- Accepting `a` changes a package it did not produce at most by consuming it. -/
theorem accept_born {S : State} {a : ActivationId} {act : Activation}
    {recs : List PackageRecord} {q : PackageId} (hq : q.producer ≠ a) :
    ((S.accept a act recs).packages q).map born = (S.packages q).map born := by
  rw [Activation.accept_packages, ite_eq_right hq]
  split
  · rw [Option.map_map]
    rfl
  · rfl

/-- What replaying the accepted activation `b` of `S` needs and yields: its output records at
birth, and its replay from every state that has not accepted `b` and holds `b`'s inputs as
they were born. -/
structure Cert (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)
    (evidence : Digest → Option Bytes) (S : State) (b : ActivationId) (act : Activation)
    (recs : List PackageRecord) : Prop where
  outputs : ∀ i, recs[i]? = (S.packages ⟨b, i⟩).map born
  replay : ∀ R : State, R.activations b = none →
    (∀ p ∈ act.trigger.inputs, R.packages p = (S.packages p).map born) →
    replayStep accepts H Δ evidence R (b, act) = some (R.accept b act recs)

/-- The facts about a state reached by activations alone that causal replay uses. -/
structure RunInv (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)
    (evidence : Digest → Option Bytes) (S : State) : Prop where
  usedNodes : S.usedNodes = Δ.nodes
  edgeLog : S.edgeLog = Δ.edges
  changeLog : S.changeLog = []
  revision : S.revision = S.activationIds.length
  not_retired : ∀ q r ret, S.packages q = some r → r.status ≠ .retired ret
  certs : ∀ b act, S.activations b = some act → ∃ recs, Cert accepts H Δ evidence S b act recs

/-- Along a run of activations the lifetime records stay initial, the revision counts the
activations, nothing retires, and every accepted activation carries a `Cert`: when it is
accepted by `replayStep_of_activate`, and afterwards because later activations only consume
its inputs and outputs. -/
theorem runInv (hΔ : Δ.Admitted) {S : State} {payloads : List Bytes}
    (hrun : ActivationRun accepts H Δ S payloads) {evidence : Digest → Option Bytes}
    (hev : ∀ b ∈ payloads, evidence (H b) = some b) : RunInv accepts H Δ evidence S := by
  induction hrun with
  | initial =>
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | @activate S S' payloads a prop hrun hact ih =>
    have hS := wf_of_reachable hΔ (reachable_of_run hrun)
    have ih := ih fun b hb => hev b (List.mem_append_left _ hb)
    obtain ⟨act, recs, rfl, hfresh, hlive, hinputs, hreplay⟩ :=
      replayStep_of_activate hact fun em hem =>
        hev _ (List.mem_append_right _ (List.mem_map_of_mem hem))
    refine ⟨ih.usedNodes, ih.edgeLog, ih.changeLog, ?_, ?_, ?_⟩
    · show S.revision + 1 = (S.activationIds ++ [a]).length
      rw [List.length_append, ih.revision]
      rfl
    · -- New outputs are live, and consumed inputs were live.
      intro q r ret hq hst
      rw [Activation.accept_packages] at hq
      split at hq
      · rw [hlive r (List.mem_of_getElem? hq)] at hst
        cases hst
      · split at hq
        · obtain ⟨r₀, -, rfl⟩ := Option.map_eq_some_iff.1 hq
          cases hst
        · exact ih.not_retired q r ret hq hst
    · intro b act' hb
      rw [Activation.accept_activations] at hb
      split at hb
      · -- The new activation replays from wherever its inputs are as they were born.
        rename_i hba
        subst hba
        cases hb
        refine ⟨recs, fun i => ?_, fun R hR hpk => hreplay R hR fun p hp => ?_⟩
        · rw [Activation.accept_packages, ite_eq_left rfl]
          cases hi : recs[i]? with
          | none => rfl
          | some r => rw [Option.map_some, born_of_live (hlive r (List.mem_of_getElem? hi))]
        · obtain ⟨r₀, h₀, hlive₀⟩ := hinputs p hp
          rw [hpk p hp, Activation.accept_packages,
            ite_eq_right (Activation.producer_ne hS hfresh h₀), ite_eq_left hp, h₀]
          show some (born { r₀ with status := .consumed b }) = some r₀
          exact congrArg some (born_of_live hlive₀)
      · -- An earlier activation's inputs and outputs are only consumed.
        rename_i hba
        obtain ⟨recs', hc⟩ := ih.certs b act' hb
        refine ⟨recs', fun i => ?_, fun R hR hpk => hc.replay R hR fun p hp => ?_⟩
        · rw [hc.outputs i]
          exact (accept_born hba).symm
        · obtain ⟨r, d, hr, -⟩ := hS.inputs b act' hb p hp
          rw [hpk p hp]
          exact accept_born (Activation.producer_ne hS hfresh hr)

/-- The state replayed from the activations `L` of `S`: `S` restricted to `L`. -/
structure Sim (S : State) (L : List ActivationId) (R : State) : Prop where
  activations : ∀ a, R.activations a = if a ∈ L then S.activations a else none
  packages : ∀ q,
    R.packages q = if q.producer ∈ L then (S.packages q).map (restore L) else none
  activationIds : R.activationIds = L
  usedNodes : R.usedNodes = S.usedNodes
  edgeLog : R.edgeLog = S.edgeLog
  changeLog : R.changeLog = S.changeLog
  revision : R.revision = L.length

/-- `L` holds the producer of every input of its activations. -/
def Closed (S : State) (L : List ActivationId) : Prop :=
  ∀ c act, c ∈ L → S.activations c = some act → ∀ p ∈ act.trigger.inputs, p.producer ∈ L

/-- Replaying an activation `b` of `S` whose inputs were all produced in `L` extends the
restriction of `S` to `L` to the restriction to `L ++ [b]`. -/
theorem sim_step {S : State} {evidence : Digest → Option Bytes} (hS : WF Δ S)
    (hinv : RunInv accepts H Δ evidence S) {L : List ActivationId} {R : State}
    (hsim : Sim S L R) (hL : Closed S L) {b : ActivationId} {act : Activation}
    (hb : S.activations b = some act) (hbL : b ∉ L)
    (hin : ∀ p ∈ act.trigger.inputs, p.producer ∈ L) :
    ∃ R', replayStep accepts H Δ evidence R (b, act) = some R' ∧ Sim S (L ++ [b]) R' := by
  obtain ⟨recs, hcert⟩ := hinv.certs b act hb
  have hR : R.activations b = none := by rw [hsim.activations, ite_eq_right hbL]
  -- `b`'s inputs are consumed by `b`, which is not replayed yet, so they are as born.
  have hpk : ∀ p ∈ act.trigger.inputs, R.packages p = (S.packages p).map born := by
    intro p hp
    obtain ⟨r, d, hr, hst, -⟩ := hS.inputs b act hb p hp
    rw [hsim.packages, ite_eq_left (hin p hp), hr, Option.map_some, Option.map_some,
      restore_of_not_mem hst hbL]
  refine ⟨_, hcert.replay R hR hpk, fun a => ?_, fun q => ?_, ?_, hsim.usedNodes, hsim.edgeLog,
    hsim.changeLog, ?_⟩
  · rw [Activation.accept_activations, hsim.activations]
    by_cases hab : a = b
    · subst hab
      simp [hb]
    · simp [hab]
  · rw [Activation.accept_packages]
    by_cases hqb : q.producer = b
    · -- An output of `b`: live, or consumed by an activation not yet replayed.
      rw [ite_eq_left hqb, ite_eq_left (List.mem_append_right _ (List.mem_singleton.2 hqb))]
      obtain ⟨c, i⟩ := q
      dsimp only at hqb
      subst hqb
      rw [hcert.outputs i]
      cases hq : S.packages ⟨c, i⟩ with
      | none => rfl
      | some r =>
        rw [Option.map_some, Option.map_some]
        cases hst : r.status with
        | live => rw [restore_of_live hst, born_of_live hst]
        | consumed d =>
          have hdL : d ∉ L := fun hd => by
            obtain ⟨act', had, hmem⟩ := hS.consumed _ r d hq hst
            exact hbL (hL d act' hd had _ hmem)
          have hdc : d ≠ c := fun hdc => by
            have := hS.causal_order _ r d hq hst
            rw [hdc] at this
            exact Nat.lt_irrefl _ this
          rw [restore_of_not_mem hst (by simp [hdL, hdc])]
        | retired ret => exact absurd hst (hinv.not_retired _ r ret hq)
    · rw [ite_eq_right hqb]
      have hmem : q.producer ∈ L ++ [b] ↔ q.producer ∈ L := by simp [hqb]
      by_cases hqi : q ∈ act.trigger.inputs
      · -- An input of `b`: consumed by `b`, in `S` and now.
        rw [ite_eq_left hqi, hsim.packages, ite_eq_left (hin q hqi),
          ite_eq_left (hmem.2 (hin q hqi))]
        obtain ⟨r, d, hr, hst, -⟩ := hS.inputs b act hb q hqi
        rw [hr, Option.map_some, Option.map_some, Option.map_some,
          restore_of_not_mem hst hbL,
          restore_of_mem hst (List.mem_append_right _ (List.mem_singleton_self b)),
          born_consume hst]
      · -- Any other package: `b` is not its consumer.
        rw [ite_eq_right hqi, hsim.packages]
        by_cases hq : q.producer ∈ L
        · rw [ite_eq_left hq, ite_eq_left (hmem.2 hq)]
          cases hr : S.packages q with
          | none => rfl
          | some r =>
            rw [Option.map_some, Option.map_some]
            cases hst : r.status with
            | consumed d =>
              have hdb : d ≠ b := fun hdb => by
                subst hdb
                obtain ⟨act', h', hmem'⟩ := hS.consumed q r d hr hst
                rw [hb] at h'
                cases h'
                exact hqi hmem'
              by_cases hd : d ∈ L
              · rw [restore_of_mem hst hd, restore_of_mem hst (List.mem_append_left _ hd)]
              · rw [restore_of_not_mem hst hd, restore_of_not_mem hst (by simp [hd, hdb])]
            | live => rw [restore_of_live hst, restore_of_live hst]
            | retired ret => rw [restore_of_retired hst, restore_of_retired hst]
        · rw [ite_eq_right hq, ite_eq_right fun h => hq (hmem.1 h)]
  · show R.activationIds ++ [b] = L ++ [b]
    rw [hsim.activationIds]
  · show R.revision + 1 = (L ++ [b]).length
    rw [hsim.revision, List.length_append]
    rfl

/-- Replaying the rest of a causally ordered list of accepted activations from the
restriction of `S` to a prefix reaches the restriction of `S` to the whole list. -/
theorem sim_fold {S : State} {evidence : Digest → Option Bytes} (hS : WF Δ S)
    (hinv : RunInv accepts H Δ evidence S) {h : List (ActivationId × Activation)}
    (hmem : ∀ x ∈ h, S.activations x.1 = some x.2) (hnodup : (h.map Prod.fst).Nodup)
    (hprefix : ∀ h₁ x h₂, h = h₁ ++ x :: h₂ →
      ∀ p ∈ x.2.trigger.inputs, p.producer ∈ h₁.map Prod.fst) :
    ∀ (h₂ h₁ : List (ActivationId × Activation)) (R : State), h = h₁ ++ h₂ →
      Sim S (h₁.map Prod.fst) R → Closed S (h₁.map Prod.fst) →
      ∃ R', h₂.foldlM (replayStep accepts H Δ evidence) R = some R' ∧
        Sim S (h.map Prod.fst) R'
  | [], h₁, R, hsplit, hsim, _ =>
    ⟨R, rfl, by rw [hsplit, List.append_nil]; exact hsim⟩
  | (b, act) :: h₂, h₁, R, hsplit, hsim, hclosed => by
    have hb : S.activations b = some act :=
      hmem _ (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
    have hbL : b ∉ h₁.map Prod.fst := by
      rw [hsplit, List.map_append, List.map_cons] at hnodup
      exact fun hm => (List.nodup_append.1 hnodup).2.2 b hm b List.mem_cons_self rfl
    have hin := hprefix h₁ (b, act) h₂ hsplit
    obtain ⟨R₁, hstep, hsim₁⟩ := sim_step hS hinv hsim hclosed hb hbL hin
    have hclosed₁ : Closed S (h₁.map Prod.fst ++ [b]) := by
      intro c act' hc hact' p hp
      rcases List.mem_append.1 hc with hc | hc
      · exact List.mem_append_left _ (hclosed c act' hc hact' p hp)
      · rw [List.mem_singleton] at hc
        subst hc
        rw [hb] at hact'
        cases hact'
        exact List.mem_append_left _ (hin p hp)
    have hmap : (h₁ ++ [(b, act)]).map Prod.fst = h₁.map Prod.fst ++ [b] := by simp
    obtain ⟨R', hfold, hsim'⟩ := sim_fold hS hinv hmem hnodup hprefix h₂ (h₁ ++ [(b, act)]) R₁
      (by rw [hsplit]; simp) (by rw [hmap]; exact hsim₁) (by rw [hmap]; exact hclosed₁)
    refine ⟨R', ?_, hsim'⟩
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff]
    exact ⟨R₁, hstep, hfold⟩

end

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
    obtain ⟨act, recs, rfl, hfresh, -, -, hreplay⟩ :=
      Replay.replayStep_of_activate hact fun em hem =>
        hevidence _ (List.mem_append_right _ (List.mem_map_of_mem hem))
    have ih' := ih fun b hb => hevidence b (List.mem_append_left _ hb)
    rw [Replay.replay_eq] at ih' ⊢
    rw [Replay.history_accept (Activation.fresh_not_mem hS hfresh), List.foldlM_append, ih']
    simpa using hreplay S hfresh fun _ _ => rfl

/-- Replay accepts only faithful histories: whatever it accepts is the history of the state it
builds, which is reachable. -/
theorem replay_sound {h : List (ActivationId × Activation)} {evidence : Digest → Option Bytes}
    (hreplay : replay accepts H Δ h evidence = some S) :
    S.history = h ∧ Reachable accepts H Δ S := by
  rw [Replay.replay_eq] at hreplay
  obtain ⟨hhist, hreach⟩ :=
    Replay.foldlM_sound (fun a => by simp [State.initial]) .initial hreplay
  exact ⟨by simpa [State.history, State.initial] using hhist, hreach⟩

/-- A reachable workflow whose revision counts only its activations was reached by
activations alone, under its current definition. -/
theorem activationRun_of_revision {grammar : List Production}
    (h : SysReachable accepts H grammar Δ S) (hrevision : S.revision = S.activationIds.length) :
    ∃ payloads, ActivationRun accepts H Δ S payloads := by
  -- `revision - |A|` never decreases, and only an activation keeps it.
  suffices key : S.activationIds.length ≤ S.revision ∧
      (S.revision = S.activationIds.length → ∃ payloads, ActivationRun accepts H Δ S payloads)
    from key.2 hrevision
  clear hrevision
  induction h with
  | initial => exact ⟨Nat.le_refl _, fun _ => ⟨[], .initial⟩⟩
  | @next Δ₁ Δ₂ S₁ S₂ op hreach hstep ih =>
    have hrev := sysStep_revision hstep
    -- Every transition but an activation keeps the accepted identities.
    suffices hkeep : S₂.activationIds = S₁.activationIds ∨
        ∃ a prop, Δ₂ = Δ₁ ∧ activate accepts H Δ₁ S₁ a prop = some S₂ ∧
          S₂.activationIds.length = S₁.activationIds.length + 1 by
      rcases hkeep with hkeep | ⟨a, prop, rfl, hact, hlen⟩
      · rw [hkeep, hrev]
        exact ⟨Nat.le_succ_of_le ih.1, fun heq => absurd heq (by have := ih.1; omega)⟩
      · rw [hlen, hrev]
        refine ⟨Nat.succ_le_succ ih.1, fun heq => ?_⟩
        obtain ⟨payloads, hrun⟩ := ih.2 (Nat.succ.inj heq)
        exact ⟨_, .activate hrun hact⟩
    cases op with
    | step op =>
      obtain ⟨rfl, hstep'⟩ := Sys.step_eq_some hstep
      cases op with
      | activate a prop =>
        refine .inr ⟨a, prop, rfl, hstep', ?_⟩
        obtain ⟨act, -, records, -, -, rfl⟩ := Common.activate_eq_some hstep'
        simp [State.accept]
      | transfer p e payload =>
        obtain ⟨_, _, -, -, -, -, -, rfl⟩ := Common.transfer_eq_some hstep'
        exact .inl rfl
      | retire p evidence =>
        obtain ⟨_, -, -, -, rfl⟩ := Common.retire_eq_some hstep'
        exact .inl rfl
    | rewrite req evidence =>
      obtain ⟨_, _, -, -, -, -, hids, -⟩ := rewrite_spec (wf_of_sysReachable hreach).2 hstep
      exact .inl hids
    | extend schema contracts =>
      obtain ⟨-, rfl⟩ := extend_spec hstep
      exact .inl rfl

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
      S'.changeLog = S.changeLog ∧ S'.revision = S.revision := by
  have hS := wf_of_reachable hΔ (Replay.reachable_of_run hrun)
  have hinv := Replay.runInv hΔ hrun hevidence
  -- The entries of `h` are the accepted activations, each once.
  have hmem : ∀ x ∈ h, S.activations x.1 = some x.2 := fun x hx =>
    (Replay.mem_history.1 (hperm.mem_iff.1 hx)).2
  have hids : (h.map Prod.fst).Perm S.activationIds := by
    rw [← Replay.history_map_fst fun a ha => (hS.activations_dom a).2 ha]
    exact hperm.map _
  have hnodup : (h.map Prod.fst).Nodup := hids.nodup_iff.2 hS.activationIds_nodup
  -- Every input of an entry was produced by an earlier entry.
  have hprefix : ∀ h₁ x h₂, h = h₁ ++ x :: h₂ →
      ∀ p ∈ x.2.trigger.inputs, p.producer ∈ h₁.map Prod.fst := by
    intro h₁ x h₂ hsplit p hp
    have hx : S.activations x.1 = some x.2 :=
      hmem x (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
    obtain ⟨r, d, hr, -⟩ := hS.inputs x.1 x.2 hx p hp
    obtain ⟨act, o, hact, -⟩ := hS.ownership p r hr
    have hpa : (p.producer, act) ∈ h :=
      hperm.mem_iff.2 (Replay.mem_history.2 ⟨Activation.producer_mem hS hr, hact⟩)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hpa
    have hi' : h[i]? = some (p.producer, act) := by rw [List.getElem?_eq_getElem hi, hget]
    have hj : h[h₁.length]? = some (x.1, x.2) := by
      rw [hsplit]
      simp
    have hlt := hcausal i h₁.length p.producer x.1 act x.2 hi' hj ⟨p, hp, rfl⟩
    rw [hsplit, List.getElem?_append_left hlt] at hi'
    exact List.mem_map_of_mem (f := Prod.fst) (List.mem_of_getElem? hi')
  -- Replay simulates the run on the activations replayed so far.
  have hsim₀ : Replay.Sim S [] (State.initial Δ) :=
    ⟨fun _ => rfl, fun _ => rfl, rfl, hinv.usedNodes.symm, hinv.edgeLog.symm,
      hinv.changeLog.symm, rfl⟩
  obtain ⟨R, hfold, hsim⟩ := Replay.sim_fold hS hinv hmem hnodup hprefix h [] (State.initial Δ)
    rfl hsim₀ fun _ _ hc => nomatch hc
  rw [← Replay.replay_eq] at hfold
  have hR := wf_of_reachable hΔ (replay_sound hfold).2
  have hacts : R.activations = S.activations := by
    funext a
    rw [hsim.activations]
    split
    · rfl
    · rename_i ha
      have ha' : a ∉ S.activationIds := fun ha' => ha (hids.mem_iff.2 ha')
      rw [← hS.activations_dom a] at ha'
      exact (Option.not_isSome_iff_eq_none.1 ha').symm
  have hpkgs : R.packages = S.packages := by
    funext q
    rw [hsim.packages]
    split
    · -- Every consumer is replayed, so no consumption is undone.
      cases hq : S.packages q with
      | none => rfl
      | some r =>
        rw [Option.map_some]
        cases hst : r.status with
        | consumed c =>
          obtain ⟨act, hact, -⟩ := hS.consumed q r c hq hst
          have hc : c ∈ S.activationIds := (hS.activations_dom c).1 (by rw [hact]; rfl)
          rw [Replay.restore_of_mem hst (hids.mem_iff.2 hc)]
        | live => rw [Replay.restore_of_live hst]
        | retired ret => rw [Replay.restore_of_retired hst]
    · rename_i hq
      cases hq' : S.packages q with
      | none => rfl
      | some r => exact absurd (hids.mem_iff.2 (Activation.producer_mem hS hq')) hq
  refine ⟨R, hfold, hacts, hpkgs, hsim.activationIds ▸ hids, ?_, hsim.usedNodes, hsim.edgeLog,
    hsim.changeLog, ?_⟩
  · refine (List.perm_ext_iff_of_nodup hR.packageIds_nodup hS.packageIds_nodup).2 fun q => ?_
    rw [← hR.packages_dom, ← hS.packages_dom, hpkgs]
  · rw [hsim.revision, hids.length_eq, hinv.revision]

end Ontography.Proofs
