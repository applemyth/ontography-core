import Ontography.Invariants

/-!
# Lemmas for activation

Inversion of `activate` and views of `State.accept`, for the preservation proof in
`Ontography.Proofs.Activation`.

`activate_inv` reduces a successful activation to an `Admissible` bundle: a fresh identity, a
node of the graph, the facts its trigger's admission establishes, and an `OutSpec` for each
output. `pkg_cases` sorts every package of the successor into a new output, a consumed input,
or an untouched record.
-/

namespace Ontography.Proofs.Activation

/-! ## Generic facts -/

/-- The monadic `guard` succeeds in `Option` exactly when its condition holds. -/
theorem guard_eq_some {p : Prop} [Decidable p] {u : Unit} :
    (guard p : Option Unit) = some u ↔ p := by
  by_cases hp : p <;> simp [guard, hp]

/-- A successful `mapM` in `Option` relates its input and output lists elementwise. -/
theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      (∀ x ∈ l, ∃ y ∈ l', f x = some y) ∧ ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | x :: xs, l', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨ih₁, ih₂⟩ := mapM_some hys
    constructor
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨y, List.mem_cons_self, hy⟩
      · obtain ⟨w, hw, hfw⟩ := ih₁ z hz
        exact ⟨w, List.mem_cons_of_mem _ hw, hfw⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨x, List.mem_cons_self, hy⟩
      · obtain ⟨w, hw, hfw⟩ := ih₂ z hz
        exact ⟨w, List.mem_cons_of_mem _ hw, hfw⟩

theorem setEq_trans {α : Type} {a b c : List α} (h₁ : SetEq a b) (h₂ : SetEq b c) : SetEq a c :=
  ⟨List.Subset.trans h₁.1 h₂.1, List.Subset.trans h₂.2 h₁.2⟩

theorem setEq_symm {α : Type} {a b : List α} (h : SetEq a b) : SetEq b a := ⟨h.2, h.1⟩

/-! ## Lookups in a definition -/

/-- A found edge is an edge of the graph with the requested identity. -/
theorem edge?_some {Δ : Definition} {e : EdgeId} {edge : Edge} (h : Δ.edge? e = some edge) :
    edge ∈ Δ.edges ∧ edge.id = e :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A found node definition is listed and names the requested node. -/
theorem nodeDef?_some {Δ : Definition} {v : NodeId} {nd : NodeDef}
    (h : Δ.nodeDef? v = some nd) : nd ∈ Δ.nodeDefs ∧ nd.node = v :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A found contract is registered under the requested identity. -/
theorem contract?_some {Δ : Definition} {c : ContractId} {ct : Contract}
    (h : Δ.contract? c = some ct) : ct ∈ Δ.contracts ∧ ct.id = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- An edge of the graph is an incoming edge of its target. -/
theorem mem_incoming {Δ : Definition} {edge : Edge} (h : edge ∈ Δ.edges) :
    edge.id ∈ Δ.incoming edge.target :=
  List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-! ## Outputs -/

/-- The birth metadata `o` and the record `r` of one admissible output of an activation at
`v`: they agree, the record is live and schema-closed, and it is either outbound or delivered
over an edge leaving `v`. -/
structure OutSpec (Δ : Definition) (v : NodeId) (o : Output) (r : PackageRecord) : Prop where
  objectType : r.objectType = o.objectType
  authority : r.authority = o.authority
  digest : r.digest = o.digest
  producerNode : r.producerNode = v
  status : r.status = .live
  objectType_mem : r.objectType ∈ Δ.schema.objectTypes
  authority_sub : r.authority ⊆ Δ.schema.tags
  route : (o.edge = none ∧ r.delivery = none) ∨
    ∃ edge ∈ Δ.edges, edge.source = v ∧ o.edge = some edge.id ∧
      r.delivery = some ⟨edge.id, edge.target⟩

/-- An admitted emission yields an output and a record satisfying `OutSpec`. -/
theorem emission_spec {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
    {Δ : Definition} (hΔ : Δ.Admitted) {v : NodeId} {α : Authority} {em : Emission}
    {x : Output × PackageRecord} (h : emission? accepts H Δ v α em = some x) :
    OutSpec Δ v x.1 x.2 := by
  obtain ⟨dest, auth, payload⟩ := em
  cases auth <;> cases dest <;>
    simp only [emission?, bind, Option.bind_eq_some_iff, guard_eq_some, pure,
      Option.some.injEq] at h
  · obtain ⟨_, hβ, _, _, edge, hedge, _, hsrc, ed, _, _, _, c, hc, _, _, rfl⟩ := h
    obtain ⟨hmem, rfl⟩ := edge?_some hedge
    exact ⟨rfl, rfl, rfl, rfl, rfl, (hΔ.contracts_wf c (contract?_some hc).1).2, hβ,
      .inr ⟨edge, hmem, hsrc, rfl, rfl⟩⟩
  · obtain ⟨_, hβ, _, _, _, ho, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ho, hβ, .inl ⟨rfl, rfl⟩⟩
  · obtain ⟨_, hβ, _, _, edge, hedge, _, hsrc, ed, _, _, _, c, hc, _, _, rfl⟩ := h
    obtain ⟨hmem, rfl⟩ := edge?_some hedge
    exact ⟨rfl, rfl, rfl, rfl, rfl, (hΔ.contracts_wf c (contract?_some hc).1).2, hβ,
      .inr ⟨edge, hmem, hsrc, rfl, rfl⟩⟩
  · obtain ⟨_, hβ, _, _, _, ho, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ho, hβ, .inl ⟨rfl, rfl⟩⟩

/-! ## Triggers -/

/-- What an admissible input of a trigger at `v` governed by `α` satisfies in `S`. -/
def InputOK (S : State) (v : NodeId) (α : Authority) (p : PackageId) : Prop :=
  ∃ r d, S.packages p = some r ∧ r.status = .live ∧ r.delivery = some d ∧ d.receiver = v ∧
    SetEq r.authority α

/-- An input that `inputEdge?` accepts satisfies `InputOK`. -/
theorem inputEdge_spec {S : State} {v : NodeId} {α : Authority} {p : PackageId} {e : EdgeId}
    (h : inputEdge? S v α p = some e) : InputOK S v α p := by
  simp only [inputEdge?, bind, Option.bind_eq_some_iff, guard_eq_some] at h
  obtain ⟨r, hr, _, hlive, d, hd, _, hrecv, _, hset, _⟩ := h
  exact ⟨r, d, hr, hlive, hd, hrecv, hset⟩

/-- An admitted package trigger is a nonempty set, and each input satisfies `InputOK` for the
returned node and authority. -/
theorem packageTrigger_spec {Δ : Definition} {S : State} {I : List PackageId} {v : NodeId}
    {α : Authority} (h : packageTrigger? Δ S I = some (v, α)) :
    I ≠ [] ∧ I.Nodup ∧ ∀ p ∈ I, InputOK S v α p := by
  simp only [packageTrigger?, bind, Option.bind_eq_some_iff, guard_eq_some] at h
  obtain ⟨p₀, hp₀, r₀, _, d₀, _, _, hnodup, edges, hedges, _, _, nd, _, h⟩ := h
  have hva : d₀.receiver = v ∧ r₀.authority = α := by
    split at h <;>
      simp only [Option.bind_eq_some_iff, guard_eq_some, exists_const, pure,
        Option.some.injEq, Prod.mk.injEq] at h <;>
      exact h.2
  obtain ⟨rfl, rfl⟩ := hva
  refine ⟨fun hI => by simp [hI] at hp₀, hnodup, fun p hp => ?_⟩
  obtain ⟨e, _, he⟩ := (mapM_some hedges).1 p hp
  exact inputEdge_spec he

/-- The facts a trigger's admission establishes. -/
structure TriggerSpec (Δ : Definition) (S : State) (v : NodeId) (α : Authority) (t : Trigger) :
    Prop where
  pkgs_ne : ∀ I, t = .pkgs I → I ≠ []
  pkgs_nodup : ∀ I, t = .pkgs I → I.Nodup
  orig_node : ∀ w β, t = .orig w β → v = w
  orig_sub : ∀ w β, t = .orig w β → β ⊆ Δ.schema.tags
  inputs : ∀ p ∈ t.inputs, InputOK S v α p

/-- An admitted trigger satisfies `TriggerSpec` for the node and authority it returns. -/
theorem trigger_spec {Δ : Definition} {S : State} {t : Trigger} {v : NodeId} {α : Authority}
    (h : trigger? Δ S t = some (v, α)) : TriggerSpec Δ S v α t := by
  cases t with
  | orig w β =>
    simp only [trigger?, rootTrigger?, bind, Option.bind_eq_some_iff, guard_eq_some, pure,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, hsub, _, _, _, _, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _ h
      cases h
    · intro _ h
      cases h
    · intro _ _ h
      cases h
      rfl
    · intro _ _ h
      cases h
      exact hsub
    · intro _ h
      simp [Trigger.inputs] at h
  | pkgs I =>
    obtain ⟨hne, hnodup, hin⟩ := packageTrigger_spec h
    refine ⟨?_, ?_, ?_, ?_, hin⟩
    · intro _ h
      cases h
      exact hne
    · intro _ h
      cases h
      exact hnodup
    · intro _ _ h
      cases h
    · intro _ _ h
      cases h

/-! ## Inversion of `activate` -/

/-- What the premises of `activate` establish about the fresh identity `a`, the recorded
activation `act` governed by `α`, and its admitted outputs `outs`. -/
structure Admissible (Δ : Definition) (S : State) (a : ActivationId) (act : Activation)
    (α : Authority) (outs : List (Output × PackageRecord)) : Prop where
  fresh : S.activations a = none
  node_mem : act.node ∈ Δ.nodes
  trigger : TriggerSpec Δ S act.node α act.trigger
  outputs_eq : act.outputs = outs.map Prod.fst
  outputs : ∀ x ∈ outs, OutSpec Δ act.node x.1 x.2

/-- A successful activation accepts an admissible activation record and its outputs. -/
theorem activate_inv {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
    {Δ : Definition} {S S' : State} {a : ActivationId} {prop : Proposal} (hΔ : Δ.Admitted)
    (h : activate accepts H Δ S a prop = some S') :
    ∃ act α outs, Admissible Δ S a act α outs ∧ S' = S.accept a act (outs.map Prod.snd) := by
  simp only [activate, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const, pure,
    Option.some.injEq] at h
  obtain ⟨hfresh, ⟨v, α⟩, htrig, nd, hnd, _, outs, houts, rfl⟩ := h
  refine ⟨⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩, α, outs,
    ⟨hfresh, ?_, trigger_spec htrig, rfl, ?_⟩, rfl⟩
  · obtain ⟨hmem, rfl⟩ := nodeDef?_some hnd
    exact hΔ.nodeDefs_nodes nd hmem
  · intro x hx
    obtain ⟨em, _, hem⟩ := (mapM_some houts).2 x hx
    exact emission_spec hΔ hem

/-! ## The accepted state -/

section Accept

variable {S : State} {a : ActivationId} {act : Activation} {recs : List PackageRecord}

theorem accept_activations {b : ActivationId} :
    (S.accept a act recs).activations b = if b = a then some act else S.activations b := rfl

theorem accept_packages {q : PackageId} :
    (S.accept a act recs).packages q =
      if q.producer = a then recs[q.output]?
      else if q ∈ act.trigger.inputs then
        (S.packages q).map fun r => { r with status := .consumed a }
      else S.packages q := rfl

theorem accept_output {q : PackageId} :
    (S.accept a act recs).output? q =
      if q.producer = a then act.outputs[q.output]? else S.output? q := by
  unfold State.output?
  rw [accept_activations]
  split <;> simp

end Accept

/-! ## Facts about the pre-state -/

section Pre

variable {Δ : Definition} {S : State} {a : ActivationId}

/-- By ownership, no recorded package has a fresh identity as its producer. -/
theorem producer_ne (hS : WF Δ S) (hfresh : S.activations a = none) {p : PackageId}
    {r : PackageRecord} (h : S.packages p = some r) : p.producer ≠ a := by
  obtain ⟨_, _, hact, _⟩ := hS.ownership p r h
  intro hp
  rw [hp, hfresh] at hact
  cases hact

/-- The producer of a recorded package is an accepted activation. -/
theorem producer_mem (hS : WF Δ S) {p : PackageId} {r : PackageRecord}
    (h : S.packages p = some r) : p.producer ∈ S.activationIds := by
  obtain ⟨_, _, hact, _⟩ := hS.ownership p r h
  exact (hS.activations_dom _).mp (by rw [hact]; rfl)

theorem fresh_not_mem (hS : WF Δ S) (hfresh : S.activations a = none) :
    a ∉ S.activationIds := by
  rw [← hS.activations_dom a, hfresh]
  simp

theorem packages_of_mem (hS : WF Δ S) {p : PackageId} (hp : p ∈ S.packageIds) :
    ∃ r, S.packages p = some r :=
  Option.isSome_iff_exists.mp ((hS.packages_dom p).mpr hp)

end Pre

/-! ## The successor of an admissible activation -/

section Successor

variable {Δ : Definition} {S : State} {a : ActivationId} {act : Activation} {α : Authority}
  {outs : List (Output × PackageRecord)}

/-- Every package of the successor is a new output, a consumed input, or untouched. -/
theorem pkg_cases (hA : Admissible Δ S a act α outs) {p : PackageId}
    {r : PackageRecord} (h : (S.accept a act (outs.map Prod.snd)).packages p = some r) :
    (∃ o, p.producer = a ∧ outs[p.output]? = some (o, r) ∧ OutSpec Δ act.node o r) ∨
    (∃ r₀, p.producer ≠ a ∧ p ∈ act.trigger.inputs ∧ S.packages p = some r₀ ∧
      r₀.status = .live ∧ SetEq r₀.authority α ∧ r = { r₀ with status := .consumed a }) ∨
    (p.producer ≠ a ∧ p ∉ act.trigger.inputs ∧ S.packages p = some r) := by
  rw [accept_packages] at h
  by_cases hpa : p.producer = a
  · rw [ite_eq_left hpa, List.getElem?_map] at h
    obtain ⟨⟨o, r'⟩, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨o, hpa, hx, hA.outputs _ (List.mem_of_getElem? hx)⟩
  · rw [ite_eq_right hpa] at h
    by_cases hin : p ∈ act.trigger.inputs
    · rw [ite_eq_left hin] at h
      obtain ⟨r₀, _, h0, hlive, _, _, hauth⟩ := hA.trigger.inputs p hin
      rw [h0, Option.map_some, Option.some.injEq] at h
      exact .inr (.inl ⟨r₀, hpa, hin, h0, hlive, hauth, h.symm⟩)
    · rw [ite_eq_right hin] at h
      exact .inr (.inr ⟨hpa, hin, h⟩)

/-- A package that is not live keeps its record. -/
theorem accept_of_not_live (hS : WF Δ S) (hA : Admissible Δ S a act α outs) {p : PackageId}
    {r : PackageRecord} (h : S.packages p = some r) (hr : r.status ≠ .live) :
    (S.accept a act (outs.map Prod.snd)).packages p = some r := by
  have hin : p ∉ act.trigger.inputs := fun hin => by
    obtain ⟨r₀, _, h0, hlive, _⟩ := hA.trigger.inputs p hin
    rw [h] at h0
    cases h0
    exact hr hlive
  rw [accept_packages, ite_eq_right (producer_ne hS hA.fresh h), ite_eq_right hin, h]

/-- A retired package of the successor is retired, unchanged, in the pre-state. -/
theorem pre_of_retired (hA : Admissible Δ S a act α outs) {p : PackageId}
    {r : PackageRecord} {ret : Retirement}
    (h : (S.accept a act (outs.map Prod.snd)).packages p = some r)
    (hr : r.status = .retired ret) : S.packages p = some r := by
  rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, _, _, _, rfl⟩ | ⟨_, _, h0⟩
  · rw [hspec.status] at hr
    cases hr
  · cases hr
  · exact h0

/-- Acceptance keeps every accepted activation. -/
theorem accept_activations_isSome {b : ActivationId} (hb : (S.activations b).isSome) :
    ((S.accept a act (outs.map Prod.snd)).activations b).isSome := by
  rw [accept_activations]
  split
  · rfl
  · exact hb

theorem isExplicitTransfer_old (hS : WF Δ S) (hA : Admissible Δ S a act α outs)
    {p : PackageId} (hp : p ∈ S.packageIds) :
    (S.accept a act (outs.map Prod.snd)).isExplicitTransfer p = S.isExplicitTransfer p := by
  obtain ⟨r, hr⟩ := packages_of_mem hS hp
  have hpa := producer_ne hS hA.fresh hr
  unfold State.isExplicitTransfer
  rw [accept_output, ite_eq_right hpa, accept_packages, ite_eq_right hpa, hr]
  by_cases hin : p ∈ act.trigger.inputs
  · rw [ite_eq_left hin, Option.map_some]
    cases S.output? p <;> rfl
  · rw [ite_eq_right hin]

theorem isExplicitTransfer_new (hA : Admissible Δ S a act α outs) {i : Nat}
    (hi : i < outs.length) :
    (S.accept a act (outs.map Prod.snd)).isExplicitTransfer ⟨a, i⟩ = false := by
  have hspec := hA.outputs _ (List.getElem_mem hi)
  unfold State.isExplicitTransfer
  rw [accept_output, ite_eq_left rfl, accept_packages, ite_eq_left rfl, hA.outputs_eq]
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some]
  rcases hspec.route with ⟨he, hd⟩ | ⟨_, _, _, he, _⟩
  · simp [hd]
  · simp [he]

theorem isExplicitRetirement_old (hS : WF Δ S) (hA : Admissible Δ S a act α outs)
    {p : PackageId} (hp : p ∈ S.packageIds) :
    (S.accept a act (outs.map Prod.snd)).isExplicitRetirement p = S.isExplicitRetirement p := by
  obtain ⟨r, hr⟩ := packages_of_mem hS hp
  have hpa := producer_ne hS hA.fresh hr
  unfold State.isExplicitRetirement
  rw [accept_packages, ite_eq_right hpa]
  by_cases hin : p ∈ act.trigger.inputs
  · obtain ⟨r₀, _, h0, hlive, _⟩ := hA.trigger.inputs p hin
    rw [hr] at h0
    cases h0
    rw [ite_eq_left hin, hr, Option.map_some]
    simp [PackageRecord.retirement?, hlive]
  · rw [ite_eq_right hin]

theorem isExplicitRetirement_new (hA : Admissible Δ S a act α outs) {i : Nat}
    (hi : i < outs.length) :
    (S.accept a act (outs.map Prod.snd)).isExplicitRetirement ⟨a, i⟩ = false := by
  have hspec := hA.outputs _ (List.getElem_mem hi)
  unfold State.isExplicitRetirement
  rw [accept_packages, ite_eq_left rfl]
  simp [List.getElem?_map, List.getElem?_eq_getElem hi, PackageRecord.retirement?, hspec.status]

/-- Activation adds no explicit transfer: every new output is outbound or born delivered, and
no existing package changes its delivery or birth metadata. -/
theorem explicitTransfers_eq (hS : WF Δ S) (hA : Admissible Δ S a act α outs) :
    (S.accept a act (outs.map Prod.snd)).explicitTransfers = S.explicitTransfers := by
  unfold State.explicitTransfers
  show (S.packageIds ++ _).countP _ = _
  rw [List.countP_append]
  have hnew : ((List.range (outs.map Prod.snd).length).map (PackageId.mk a)).countP
      (S.accept a act (outs.map Prod.snd)).isExplicitTransfer = 0 := by
    rw [List.countP_eq_zero]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    rw [List.mem_range, List.length_map] at hi
    simp [isExplicitTransfer_new hA hi]
  rw [hnew, Nat.add_zero]
  exact List.countP_congr fun p hp => by rw [isExplicitTransfer_old hS hA hp]

/-- Activation adds no explicit retirement: new outputs are live, and consumed inputs were
live. -/
theorem explicitRetirements_eq (hS : WF Δ S) (hA : Admissible Δ S a act α outs) :
    (S.accept a act (outs.map Prod.snd)).explicitRetirements = S.explicitRetirements := by
  unfold State.explicitRetirements
  show (S.packageIds ++ _).countP _ = _
  rw [List.countP_append]
  have hnew : ((List.range (outs.map Prod.snd).length).map (PackageId.mk a)).countP
      (S.accept a act (outs.map Prod.snd)).isExplicitRetirement = 0 := by
    rw [List.countP_eq_zero]
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    rw [List.mem_range, List.length_map] at hi
    simp [isExplicitRetirement_new hA hi]
  rw [hnew, Nat.add_zero]
  exact List.countP_congr fun p hp => by rw [isExplicitRetirement_old hS hA hp]

end Successor

end Ontography.Proofs.Activation
