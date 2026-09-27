import Ontography.Invariants

/-!
# General lemmas

Facts the invariant proofs share: point updates, counting over duplicate-free lists, lookups
in a definition, and inversion of the `Option` monad the rules are written in.

The last section proves once that replacing the record of one live package and advancing the
revision preserves every field of `WF` the replacement does not touch. Transfer and explicit
retirement both have this shape, so each discharges only the obligations of the record it
changes.
-/

namespace Ontography.Proofs.Common

/-! ## Point updates -/

section Update

variable {α β : Type} [DecidableEq α] {f : α → Option β} {k x : α} {v w : β}

@[simp] theorem update_self : update f k v k = some v := by simp [update]

theorem update_of_ne (h : x ≠ k) : update f k v x = f x := by simp [update, h]

theorem update_eq_some : update f k v x = some w ↔ x = k ∧ v = w ∨ x ≠ k ∧ f x = some w := by
  by_cases h : x = k <;> simp [update, h]

/-- Updating a key that is already present leaves the domain unchanged. -/
theorem isSome_update (hk : (f k).isSome) : (update f k v x).isSome = (f x).isSome := by
  by_cases h : x = k
  · subst h; simp [hk]
  · simp [update_of_ne h]

end Update

/-! ## Counting -/

/-- Turning a predicate on at exactly one element of a duplicate-free list adds one to its
count. -/
theorem countP_eq_succ {α : Type} {l : List α} {x : α} {P Q : α → Bool} (hl : l.Nodup)
    (hx : x ∈ l) (hP : P x = false) (hQ : Q x = true) (h : ∀ y, y ≠ x → Q y = P y) :
    l.countP Q = l.countP P + 1 := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.nodup_cons] at hl
    by_cases hyx : y = x
    · subst hyx
      have : ys.countP Q = ys.countP P :=
        List.countP_congr fun z hz => by rw [h z fun hzy => hl.1 (hzy ▸ hz)]
      simp [hP, hQ, this]
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.1 hx with hxy | hx'
        · exact absurd hxy.symm hyx
        · exact hx'
      simp [List.countP_cons, h y hyx, ih hl.2 hx']
      omega

/-! ## Lookups in a definition -/

section Lookup

variable {Δ : Definition}

theorem edge?_mem {e : EdgeId} {edge : Edge} (h : Δ.edge? e = some edge) :
    edge ∈ Δ.edges ∧ edge.id = e :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem nodeDef?_mem {v : NodeId} {d : NodeDef} (h : Δ.nodeDef? v = some d) :
    d ∈ Δ.nodeDefs ∧ d.node = v :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem edgeDef?_mem {e : EdgeId} {d : EdgeDef} (h : Δ.edgeDef? e = some d) :
    d ∈ Δ.edgeDefs ∧ d.edge = e :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem contract?_mem {c : ContractId} {k : Contract} (h : Δ.contract? c = some k) :
    k ∈ Δ.contracts ∧ k.id = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem ceiling?_mem {v : NodeId} {c : Authority} (h : Δ.ceiling? v = some c) :
    ∃ root ∈ Δ.roots, root.node = v ∧ root.ceiling = c := by
  obtain ⟨root, hroot, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨root, List.mem_of_find?_eq_some hroot, by simpa using List.find?_some hroot, rfl⟩

theorem mem_incoming {e : EdgeId} {v : NodeId} :
    e ∈ Δ.incoming v ↔ ∃ edge ∈ Δ.edges, edge.target = v ∧ edge.id = e := by
  simp [Definition.incoming, and_assoc]

end Lookup

/-! ## Option inversion -/

/-- A guard in the `Option` monad succeeds exactly when its condition holds. With
`Option.bind_eq_some_iff` this inverts a rule into its premises and its successor. -/
@[simp] theorem guard_eq_some {p : Prop} [Decidable p] {u : Unit} :
    (guard p : Option Unit) = some u ↔ p := by
  by_cases h : p <;> simp [guard, h]

/-! ## Replacing one record -/

section Record

variable {Δ : Definition} {S : State} {p : PackageId} {r r' : PackageRecord}

/-- `S` with the record of `p` replaced by `r'` and the revision advanced once: the successor
shape of transfer and explicit retirement. -/
def setRecord (S : State) (p : PackageId) (r' : PackageRecord) : State :=
  { S with packages := update S.packages p r', revision := S.revision + 1 }

@[simp] theorem setRecord_packages : (setRecord S p r').packages = update S.packages p r' := rfl

@[simp] theorem setRecord_packageIds : (setRecord S p r').packageIds = S.packageIds := rfl

@[simp] theorem output?_setRecord : (setRecord S p r').output? = S.output? := rfl

theorem setRecord_packages_eq_some {q : PackageId} {x : PackageRecord} :
    (setRecord S p r').packages q = some x ↔ q = p ∧ r' = x ∨ q ≠ p ∧ S.packages q = some x :=
  update_eq_some

/-! The revision-accounting counts change only through `p`. -/

theorem isExplicitTransfer_setRecord_of_ne {q : PackageId} (hq : q ≠ p) :
    (setRecord S p r').isExplicitTransfer q = S.isExplicitTransfer q := by
  simp only [State.isExplicitTransfer, setRecord_packages, output?_setRecord, update_of_ne hq]

theorem isExplicitRetirement_setRecord_of_ne {q : PackageId} (hq : q ≠ p) :
    (setRecord S p r').isExplicitRetirement q = S.isExplicitRetirement q := by
  simp only [State.isExplicitRetirement, setRecord_packages, update_of_ne hq]

/-- Keeping the delivery of `p` keeps the explicit-transfer count. -/
theorem explicitTransfers_setRecord (hr : S.packages p = some r)
    (hd : r'.delivery = r.delivery) :
    (setRecord S p r').explicitTransfers = S.explicitTransfers := by
  unfold State.explicitTransfers
  rw [setRecord_packageIds]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq
    simp only [State.isExplicitTransfer, setRecord_packages, output?_setRecord, update_self, hr]
    cases S.output? q <;> simp [hd]
  · exact isExplicitTransfer_setRecord_of_ne hq

/-- Keeping the status of `p` keeps the explicit-retirement count. -/
theorem explicitRetirements_setRecord (hr : S.packages p = some r)
    (hs : r'.status = r.status) :
    (setRecord S p r').explicitRetirements = S.explicitRetirements := by
  unfold State.explicitRetirements
  rw [setRecord_packageIds]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq
    simp only [State.isExplicitRetirement, setRecord_packages, update_self, hr,
      PackageRecord.retirement?, hs]
  · exact isExplicitRetirement_setRecord_of_ne hq

/-- Making the recorded package `p` an explicit transfer adds one to the count. -/
theorem explicitTransfers_setRecord_succ (hS : WF Δ S) (hr : S.packages p = some r)
    (hbefore : S.isExplicitTransfer p = false)
    (hafter : (setRecord S p r').isExplicitTransfer p = true) :
    (setRecord S p r').explicitTransfers = S.explicitTransfers + 1 :=
  countP_eq_succ hS.packageIds_nodup ((hS.packages_dom p).1 (by simp [hr])) hbefore hafter
    fun _ hq => isExplicitTransfer_setRecord_of_ne hq

/-- Making the recorded package `p` an explicit retirement adds one to the count. -/
theorem explicitRetirements_setRecord_succ (hS : WF Δ S) (hr : S.packages p = some r)
    (hbefore : S.isExplicitRetirement p = false)
    (hafter : (setRecord S p r').isExplicitRetirement p = true) :
    (setRecord S p r').explicitRetirements = S.explicitRetirements + 1 :=
  countP_eq_succ hS.packageIds_nodup ((hS.packages_dom p).1 (by simp [hr])) hbefore hafter
    fun _ hq => isExplicitRetirement_setRecord_of_ne hq

/-- Replacing the record of a live package `p` by `r'`, which keeps its immutable facts,
preserves `WF` given the obligations of `r'` itself: its status is not a consumption, its
delivery is a logged edge from the producer's node and agrees with its birth edge, a
retirement it carries satisfies I4 and stamps apart from every other explicit retirement, a
live `r'` satisfies I5, and the revision-accounting counts grow by one in all. -/
theorem wf_setRecord (hS : WF Δ S) (hr : S.packages p = some r) (hlive : r.status = .live)
    (hfacts : r'.objectType = r.objectType ∧ r'.authority = r.authority ∧
      r'.digest = r.digest ∧ r'.producerNode = r.producerNode)
    (hconsumed : ∀ b, r'.status ≠ .consumed b)
    (hdelivery : ∀ d, r'.delivery = some d →
      (⟨d.edge, r.producerNode, d.receiver⟩ : Edge) ∈ S.edgeLog)
    (hbirth : ∀ o e, S.output? p = some o → o.edge = some e → ∃ v, r'.delivery = some ⟨e, v⟩)
    (hretirement : ∀ ret, r'.status = .retired ret →
      (ret.reason = .noAcceptingEdge → r'.delivery = none) ∧
      (ret.reason = .routeRemoved → r'.delivery ≠ none) ∧
      (ret.evidence ≠ none → ret.reason = .explicit) ∧
      (∀ a, ret.evidence = some a → (S.activations a).isSome) ∧
      1 ≤ ret.revision ∧ ret.revision ≤ S.revision + 1 ∧
      (ret.reason = .holderRemoved → r'.holder ∉ Δ.nodes) ∧
      (ret.reason = .explicit ↔ ret.revision ∉ S.changeLog))
    (hstamps : ∀ ρ, r'.status = .retired ρ → ρ.reason = .explicit →
      ∀ q s σ, S.packages q = some s → s.status = .retired σ → σ.reason = .explicit →
        σ.revision ≠ ρ.revision)
    (hcustody : r'.status = .live → r'.holder ∈ Δ.nodes)
    (hroutes : ∀ d nd, r'.status = .live → r'.delivery = some d →
      Δ.nodeDef? d.receiver = some nd → nd.ingress = .all → d.edge ∈ Δ.incoming d.receiver)
    (hcount : (setRecord S p r').explicitTransfers + (setRecord S p r').explicitRetirements =
      S.explicitTransfers + S.explicitRetirements + 1) :
    WF Δ (setRecord S p r') := by
  obtain ⟨hobj, hauth, hdig, hnode⟩ := hfacts
  have hp : (S.packages p).isSome := by simp [hr]
  -- Every record after the replacement shares its immutable facts with one before it.
  have facts : ∀ q x, (setRecord S p r').packages q = some x → ∃ y, S.packages q = some y ∧
      x.objectType = y.objectType ∧ x.authority = y.authority ∧ x.digest = y.digest ∧
      x.producerNode = y.producerNode := by
    intro q x hx
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact ⟨r, hr, hobj, hauth, hdig, hnode⟩
    · exact ⟨x, hx, rfl, rfl, rfl, rfl⟩
  refine
    { activationIds_nodup := hS.activationIds_nodup
      activations_dom := hS.activations_dom
      packageIds_nodup := hS.packageIds_nodup
      packages_dom := fun q => by
        simpa [setRecord, isSome_update hp] using hS.packages_dom q
      ownership := ?_
      outputs_recorded := fun a act ha i hi => by
        simpa [setRecord, isSome_update hp] using hS.outputs_recorded a act ha i hi
      consumed := ?_
      inputs := ?_
      join_authority := ?_
      triggers := hS.triggers
      delivery := ?_
      birth_edge := ?_
      retirement := ?_
      explicit_stamps := ?_
      custody := ?_
      all_routes := ?_
      revision := ?_
      changeLog_nodup := hS.changeLog_nodup
      changeLog_le := fun n hn => by
        have := hS.changeLog_le n hn
        exact ⟨this.1, by simp only [setRecord]; omega⟩
      used_nodes := hS.used_nodes
      edge_log := hS.edge_log
      edge_log_ids := hS.edge_log_ids
      activation_nodes_used := hS.activation_nodes_used
      edge_log_nodes := hS.edge_log_nodes
      used_nonempty := hS.used_nonempty
      causal_order := ?_
      schema_closure := ?_ }
  · -- I1
    intro q x hx
    obtain ⟨y, hy, h₁, h₂, h₃, h₄⟩ := facts q x hx
    obtain ⟨act, o, hact, ho, h₅, h₆, h₇, h₈⟩ := hS.ownership q y hy
    exact ⟨act, o, hact, ho, h₁.trans h₅, h₂.trans h₆, h₃.trans h₇, h₄.trans h₈⟩
  · -- I2: a consumed record is not the replacement.
    intro q x b hx hs
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact absurd hs (hconsumed b)
    · exact hS.consumed q x b hx hs
  · -- I2: an input is consumed, so it is not the live `p`.
    intro b act hact q hq
    obtain ⟨y, d, hy, hs, hd, hrecv⟩ := hS.inputs b act hact q hq
    have hqp : q ≠ p := by
      rintro rfl
      rw [hr] at hy
      cases hy
      rw [hlive] at hs
      cases hs
    exact ⟨y, d, by simpa [setRecord, update_of_ne hqp] using hy, hs, hd, hrecv⟩
  · -- I2
    intro b act hact q hq q' hq' x x' hx hx'
    obtain ⟨y, hy, -, hya, -⟩ := facts q x hx
    obtain ⟨y', hy', -, hya', -⟩ := facts q' x' hx'
    rw [hya, hya']
    exact hS.join_authority b act hact q hq q' hq' y y' hy hy'
  · -- I3
    intro q x d hx hd
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · rw [hnode]
      exact hdelivery d hd
    · exact hS.delivery q x d hx hd
  · -- I3
    intro q x o e hx ho he
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact hbirth o e ho he
    · exact hS.birth_edge q x o e hx ho he
  · -- I4
    intro q x ret hx hs
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact hretirement ret hs
    · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hS.retirement q x ret hx hs
      exact ⟨h₁, h₂, h₃, h₄, h₅, by simp only [setRecord]; omega, h₇, h₈⟩
  · -- I4
    intro q q' x x' ρ σ hx hx' hs hs' he he' hrev
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hy⟩ <;>
      rcases setRecord_packages_eq_some.1 hx' with ⟨rfl, rfl⟩ | ⟨-, hy'⟩
    · rfl
    · exact absurd hrev.symm (hstamps ρ hs he q' x' σ hy' hs' he')
    · exact absurd hrev (hstamps σ hs' he' q x ρ hy hs he)
    · exact hS.explicit_stamps q q' x x' ρ σ hy hy' hs hs' he he' hrev
  · -- I5
    intro q x hx hs
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact hcustody hs
    · exact hS.custody q x hx hs
  · -- I5
    intro q x d nd hx hs hd hnd hall
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact hroutes d nd hs hd hnd hall
    · exact hS.all_routes q x d nd hx hs hd hnd hall
  · -- I6
    have := hS.revision
    simp only [setRecord, State.definitionChanges] at hcount this ⊢
    omega
  · -- Causal acyclicity: a consumed record is not the replacement.
    intro q x b hx hs
    rcases setRecord_packages_eq_some.1 hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact absurd hs (hconsumed b)
    · exact hS.causal_order q x b hx hs
  · -- Schema closure
    intro q x hx
    obtain ⟨y, hy, hyo, hya, -⟩ := facts q x hx
    rw [hyo, hya]
    exact hS.schema_closure q y hy

end Record

end Ontography.Proofs.Common
