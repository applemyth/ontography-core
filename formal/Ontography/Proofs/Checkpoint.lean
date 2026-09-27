import Ontography.Checkpoint
import Ontography.Proofs.Basic

/-!
# Checkpoint restoration

`CheckpointValid` reads a state only through its checkpoint. Besides the recorded components,
it reads the birth metadata `output?`, the revision-accounting counts, and the causal history,
and these are functions of the activation map, the package map, and the package list. Two
states that record the same checkpoint therefore pass or fail together.

Every well-formed state passes. Most checks are fields of `WF`, acyclicity is
`causal_acyclic`, and the rest follow from the logs `WF` keeps. A delivery's edge is logged,
so its identity is used. A current edge is logged too, and logged identities are unique, so a
delivery agrees with its edge's current incidence and with every other delivery over that
edge. A logged edge's endpoints are used, so some node identity is used once an edge identity
is. The change log is a duplicate-free list of `definitionChanges` stamps that holds every
structural stamp and no explicit one.

Conversely, every checkpoint that passes is recorded, up to acceptance order, by a well-formed
state. That state keeps the maps, the lifetime identities, and the counts, and rebuilds the
rest:
- The acceptance order is a causal order of the activations. One exists because the causal
  history is acyclic and finite: some activation consumed no output of another, so it can go
  first, and the rest are ordered in turn.
- The incidence log gives each used edge identity its current incidence, else the endpoints
  on which every delivery over it agrees, else some used node for both endpoints.
- The change log holds every structural stamp, which is never an explicit one, and enough
  other past revisions to count the definition changes, avoiding every explicit stamp. The
  revision leaves room for them, since it counts the explicit retirements apart from the
  definition changes.
-/

namespace Ontography.Proofs

namespace Ckpt

/-- `f` is injective on a list whose image under `f` has no duplicates. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (hxy ▸ List.mem_map_of_mem hy') h.1
    · exact absurd (hxy.symm ▸ List.mem_map_of_mem hx') h.1
    · exact ih h.2 hx' hy'

end Ckpt

variable {Δ : Definition} {S : State}

/-- The checks read only the checkpoint. -/
theorem checkpointValid_congr {S' : State} (hsame : SameCheckpoint S S')
    (h : CheckpointValid Δ S) : CheckpointValid Δ S' := by
  obtain ⟨hA, hP, hIds, hPIds, hN, hE, hD, hR⟩ := hsame
  -- `DependsOn`, `output?`, and the revision-accounting counts read only the maps, and the
  -- counts are invariant under reordering the package identities.
  have hDep : DependsOn S = DependsOn S' := by
    funext b a; simp only [DependsOn, hP]
  have hT : S.explicitTransfers = S'.explicitTransfers := by
    unfold State.explicitTransfers
    have : S.isExplicitTransfer = S'.isExplicitTransfer := by
      funext p; simp only [State.isExplicitTransfer, State.output?, hA, hP]
    rw [this]; exact hPIds.countP_eq _
  have hX : S.explicitRetirements = S'.explicitRetirements := by
    unfold State.explicitRetirements
    have : S.isExplicitRetirement = S'.isExplicitRetirement := by
      funext p; simp only [State.isExplicitRetirement, hP]
    rw [this]; exact hPIds.countP_eq _
  have hO : S.output? = S'.output? := by funext p; simp only [State.output?, hA]
  exact {
    activationIds_nodup := hIds.nodup_iff.mp h.activationIds_nodup
    activations_dom := fun a => by rw [← hA, h.activations_dom a]; exact hIds.mem_iff
    packageIds_nodup := hPIds.nodup_iff.mp h.packageIds_nodup
    packages_dom := fun p => by rw [← hP, h.packages_dom p]; exact hPIds.mem_iff
    used_nonempty := by rw [← hN, ← hE]; exact h.used_nonempty
    current_used := by rw [← hN, ← hE]; exact h.current_used
    used_edges := by rw [← hN, ← hE]; exact h.used_edges
    activation_nodes_used := by rw [← hA, ← hN]; exact h.activation_nodes_used
    ownership := by rw [← hA, ← hP]; exact h.ownership
    outputs_recorded := by rw [← hA, ← hP]; exact h.outputs_recorded
    schema_closure := by rw [← hP]; exact h.schema_closure
    acyclic := by rw [← hDep]; exact h.acyclic
    triggers := by rw [← hA]; exact h.triggers
    consumed := by rw [← hA, ← hP]; exact h.consumed
    inputs := by rw [← hA, ← hP]; exact h.inputs
    join_authority := by rw [← hA, ← hP]; exact h.join_authority
    delivery_used := by rw [← hP, ← hE, ← hN]; exact h.delivery_used
    delivery_current := by rw [← hP]; exact h.delivery_current
    delivery_consistent := by rw [← hP]; exact h.delivery_consistent
    birth_edge := by rw [← hP, ← hO]; exact h.birth_edge
    custody := by rw [← hP]; exact h.custody
    all_routes := by rw [← hP]; exact h.all_routes
    retirement := by rw [← hP, ← hA, ← hR]; exact h.retirement
    explicit_stamps := by rw [← hP]; exact h.explicit_stamps
    structural_stamps := by rw [← hP, ← hD]; exact h.structural_stamps
    revision := by rw [← hR, ← hT, ← hX, ← hD, ← hIds.length_eq]; exact h.revision }

-- Restoration needs nothing of `Δ` beyond `WF`: `hΔ` is unused, and kept so that the
-- statement is exactly `Ontography.checkpoint_of_wf`.
set_option linter.unusedVariables false in
/-- Restoration accepts every well-formed state, so it never rejects a reachable one. -/
theorem checkpoint_of_wf (hΔ : Δ.Admitted) (hS : WF Δ S) : CheckpointValid Δ S where
  activationIds_nodup := hS.activationIds_nodup
  activations_dom := hS.activations_dom
  packageIds_nodup := hS.packageIds_nodup
  packages_dom := hS.packages_dom
  used_nonempty := ⟨hS.used_nonempty.1, fun e he => by
    obtain ⟨edge, hedge, rfl⟩ := List.mem_map.1 he
    exact hS.used_nonempty.2 edge hedge⟩
  current_used := ⟨hS.used_nodes, List.map_subset _ hS.edge_log⟩
  used_edges := ⟨hS.edge_log_ids, fun hne => by
    -- A logged edge names used endpoints.
    cases hlog : S.edgeLog with
    | nil => exact absurd (by simp [State.usedEdges, hlog]) hne
    | cons e _ => exact List.ne_nil_of_mem (hS.edge_log_nodes e (by simp [hlog])).1⟩
  activation_nodes_used := hS.activation_nodes_used
  ownership := hS.ownership
  outputs_recorded := hS.outputs_recorded
  schema_closure := hS.schema_closure
  acyclic := Ontography.causal_acyclic hS
  triggers := hS.triggers
  consumed := hS.consumed
  inputs := hS.inputs
  join_authority := hS.join_authority
  delivery_used p r d hr hd :=
    have hlog := hS.delivery p r d hr hd
    ⟨List.mem_map_of_mem hlog, (hS.edge_log_nodes _ hlog).2⟩
  delivery_current p r d e hr hd he := by
    -- The current edge and the delivery's incidence are both logged under the identity `d.edge`.
    obtain ⟨hmem, hid⟩ := Common.edge?_mem he
    obtain rfl := Ckpt.eq_of_nodup_map hS.edge_log_ids (hS.edge_log hmem)
      (hS.delivery p r d hr hd) hid
    exact ⟨rfl, rfl⟩
  delivery_consistent p q r s d d' hr hs hd hd' hedge := by
    -- Both incidences are logged under the identity `d.edge`.
    obtain ⟨-, h₁, h₂⟩ := Edge.mk.inj (Ckpt.eq_of_nodup_map hS.edge_log_ids
      (hS.delivery p r d hr hd) (hS.delivery q s d' hs hd') hedge)
    exact ⟨h₁, h₂⟩
  birth_edge := hS.birth_edge
  custody := hS.custody
  all_routes := hS.all_routes
  retirement p r ret hr hs :=
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, _⟩ := hS.retirement p r ret hr hs
    ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  explicit_stamps p q r s ρ σ hr hs hρ hσ he hrev := by
    -- An explicit stamp is no definition change, so a retirement sharing it is explicit too.
    obtain ⟨-, -, -, -, -, -, -, hρs⟩ := hS.retirement p r ρ hr hρ
    obtain ⟨-, -, -, -, -, -, -, hσs⟩ := hS.retirement q s σ hs hσ
    have hσe : σ.reason = .explicit := hσs.2 (hrev ▸ hρs.1 he)
    exact ⟨hσe, hS.explicit_stamps p q r s ρ σ hr hs hρ hσ he hσe hrev⟩
  structural_stamps := ⟨S.changeLog, hS.changeLog_nodup, Nat.le_refl _,
    fun p r ret hr hs hne => by
      -- A stamp outside the change log would make the retirement explicit.
      obtain ⟨-, -, -, -, -, -, -, hstamp⟩ := hS.retirement p r ret hr hs
      exact Decidable.byContradiction fun hmem => hne (hstamp.2 hmem)⟩
  revision := hS.revision

namespace Ckpt

/-! ## A causal order -/

/-- A nonempty list has an element with no `R`-successor in it when `R` is acyclic. Induct on
the list, contracting its head: in the tail, a step through the head counts as one step, which
keeps the relation acyclic. -/
theorem exists_minimal {α : Type} (l : List α) :
    ∀ R : α → α → Prop, (∀ x, ¬ Relation.TransGen R x x) → l ≠ [] →
      ∃ m ∈ l, ∀ a ∈ l, ¬ R m a := by
  induction l with
  | nil => exact fun _ _ h => absurd rfl h
  | cons x xs ih =>
    intro R hR _
    by_cases hxs : xs = []
    · subst hxs
      refine ⟨x, List.mem_singleton_self x, fun a ha hxa => ?_⟩
      rw [List.mem_singleton.1 ha] at hxa
      exact hR x (.single hxa)
    · let R' : α → α → Prop := fun b a => R b a ∨ R b x ∧ R x a
      -- A chain of `R'` steps is a chain of `R` steps.
      have hchain : ∀ {b a}, Relation.TransGen R' b a → Relation.TransGen R b a := by
        intro b a h
        induction h with
        | single h =>
          rcases h with h | ⟨h₁, h₂⟩
          · exact .single h
          · exact .tail (.single h₁) h₂
        | tail _ h ih =>
          rcases h with h | ⟨h₁, h₂⟩
          · exact .tail ih h
          · exact .tail (.tail ih h₁) h₂
      obtain ⟨m, hm, hmin⟩ := ih R' (fun y hy => hR y (hchain hy)) hxs
      by_cases hmx : R m x
      · -- A successor of `x` in the tail would be an `R'`-successor of `m`.
        refine ⟨x, List.mem_cons_self, fun a ha hxa => ?_⟩
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hR a (.single hxa)
        · exact hmin a ha (.inr ⟨hmx, hxa⟩)
      · refine ⟨m, List.mem_cons_of_mem _ hm, fun a ha hma => ?_⟩
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hmx hma
        · exact hmin a ha (.inl hma)

/-- A list has a causal order when `R`, relating each element to those it must follow, is
acyclic: put first an element that follows none, then order the rest. -/
theorem exists_order {α : Type} [BEq α] [LawfulBEq α] (R : α → α → Prop)
    (hR : ∀ x, ¬ Relation.TransGen R x x) (l : List α) :
    ∃ L : List α, L.Perm l ∧ ∀ b ∈ l, ∀ a ∈ l, R b a → L.idxOf a < L.idxOf b := by
  induction hl : l.length generalizing l with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact ⟨[], .nil, fun b hb => absurd hb List.not_mem_nil⟩
  | succ n ih =>
    obtain ⟨m, hm, hmin⟩ := exists_minimal l R hR (by rintro rfl; cases hl)
    obtain ⟨L, hperm, hord⟩ :=
      ih (l.erase m) (by rw [List.length_erase_of_mem hm, hl]; rfl)
    refine ⟨m :: L, (hperm.cons m).trans (List.perm_cons_erase hm).symm, ?_⟩
    intro b hb a ha hba
    have hbm : m ≠ b := by rintro rfl; exact hmin a ha hba
    have hb' := (List.mem_erase_of_ne (Ne.symm hbm)).2 hb
    by_cases ham : m = a
    · subst ham
      simp [List.idxOf_cons, hbm]
    · have ha' := (List.mem_erase_of_ne (Ne.symm ham)).2 ha
      simpa [List.idxOf_cons, hbm, ham] using hord b hb' a ha' hba

/-! ## An incidence log -/

open Classical in
/-- The incidence on which the deliveries over `id` agree, if any, else a used node for both
endpoints. -/
noncomputable def receipt (S : State) (id : EdgeId) : Edge :=
  if h : ∃ ends : NodeId × NodeId, ∃ p r d, S.packages p = some r ∧ r.delivery = some d ∧
      d.edge = id ∧ ends = (r.producerNode, d.receiver) then
    ⟨id, (Classical.choose h).1, (Classical.choose h).2⟩
  else ⟨id, S.usedNodes.headD "", S.usedNodes.headD ""⟩

/-- The logged incidence of an edge identity: its current incidence, else a receipt's. -/
noncomputable def incidence (Δ : Definition) (S : State) (id : EdgeId) : Edge :=
  (Δ.edge? id).getD (receipt S id)

/-- The logged incidence of `id` is an edge named `id`. -/
theorem incidence_id {id : EdgeId} : (incidence Δ S id).id = id := by
  unfold incidence
  cases he : Δ.edge? id with
  | none => unfold receipt; split <;> rfl
  | some e => exact (Common.edge?_mem he).2

/-- A current edge is found under its identity. -/
theorem edge?_of_mem (hΔ : Δ.Admitted) {e : Edge} (he : e ∈ Δ.edges) :
    Δ.edge? e.id = some e := by
  have hsome : (Δ.edge? e.id).isSome := by
    unfold Definition.edge?
    exact List.find?_isSome.2 ⟨e, he, by simp⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hmem, hid⟩ := Common.edge?_mem he'
  rw [he', eq_of_nodup_map hΔ.edges_nodup hmem he hid]

/-- A current edge is its own logged incidence. -/
theorem incidence_current (hΔ : Δ.Admitted) {e : Edge} (he : e ∈ Δ.edges) :
    incidence Δ S e.id = e := by
  simp [incidence, edge?_of_mem hΔ he]

/-- A delivery's producer node and receiver are its edge's logged incidence. -/
theorem incidence_delivery (h : CheckpointValid Δ S) {p : PackageId} {r : PackageRecord}
    {d : Delivery} (hr : S.packages p = some r) (hd : r.delivery = some d) :
    incidence Δ S d.edge = ⟨d.edge, r.producerNode, d.receiver⟩ := by
  unfold incidence
  cases he : Δ.edge? d.edge with
  | some e =>
    obtain ⟨hs, ht⟩ := h.delivery_current p r d e hr hd he
    obtain ⟨-, hid⟩ := Common.edge?_mem he
    show e = _
    rw [← hs, ← ht, ← hid]
  | none =>
    show receipt S d.edge = _
    have hex : ∃ ends : NodeId × NodeId, ∃ p r d', S.packages p = some r ∧
        r.delivery = some d' ∧ d'.edge = d.edge ∧ ends = (r.producerNode, d'.receiver) :=
      ⟨_, p, r, d, hr, hd, rfl, rfl⟩
    unfold receipt
    rw [dite_eq_left hex]
    -- The chosen delivery agrees with this one.
    obtain ⟨q, s, d', hs, hd', hedge, hends⟩ := Classical.choose_spec hex
    obtain ⟨hnode, hrecv⟩ := h.delivery_consistent p q r s d d' hr hs hd hd' hedge.symm
    rw [hends, hnode, hrecv]

/-- The endpoints of a used edge identity's logged incidence are used node identities. -/
theorem incidence_nodes (hΔ : Δ.Admitted) (h : CheckpointValid Δ S) {id : EdgeId}
    (hid : id ∈ S.usedEdges) :
    (incidence Δ S id).source ∈ S.usedNodes ∧ (incidence Δ S id).target ∈ S.usedNodes := by
  unfold incidence
  cases he : Δ.edge? id with
  | some e =>
    obtain ⟨hs, ht⟩ := hΔ.endpoints e (Common.edge?_mem he).1
    exact ⟨h.current_used.1 hs, h.current_used.1 ht⟩
  | none =>
    show (receipt S id).source ∈ S.usedNodes ∧ (receipt S id).target ∈ S.usedNodes
    unfold receipt
    split
    · rename_i hex
      obtain ⟨p, r, d, hr, hd, -, hends⟩ := Classical.choose_spec hex
      obtain ⟨act, -, hact, -, -, -, -, hnode⟩ := h.ownership p r hr
      refine ⟨?_, ?_⟩
      · show (Classical.choose hex).1 ∈ S.usedNodes
        rw [hends, hnode]
        exact h.activation_nodes_used _ act hact
      · show (Classical.choose hex).2 ∈ S.usedNodes
        rw [hends]
        exact (h.delivery_used p r d hr hd).2
    · -- Some node identity is used, because `id` is.
      obtain ⟨v, vs, hvs⟩ := List.exists_cons_of_ne_nil (h.used_edges.2 (List.ne_nil_of_mem hid))
      simp [hvs]

/-! ## A change log -/

/-- `k` distinct revisions in `[1, n]` avoid a list `X` that leaves room for them. -/
theorem exists_fresh (X : List Nat) {k n : Nat} (hk : k + X.length ≤ n) :
    ∃ F : List Nat, F.Nodup ∧ F.length = k ∧ ∀ m ∈ F, 1 ≤ m ∧ m ≤ n ∧ m ∉ X := by
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : List Nat, F₀ = (List.range' 1 n).filter fun m => m ∉ X :=
    ⟨_, rfl⟩
  have hnodup : F₀.Nodup := hF₀ ▸ List.Pairwise.filter _ List.nodup_range'
  have hmem : ∀ m, m ∈ F₀ ↔ (1 ≤ m ∧ m < 1 + n) ∧ m ∉ X := by
    intro m
    rw [hF₀, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  -- Every revision in `[1, n]` avoids `X` or lies in it.
  have hlen : n ≤ F₀.length + X.length := by
    have := (List.nodup_range' (s := 1) (n := n)).length_le_of_subset (l₂ := F₀ ++ X)
      fun m hm => by
        rw [List.mem_range'_1] at hm
        by_cases hmX : m ∈ X
        · exact List.mem_append_right _ hmX
        · exact List.mem_append_left _ ((hmem m).2 ⟨hm, hmX⟩)
    simpa using this
  refine ⟨F₀.take k, hnodup.sublist (List.take_sublist _ _), ?_, fun m hm => ?_⟩
  · rw [List.length_take]
    omega
  · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (hmem m).1 (List.mem_of_mem_take hm)
    exact ⟨h₁, by omega, h₃⟩

/-- The explicit stamps: at most one per explicit retirement, each an explicit stamp, and every
explicit stamp among them. -/
theorem exists_explicit (h : CheckpointValid Δ S) :
    ∃ E : List Nat, E.length ≤ S.explicitRetirements ∧
      (∀ p r ret, S.packages p = some r → r.status = .retired ret → ret.reason = .explicit →
        ret.revision ∈ E) ∧
      ∀ n ∈ E, ∃ p r ret, S.packages p = some r ∧ r.status = .retired ret ∧
        ret.reason = .explicit ∧ ret.revision = n := by
  refine ⟨(S.packageIds.filter S.isExplicitRetirement).filterMap fun p =>
    ((S.packages p).bind PackageRecord.retirement?).map (·.revision), ?_, ?_, ?_⟩
  · exact Nat.le_trans (List.length_filterMap_le _ _)
      (Nat.le_of_eq List.countP_eq_length_filter.symm)
  · intro p r ret hr hs he
    refine List.mem_filterMap.2
      ⟨p, List.mem_filter.2 ⟨(h.packages_dom p).1 (by simp [hr]), ?_⟩, ?_⟩
    · simp [State.isExplicitRetirement, hr, PackageRecord.retirement?, hs, he]
    · simp [hr, PackageRecord.retirement?, hs]
  · intro n hn
    obtain ⟨p, hp, hpn⟩ := List.mem_filterMap.1 hn
    have hexp := (List.mem_filter.1 hp).2
    cases hr : S.packages p with
    | none => simp [hr] at hpn
    | some r =>
      cases hs : r.status with
      | retired ret =>
        refine ⟨p, r, ret, hr, hs, ?_, ?_⟩
        · simpa [State.isExplicitRetirement, hr, PackageRecord.retirement?, hs] using hexp
        · simpa [hr, PackageRecord.retirement?, hs] using hpn
      | live => simp [hr, PackageRecord.retirement?, hs] at hpn
      | consumed b => simp [hr, PackageRecord.retirement?, hs] at hpn

/-- A change log for a valid checkpoint: `definitionChanges` distinct past revisions that hold
every structural stamp and no explicit one. It is the structural stamps followed by revisions
that avoid every stamp, and the revision leaves room for them apart from the explicit
stamps. -/
theorem exists_changeLog (h : CheckpointValid Δ S) :
    ∃ C : List Nat, C.Nodup ∧ C.length = S.definitionChanges ∧
      (∀ n ∈ C, 1 ≤ n ∧ n ≤ S.revision) ∧
      ∀ p r ret, S.packages p = some r → r.status = .retired ret →
        (ret.reason = .explicit ↔ ret.revision ∉ C) := by
  obtain ⟨stamps, hnodup, hlen, hstruct⟩ := h.structural_stamps
  obtain ⟨E, hE, hE_mem, hE_explicit⟩ := exists_explicit h
  -- The structural stamps, as past revisions that are no explicit stamp.
  obtain ⟨T, hT⟩ : ∃ T : List Nat,
      T = stamps.filter fun n => 1 ≤ n ∧ n ≤ S.revision ∧ n ∉ E := ⟨_, rfl⟩
  have hTnodup : T.Nodup := hT ▸ List.Pairwise.filter _ hnodup
  have hTlen : T.length ≤ S.definitionChanges :=
    hT ▸ Nat.le_trans (List.length_filter_le _ _) hlen
  have hTmem : ∀ n, n ∈ T ↔ n ∈ stamps ∧ 1 ≤ n ∧ n ≤ S.revision ∧ n ∉ E := by
    intro n
    rw [hT, List.mem_filter, decide_eq_true_eq]
  have hrev := h.revision
  obtain ⟨F, hFnodup, hFlen, hFmem⟩ :=
    exists_fresh (E ++ T) (k := S.definitionChanges - T.length) (n := S.revision) (by
      rw [List.length_append]
      omega)
  refine ⟨T ++ F, ?_, ?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hTnodup, hFnodup, fun a ha b hb hab => ?_⟩
    subst hab
    exact (hFmem a hb).2.2 (List.mem_append_right _ ha)
  · rw [List.length_append, hFlen]
    omega
  · intro n hn
    rcases List.mem_append.1 hn with hn | hn
    · obtain ⟨-, h₁, h₂, -⟩ := (hTmem n).1 hn
      exact ⟨h₁, h₂⟩
    · obtain ⟨h₁, h₂, -⟩ := hFmem n hn
      exact ⟨h₁, h₂⟩
  · intro p r ret hr hs
    obtain ⟨-, -, -, -, h₁, h₂, -⟩ := h.retirement p r ret hr hs
    constructor
    · -- An explicit stamp is in `E`, which both parts avoid.
      intro he hmem
      have hE' := hE_mem p r ret hr hs he
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact ((hTmem _).1 hmem).2.2.2 hE'
      · exact (hFmem _ hmem).2.2 (List.mem_append_left _ hE')
    · -- A structural stamp is in `T`, since only explicit retirements carry explicit stamps.
      intro hnot
      refine Decidable.byContradiction fun hne => hnot (List.mem_append_left _ ?_)
      refine (hTmem _).2 ⟨hstruct p r ret hr hs hne, h₁, h₂, fun hmem => ?_⟩
      obtain ⟨q, s, σ, hq, hσ, hσe, hrev'⟩ := hE_explicit _ hmem
      exact hne (h.explicit_stamps q p s r σ ret hq hr hσ hs hσe hrev').1

end Ckpt

open Ckpt in
/-- Restoration checks exactly the invariants: every checkpoint that passes is recorded by a
well-formed state, which differs from it at most in acceptance order and the ghost logs. -/
theorem checkpoint_sound (hΔ : Δ.Admitted) (h : CheckpointValid Δ S) :
    ∃ S', S'.activations = S.activations ∧ S'.packages = S.packages ∧
      S'.activationIds.Perm S.activationIds ∧ S'.packageIds = S.packageIds ∧
      S'.usedNodes = S.usedNodes ∧ S'.usedEdges = S.usedEdges ∧
      S'.definitionChanges = S.definitionChanges ∧ S'.revision = S.revision ∧ WF Δ S' := by
  obtain ⟨L, hperm, hord⟩ := exists_order (DependsOn S) h.acyclic S.activationIds
  obtain ⟨C, hCnodup, hClen, hCle, hCiff⟩ := exists_changeLog h
  have hedges : (S.usedEdges.map (incidence Δ S)).map (·.id) = S.usedEdges := by
    rw [List.map_map]
    exact List.map_id'' (fun _ => incidence_id) _
  have hmem : ∀ a act, S.activations a = some act → a ∈ S.activationIds :=
    fun a act ha => (h.activations_dom a).1 (by simp [ha])
  refine ⟨{ S with
      activationIds := L
      edgeLog := S.usedEdges.map (incidence Δ S)
      changeLog := C },
    rfl, rfl, hperm, rfl, rfl, hedges, hClen, rfl, ?_⟩
  exact {
    activationIds_nodup := hperm.nodup_iff.2 h.activationIds_nodup
    activations_dom := fun a => (h.activations_dom a).trans hperm.mem_iff.symm
    packageIds_nodup := h.packageIds_nodup
    packages_dom := h.packages_dom
    ownership := h.ownership
    outputs_recorded := h.outputs_recorded
    consumed := h.consumed
    inputs := h.inputs
    join_authority := h.join_authority
    triggers := h.triggers
    delivery := fun p r d hr hd =>
      List.mem_map.2 ⟨d.edge, (h.delivery_used p r d hr hd).1, incidence_delivery h hr hd⟩
    birth_edge := h.birth_edge
    retirement := fun p r ret hr hs => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h.retirement p r ret hr hs
      exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, hCiff p r ret hr hs⟩
    explicit_stamps := fun p q r s ρ σ hr hs hρ hσ he _ hrev =>
      (h.explicit_stamps p q r s ρ σ hr hs hρ hσ he hrev).2
    custody := h.custody
    all_routes := h.all_routes
    revision := by
      show S.revision = L.length + S.explicitTransfers + S.explicitRetirements + C.length
      rw [hperm.length_eq, hClen]
      exact h.revision
    changeLog_nodup := hCnodup
    changeLog_le := hCle
    used_nodes := h.current_used.1
    edge_log := fun e he =>
      List.mem_map.2 ⟨e.id, h.current_used.2 (List.mem_map_of_mem he), incidence_current hΔ he⟩
    edge_log_ids := by
      show ((S.usedEdges.map (incidence Δ S)).map (·.id)).Nodup
      rw [hedges]
      exact h.used_edges.1
    activation_nodes_used := h.activation_nodes_used
    edge_log_nodes := fun e he => by
      obtain ⟨id, hid, rfl⟩ := List.mem_map.1 he
      exact incidence_nodes hΔ h hid
    used_nonempty := ⟨h.used_nonempty.1, fun e he => by
      obtain ⟨id, hid, rfl⟩ := List.mem_map.1 he
      rw [incidence_id]
      exact h.used_nonempty.2 id hid⟩
    causal_order := fun p r b hr hs => by
      -- The producer and the consumer are accepted, and the order puts the producer first.
      obtain ⟨act, hact, -⟩ := h.consumed p r b hr hs
      obtain ⟨act', -, hact', -⟩ := h.ownership p r hr
      exact hord b (hmem b act hact) p.producer (hmem _ act' hact') ⟨p, r, rfl, hr, hs⟩
    schema_closure := h.schema_closure }

end Ontography.Proofs
