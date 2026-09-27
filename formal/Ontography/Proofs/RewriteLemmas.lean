import Ontography.System
import Ontography.Proofs.Basic
import Ontography.Proofs.ActivationLemmas

/-!
# Lemmas for rewriting

Inversion of the parts of `rewrite`, for the proofs in `Ontography.Proofs.Rewrite`.

`lookup_fates` reads the batch of cleanup fates: a package retires exactly when it is
recorded and its own cleanup retires it. `cleanup_retire` and `cleanup_keep` state what a
cleanup decision establishes, and `structural_spec` what an admitted replacement does to the
graph. `wf_cleaned` is the batch counterpart of `Common.wf_setRecord`: replacing the
definition by an admitted replacement and every live record by its cleanup, and recording
one definition change, preserves `WF`.
-/

namespace Ontography.Proofs.Rewrite

open Common

/-! ## The batch of fates -/

/-- Each entry of a successful batch `l.mapM f` is keyed by its own element, so the entries
the batch retires are looked up by key: `q` finds its own fate when listed, and nothing
otherwise. -/
theorem lookup_fates {α β : Type} [DecidableEq α] {f : α → Option (α × Option β)}
    (hf : ∀ p x, f p = some x → x.1 = p) :
    ∀ {l : List α} {fates : List (α × Option β)}, l.mapM f = some fates → ∀ q,
      (fates.filterMap fun g => g.2.map fun x => (g.1, x)).lookup q =
        if q ∈ l then (f q).bind Prod.snd else none
  | [], fates, h, q => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | p :: ps, fates, h, q => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨p', x⟩, hp, ys, hys, rfl⟩ := h
    obtain rfl : p = p' := (hf p _ hp).symm
    have ih := lookup_fates hf hys q
    by_cases hqp : q = p
    · subst hqp
      cases x with
      | none => simp [ih, hp]
      | some b => simp [hp]
    · have hne : (q == p) = false := by simp [hqp]
      cases x with
      | none => simp [ih, hqp]
      | some b => simp [List.lookup_cons, hne, ih, hqp]

/-! ## Cleanup decisions -/

section Cleanup

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ next : Definition}
  {deleted : List NodeId} {evidence : List (Digest × Bytes)} {r : PackageRecord}

/-- A cleanup retirement is structural and fits the package's phase: `HolderRemoved` for a
deleted holder, `NoAcceptingEdge` for an outbound package, and `RouteRemoved` for a
delivered one. -/
theorem cleanup_retire {reason : Reason}
    (h : cleanup? accepts H Δ next deleted evidence r = some (some reason)) :
    reason ≠ .explicit ∧ (reason = .holderRemoved → r.holder ∈ deleted) ∧
      (reason = .noAcceptingEdge → r.delivery = none) ∧
      (reason = .routeRemoved → r.delivery ≠ none) := by
  unfold cleanup? at h
  split at h
  · cases h
    simp_all
  · split at h
    · have : reason = .noAcceptingEdge := by
        split at h
        · cases h
        · dsimp only at h
          split at h
          · cases h
            rfl
          · simp only [bind, Option.bind_eq_some_iff, guard_eq_some] at h
            obtain ⟨_, -, h⟩ := h
            split at h <;> simp_all
      subst this
      simp_all
    · have : reason = .routeRemoved := by
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h
              rfl
      subst this
      simp_all

/-- A package cleanup keeps has a surviving holder, and a kept receipt at an `All` node names
an edge still incoming to it. -/
theorem cleanup_keep (h : cleanup? accepts H Δ next deleted evidence r = some none) :
    r.holder ∉ deleted ∧ ∀ d nd, r.delivery = some d → next.nodeDef? r.holder = some nd →
      nd.ingress = .all → d.edge ∈ next.incoming r.holder := by
  unfold cleanup? at h
  split at h
  · cases h
  · rename_i hdel
    refine ⟨hdel, fun d nd hd hnd hall => ?_⟩
    split at h
    · rename_i hd'
      rw [hd] at hd'
      cases hd'
    · rename_i d' hd'
      rw [hd] at hd'
      cases hd'
      rw [hnd] at h
      dsimp only at h
      rw [hall] at h
      dsimp only at h
      split at h
      · assumption
      · cases h

end Cleanup

/-! ## The structural step -/

/-- What an admitted replacement does to the graph: the schema stays, the deleted nodes leave,
the fresh nodes and edges join, every kept edge is a current one, and the fresh identities
were never used. -/
structure StructuralSpec (Δ : Definition) (S : State) (rep : Replacement) : Prop where
  admitted : rep.next.Admitted
  schema : rep.next.schema = Δ.schema
  nodes : rep.next.nodes = Δ.nodes.filter (· ∉ rep.deleted) ++ rep.freshNodes
  edges : ∃ kept, kept ⊆ Δ.edges ∧ rep.next.edges = kept ++ rep.freshEdges
  freshNodes : ∀ v ∈ rep.freshNodes, v ∉ S.usedNodes
  freshEdges : ∀ e ∈ rep.freshEdges, e.id ∉ S.usedEdges

/-- An admitted structural step satisfies `StructuralSpec`. -/
theorem structural_spec {Δ : Definition} {S : State} {pr : Production} {m : Match}
    {rep : Replacement} (h : structural? Δ S pr m = some rep) : StructuralSpec Δ S rep := by
  simp only [structural?, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hfreshN, hfreshE, -, hadm, rfl⟩ := h
  refine ⟨hadm, rfl, rfl, ⟨_, List.filter_sublist.subset, rfl⟩, ?_, ?_⟩
  · intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
    exact hfreshN b hb
  · intro e he
    obtain ⟨b, hb, he⟩ := List.mem_filterMap.1 he
    obtain ⟨re, -, rfl⟩ := Option.map_eq_some_iff.1 he
    exact hfreshE b hb

/-! ## Holders -/

/-- Every recorded package's holder is a lifetime node: an outbound package's holder is its
producer's node, and a delivered one's is the target of a logged edge. -/
theorem holder_used {Δ : Definition} {S : State} (hS : WF Δ S) {p : PackageId}
    {r : PackageRecord} (hr : S.packages p = some r) : r.holder ∈ S.usedNodes := by
  unfold PackageRecord.holder
  cases hd : r.delivery with
  | none =>
    obtain ⟨act, o, hact, -, -, -, -, hnode⟩ := hS.ownership p r hr
    rw [hnode]
    exact hS.activation_nodes_used _ act hact
  | some d => exact (hS.edge_log_nodes _ (hS.delivery p r d hr hd)).2

/-! ## The cleaned state -/

section Cleaned

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {rep : Replacement} {evidence : List (Digest × Bytes)} {S S' : State}

/-- `S'` records the packages of `S` after cleanup under `Δ ⟶ rep.next`: no package is added,
a package that is not live keeps its record, and a live package is kept or retired at the
successor revision by its own cleanup decision. -/
structure Cleaned (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)
    (rep : Replacement) (evidence : List (Digest × Bytes)) (S S' : State) : Prop where
  absent : ∀ q, S.packages q = none → S'.packages q = none
  dead : ∀ q r, S.packages q = some r → r.status ≠ .live → S'.packages q = some r
  live : ∀ q r, S.packages q = some r → r.status = .live →
    ∃ fate, cleanup? accepts H Δ rep.next rep.deleted evidence r = some fate ∧
      S'.packages q = some (match fate with
        | none => r
        | some reason => { r with status := .retired ⟨reason, S.revision + 1, none⟩ })

namespace Cleaned

variable (hc : Cleaned accepts H Δ rep evidence S S')
include hc

/-- Every record after cleanup is a record before it, kept, or a live one retired by its
cleanup decision. -/
theorem cases {q : PackageId} {x : PackageRecord} (hx : S'.packages q = some x) :
    ∃ r, S.packages q = some r ∧
      ((x = r ∧
          (r.status = .live → cleanup? accepts H Δ rep.next rep.deleted evidence r = some none)) ∨
        (r.status = .live ∧ ∃ reason,
          cleanup? accepts H Δ rep.next rep.deleted evidence r = some (some reason) ∧
            x = { r with status := .retired ⟨reason, S.revision + 1, none⟩ })) := by
  cases hq : S.packages q with
  | none =>
    rw [hc.absent q hq] at hx
    cases hx
  | some r =>
    refine ⟨r, rfl, ?_⟩
    by_cases hst : r.status = .live
    · obtain ⟨fate, hfate, h⟩ := hc.live q r hq hst
      rw [hx, Option.some.injEq] at h
      cases fate with
      | none => exact .inl ⟨h, fun _ => hfate⟩
      | some reason => exact .inr ⟨hst, reason, hfate, h⟩
    · rw [hc.dead q r hq hst, Option.some.injEq] at hx
      exact .inl ⟨hx.symm, fun h => absurd h hst⟩

/-- Cleanup keeps every package's immutable facts and delivery. -/
theorem facts {q : PackageId} {x : PackageRecord} (hx : S'.packages q = some x) :
    ∃ r, S.packages q = some r ∧ x.objectType = r.objectType ∧ x.authority = r.authority ∧
      x.digest = r.digest ∧ x.producerNode = r.producerNode ∧ x.delivery = r.delivery := by
  obtain ⟨r, hr, ⟨rfl, -⟩ | ⟨-, _, -, rfl⟩⟩ := hc.cases hx
  · exact ⟨x, hr, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨r, hr, rfl, rfl, rfl, rfl, rfl⟩

/-- Every record before cleanup is still recorded, with its delivery, and its status changes
only by a structural retirement of a live package. -/
theorem forward {q : PackageId} {r : PackageRecord} (hr : S.packages q = some r) :
    ∃ x, S'.packages q = some x ∧ x.delivery = r.delivery ∧
      (x.status = r.status ∨ r.status = .live ∧
        ∃ reason, reason ≠ .explicit ∧ x.status = .retired ⟨reason, S.revision + 1, none⟩) := by
  by_cases hst : r.status = .live
  · obtain ⟨fate, hfate, h⟩ := hc.live q r hr hst
    cases fate with
    | none => exact ⟨r, h, rfl, .inl rfl⟩
    | some reason => exact ⟨_, h, rfl, .inr ⟨hst, reason, (cleanup_retire hfate).1, rfl⟩⟩
  · exact ⟨r, hc.dead q r hr hst, rfl, .inl rfl⟩

end Cleaned

/-- Replacing the definition by an admitted replacement, cleaning up every live package under
it, and recording one definition change preserves `WF`: the batch counterpart of
`Common.wf_setRecord`. -/
theorem wf_cleaned (hS : WF Δ S) (hrep : StructuralSpec Δ S rep)
    (hacts : S'.activations = S.activations) (hactIds : S'.activationIds = S.activationIds)
    (hpkgIds : S'.packageIds = S.packageIds)
    (hused : S'.usedNodes = S.usedNodes ++ rep.freshNodes)
    (hlog : S'.edgeLog = S.edgeLog ++ rep.freshEdges)
    (hchange : S'.changeLog = S.changeLog ++ [S.revision + 1])
    (hrev : S'.revision = S.revision + 1) (hc : Cleaned accepts H Δ rep evidence S S') :
    WF rep.next S' := by
  have hout : S'.output? = S.output? := by
    funext q
    unfold State.output?
    rw [hacts]
  have hsome : ∀ q, (S'.packages q).isSome = (S.packages q).isSome := by
    intro q
    cases hq : S.packages q with
    | none => rw [hc.absent q hq]
    | some r =>
      obtain ⟨x, hx, -⟩ := hc.forward hq
      rw [hx]
      rfl
  have hnodes : ∀ v, v ∈ rep.next.nodes ↔ (v ∈ Δ.nodes ∧ v ∉ rep.deleted) ∨ v ∈ rep.freshNodes := by
    intro v
    rw [hrep.nodes]
    simp
  obtain ⟨kept, hkept, hedges⟩ := hrep.edges
  -- I7: the replacement's nodes are lifetime identities.
  have hused_nodes : rep.next.nodes ⊆ S'.usedNodes := by
    intro v hv
    rw [hused]
    rcases (hnodes v).1 hv with ⟨hv, -⟩ | hv
    · exact List.mem_append_left _ (hS.used_nodes hv)
    · exact List.mem_append_right _ hv
  -- I6: cleanup adds no explicit transfer and no explicit retirement.
  have hET : S'.explicitTransfers = S.explicitTransfers := by
    unfold State.explicitTransfers
    rw [hpkgIds]
    congr 1
    funext q
    unfold State.isExplicitTransfer
    rw [hout]
    cases hq : S.packages q with
    | none => rw [hc.absent q hq]
    | some r =>
      obtain ⟨x, hx, hdel, -⟩ := hc.forward hq
      rw [hx]
      cases S.output? q <;> simp [hdel]
  have hER : S'.explicitRetirements = S.explicitRetirements := by
    unfold State.explicitRetirements
    rw [hpkgIds]
    congr 1
    funext q
    unfold State.isExplicitRetirement
    cases hq : S.packages q with
    | none => rw [hc.absent q hq]
    | some r =>
      obtain ⟨x, hx, -, hst⟩ := hc.forward hq
      rw [hx]
      rcases hst with hst | ⟨hlive, reason, hne, hst⟩
      · simp [PackageRecord.retirement?, hst]
      · simp [PackageRecord.retirement?, hst, hlive, hne]
  refine
    { activationIds_nodup := hactIds ▸ hS.activationIds_nodup
      activations_dom := fun a => by
        rw [hacts, hactIds]
        exact hS.activations_dom a
      packageIds_nodup := hpkgIds ▸ hS.packageIds_nodup
      packages_dom := fun p => by
        rw [hsome, hpkgIds]
        exact hS.packages_dom p
      ownership := ?_
      outputs_recorded := fun a act ha i hi => by
        rw [hacts] at ha
        rw [hsome]
        exact hS.outputs_recorded a act ha i hi
      consumed := ?_
      inputs := ?_
      join_authority := ?_
      triggers := fun b act hb => by
        rw [hacts] at hb
        rw [hrep.schema]
        exact hS.triggers b act hb
      delivery := ?_
      birth_edge := ?_
      retirement := ?_
      explicit_stamps := ?_
      custody := ?_
      all_routes := ?_
      revision := ?_
      changeLog_nodup := ?_
      changeLog_le := ?_
      used_nodes := hused_nodes
      edge_log := ?_
      edge_log_ids := ?_
      activation_nodes_used := fun a act ha => by
        rw [hacts] at ha
        rw [hused]
        exact List.mem_append_left _ (hS.activation_nodes_used a act ha)
      edge_log_nodes := ?_
      used_nonempty := ?_
      causal_order := ?_
      schema_closure := ?_ }
  · -- I1
    intro p x hx
    obtain ⟨r, hr, h₁, h₂, h₃, h₄, -⟩ := hc.facts hx
    obtain ⟨act, o, hact, ho, h₅, h₆, h₇, h₈⟩ := hS.ownership p r hr
    exact ⟨act, o, by rw [hacts]; exact hact, ho, h₁.trans h₅, h₂.trans h₆, h₃.trans h₇,
      h₄.trans h₈⟩
  · -- I2: a consumed record is an old one.
    intro p x b hx hst
    obtain ⟨r, hr, ⟨rfl, -⟩ | ⟨-, reason, -, rfl⟩⟩ := hc.cases hx
    · rw [hacts]
      exact hS.consumed p x b hr hst
    · cases hst
  · -- I2: an input is consumed, so cleanup keeps it.
    intro b act hb p hp
    rw [hacts] at hb
    obtain ⟨r, d, hr, hst, hd, hrecv⟩ := hS.inputs b act hb p hp
    exact ⟨r, d, hc.dead p r hr (by rw [hst]; simp), hst, hd, hrecv⟩
  · -- I2
    intro b act hb p hp q hq x y hx hy
    rw [hacts] at hb
    obtain ⟨r, hr, -, hxa, -⟩ := hc.facts hx
    obtain ⟨s, hs, -, hya, -⟩ := hc.facts hy
    rw [hxa, hya]
    exact hS.join_authority b act hb p hp q hq r s hr hs
  · -- I3: deliveries are kept, and the edge log only grows.
    intro p x d hx hd
    obtain ⟨r, hr, -, -, -, hnode, hdel⟩ := hc.facts hx
    rw [hlog, hnode]
    exact List.mem_append_left _ (hS.delivery p r d hr (hdel ▸ hd))
  · -- I3
    intro p x o e hx ho he
    obtain ⟨r, hr, -, -, -, -, hdel⟩ := hc.facts hx
    rw [hout] at ho
    rw [hdel]
    exact hS.birth_edge p r o e hr ho he
  · -- I4
    intro p x ret hx hst
    obtain ⟨r, hr, ⟨rfl, -⟩ | ⟨hlive, reason, hfate, rfl⟩⟩ := hc.cases hx
    · -- An old retirement: its stamp is past, and a removed holder stays removed, since a
      -- fresh node was never a lifetime node.
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hS.retirement p x ret hr hst
      have hne : ret.revision ≠ S.revision + 1 := by omega
      refine ⟨h₁, h₂, h₃, fun a ha => by rw [hacts]; exact h₄ a ha, h₅, by rw [hrev]; omega,
        fun hh hmem => ?_, ?_⟩
      · rcases (hnodes _).1 hmem with ⟨hmem, -⟩ | hmem
        · exact h₇ hh hmem
        · exact hrep.freshNodes _ hmem (holder_used hS hr)
      · rw [hchange, List.mem_append, List.mem_singleton]
        simp only [hne, or_false]
        exact h₈
    · -- A new retirement: structural, stamped with the new definition change.
      obtain ⟨hne, hhold, hnoacc, hroute⟩ := cleanup_retire hfate
      cases hst
      have hheld : r.holder ∈ S.usedNodes := holder_used hS hr
      refine ⟨hnoacc, hroute, fun h => absurd rfl h, fun _ ha => (nomatch ha),
        Nat.le_add_left _ _, hrev ▸ Nat.le_refl _, fun hh hmem => ?_, ?_⟩
      · rcases (hnodes _).1 hmem with ⟨-, hmem⟩ | hmem
        · exact hmem (hhold hh)
        · exact hrep.freshNodes _ hmem hheld
      · rw [hchange]
        simp [hne]
  · -- I4: every explicit retirement is an old one.
    intro p q x y ρ σ hx hy hxs hys hρ hσ hstamp
    obtain ⟨r, hr, ⟨rfl, -⟩ | ⟨-, reason, hfate, rfl⟩⟩ := hc.cases hx
    · obtain ⟨s, hs, ⟨rfl, -⟩ | ⟨-, reason', hfate', rfl⟩⟩ := hc.cases hy
      · exact hS.explicit_stamps p q x y ρ σ hr hs hxs hys hρ hσ hstamp
      · cases hys
        exact absurd hσ (cleanup_retire hfate').1
    · cases hxs
      exact absurd hρ (cleanup_retire hfate).1
  · -- I5: a kept live package's holder survives.
    intro p x hx hst
    obtain ⟨r, hr, ⟨rfl, hkeep⟩ | ⟨-, reason, -, rfl⟩⟩ := hc.cases hx
    · exact (hnodes _).2 (.inl ⟨hS.custody p x hr hst, (cleanup_keep (hkeep hst)).1⟩)
    · cases hst
  · -- I5: a kept receipt at an `All` node names an incoming edge of the replacement.
    intro p x d nd hx hst hd hnd hall
    obtain ⟨r, hr, ⟨rfl, hkeep⟩ | ⟨-, reason, -, rfl⟩⟩ := hc.cases hx
    · have hholder : x.holder = d.receiver := by
        unfold PackageRecord.holder
        rw [hd]
      rw [← hholder] at hnd ⊢
      exact (cleanup_keep (hkeep hst)).2 d nd hd hnd hall
    · cases hst
  · -- I6: one more definition change, and the same counts otherwise.
    have := hS.revision
    unfold State.definitionChanges at this ⊢
    rw [hrev, hET, hER, hactIds, hchange, List.length_append, List.length_singleton]
    omega
  · -- I6: the new stamp exceeds every recorded definition change.
    rw [hchange, List.nodup_append]
    refine ⟨hS.changeLog_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    have := (hS.changeLog_le a ha).2
    omega
  · intro n hn
    rw [hchange, List.mem_append, List.mem_singleton] at hn
    rw [hrev]
    rcases hn with hn | rfl
    · have := hS.changeLog_le n hn
      omega
    · omega
  · -- I7: a kept edge is a current one, and the fresh edges are logged.
    intro e he
    rw [hedges, List.mem_append] at he
    rw [hlog]
    rcases he with he | he
    · exact List.mem_append_left _ (hS.edge_log (hkept he))
    · exact List.mem_append_right _ he
  · -- I7: fresh edge identities are distinct and never used.
    have hfresh : (rep.freshEdges.map (·.id)).Nodup := by
      have := hrep.admitted.edges_nodup
      rw [hedges, List.map_append, List.nodup_append] at this
      exact this.2.1
    rw [hlog, List.map_append, List.nodup_append]
    refine ⟨hS.edge_log_ids, hfresh, ?_⟩
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
    exact hrep.freshEdges e he (hab ▸ ha)
  · -- I7: a fresh edge joins nodes of the replacement.
    intro e he
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · have := hS.edge_log_nodes e he
      rw [hused]
      exact ⟨List.mem_append_left _ this.1, List.mem_append_left _ this.2⟩
    · have := hrep.admitted.endpoints e (by rw [hedges]; exact List.mem_append_right _ he)
      exact ⟨hused_nodes this.1, hused_nodes this.2⟩
  · -- I7: fresh identities are nonempty, as the replacement is admitted.
    refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · rw [hused, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hS.used_nonempty.1 v hv
      · exact hrep.admitted.nodes_nonempty v ((hnodes v).2 (.inr hv))
    · rw [hlog, List.mem_append] at he
      rcases he with he | he
      · exact hS.used_nonempty.2 e he
      · exact hrep.admitted.edges_nonempty e (by rw [hedges]; exact List.mem_append_right _ he)
  · -- Causal acyclicity: a consumed record is an old one.
    intro p x b hx hst
    obtain ⟨r, hr, ⟨rfl, -⟩ | ⟨-, reason, -, rfl⟩⟩ := hc.cases hx
    · rw [hactIds]
      exact hS.causal_order p x b hr hst
    · cases hst
  · -- Schema closure: the schema stays.
    intro p x hx
    obtain ⟨r, hr, hobj, hauth, -⟩ := hc.facts hx
    rw [hrep.schema, hobj, hauth]
    exact hS.schema_closure p r hr

end Cleaned

end Ontography.Proofs.Rewrite
