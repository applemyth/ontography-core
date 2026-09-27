import Ontography.Commutation
import Ontography.Proofs.Basic
import Ontography.Proofs.ActivationLemmas

/-!
# Lemmas for locality and commutation

What `structural?` guarantees about its replacement, what `cleanup?` reads, and how both
respect `Definition.Equiv`, for the proofs in `Ontography.Proofs.Commutation`.

`Shape` records the facts of a successful `structural?` that cleanup depends on: the deleted
nodes are a function of the production and the match, and the replacement keeps the
contracts and every retained node and edge with its annotation, and gives its new nodes and
edges unused identities. From these, `cleanup_keep` shows that a package whose holder a
rewrite does not affect is kept, and `cleanup_eq` that one rewrite decides the same fate for a
package before and after a second rewrite that does not affect its holder.
-/

namespace Ontography.Proofs.Commute

open Ontography.Proofs.Activation (setEq_symm setEq_trans)

/-! ## Lists as sets -/

section Lists

variable {α β : Type}

/-- `SetEq` tests on set-equal arguments agree. -/
theorem setEq_congr {a b c d : List α} (hab : SetEq a b) (hcd : SetEq c d) :
    SetEq a c ↔ SetEq b d :=
  ⟨fun h => setEq_trans (setEq_symm hab) (setEq_trans h hcd),
    fun h => setEq_trans hab (setEq_trans h (setEq_symm hcd))⟩

/-- Filtering and mapping preserve set equality. -/
theorem setEq_filter_map {l₁ l₂ : List α} (h : SetEq l₁ l₂) (p : α → Bool) (f : α → β) :
    SetEq ((l₁.filter p).map f) ((l₂.filter p).map f) := by
  constructor <;> intro x hx <;> obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx <;>
    rw [List.mem_filter] at ha
  · exact List.mem_map_of_mem (List.mem_filter.2 ⟨h.1 ha.1, ha.2⟩)
  · exact List.mem_map_of_mem (List.mem_filter.2 ⟨h.2 ha.1, ha.2⟩)

/-- Distinct keys identify elements. -/
theorem eq_of_map_nodup {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact (h.1 (hxy ▸ List.mem_map_of_mem hy')).elim
    · exact (h.1 (hxy.symm ▸ List.mem_map_of_mem hx')).elim
    · exact eq_of_map_nodup h.2 hx' hy' hxy

/-- A search agrees across set-equal lists when at most one element of the second
matches. -/
theorem find?_eq_of_setEq {p : α → Bool} {l₁ l₂ : List α} (h : SetEq l₁ l₂)
    (huniq : ∀ x ∈ l₂, ∀ y ∈ l₂, p x = true → p y = true → x = y) :
    l₁.find? p = l₂.find? p := by
  cases h₁ : l₁.find? p with
  | none =>
    symm
    rw [List.find?_eq_none] at h₁ ⊢
    exact fun x hx => h₁ x (h.2 hx)
  | some a =>
    have ha := h.1 (List.mem_of_find?_eq_some h₁)
    have hpa := List.find?_some h₁
    cases h₂ : l₂.find? p with
    | none => exact absurd hpa (List.find?_eq_none.1 h₂ a ha)
    | some b =>
      rw [huniq a ha b (List.mem_of_find?_eq_some h₂) hpa (List.find?_some h₂)]

/-- A search by a unique key agrees across set-equal lists. -/
theorem find?_key_eq [BEq β] [LawfulBEq β] {key : α → β} {l₁ l₂ : List α} (h : SetEq l₁ l₂)
    (hnd : (l₂.map key).Nodup) (k : β) :
    l₁.find? (fun x => key x == k) = l₂.find? (fun x => key x == k) :=
  find?_eq_of_setEq h fun _ hx _ hy hpx hpy =>
    eq_of_map_nodup hnd hx hy (by rw [beq_iff_eq.1 hpx, beq_iff_eq.1 hpy])

/-- A filter that passes every match leaves a search unchanged. -/
theorem find?_filter_of_imp {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, q a = true → p a = true) → (l.filter p).find? q = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ih := find?_filter_of_imp (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases hq : q a = true
    · simp [h a List.mem_cons_self hq, hq]
    · by_cases hp : p a = true <;> simp [hp, hq, ih]

/-- A search that succeeds in a prefix is decided there. -/
theorem find?_append_of_some {p : α → Bool} {l₁ l₂ : List α} {a : α}
    (h : l₁.find? p = some a) : (l₁ ++ l₂).find? p = some a := by
  rw [List.find?_append, h, Option.some_or]

/-- `any` agrees across lists with the same members on which the predicates agree. -/
theorem any_congr {l₁ l₂ : List α} {p q : α → Bool} (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hpq : ∀ x ∈ l₁, p x = q x) : l₁.any p = l₂.any q := by
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (hmem x).1 hx, hpq x hx ▸ hp⟩,
    fun ⟨x, hx, hq⟩ => ⟨x, (hmem x).2 hx, (hpq x ((hmem x).2 hx)).symm ▸ hq⟩⟩

/-- Lists with the same members are empty together. -/
theorem eq_nil_congr {l₁ l₂ : List α} (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = [] ↔ l₂ = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  exact ⟨fun h x hx => h x ((hmem x).2 hx), fun h x hx => h x ((hmem x).1 hx)⟩

end Lists

/-! ## Lookups in a definition -/

section Lookup

variable {Δ Δ₁ Δ₂ : Definition}

theorem mem_outgoing {v : NodeId} {e : EdgeId} :
    e ∈ Δ.outgoing v ↔ ∃ edge ∈ Δ.edges, edge.source = v ∧ edge.id = e := by
  simp [Definition.outgoing, and_assoc]

theorem mem_outgoing_of_mem {edge : Edge} (h : edge ∈ Δ.edges) :
    edge.id ∈ Δ.outgoing edge.source :=
  mem_outgoing.2 ⟨edge, h, rfl, rfl⟩

/-- In an admitted definition every node has a definition. -/
theorem nodeDef?_isSome (hΔ : Δ.Admitted) {v : NodeId} (hv : v ∈ Δ.nodes) :
    ∃ nd, Δ.nodeDef? v = some nd := by
  obtain ⟨d, hd, rfl⟩ := hΔ.nodes_defined v hv
  cases h : Δ.nodeDef? d.node with
  | none => exact absurd (by simp) (List.find?_eq_none.1 h d hd)
  | some nd => exact ⟨nd, rfl⟩

/-- In an admitted definition every edge has an annotation. -/
theorem edgeDef?_isSome (hΔ : Δ.Admitted) {e : Edge} (he : e ∈ Δ.edges) :
    ∃ ed, Δ.edgeDef? e.id = some ed := by
  obtain ⟨d, hd, hde⟩ := hΔ.edges_defined e he
  cases h : Δ.edgeDef? e.id with
  | none => exact absurd (by simp [hde]) (List.find?_eq_none.1 h d hd)
  | some ed => exact ⟨ed, rfl⟩

/-- Metadata acceptance reads only the edge's annotation and the contract registry. -/
theorem metadataAccepts_congr {e : Edge} {r : PackageRecord}
    (hd : Δ₁.edgeDef? e.id = Δ₂.edgeDef? e.id) (hc : ∀ c, Δ₁.contract? c = Δ₂.contract? c) :
    Δ₁.MetadataAccepts e r ↔ Δ₂.MetadataAccepts e r := by
  unfold Definition.MetadataAccepts
  rw [hd]
  cases Δ₂.edgeDef? e.id with
  | none => exact Iff.rfl
  | some ed => simp only [hc]

end Lookup

/-! ## Equivalent definitions -/

namespace Equiv

variable {Δ₁ Δ₂ : Definition}

theorem symm (h : Δ₁.Equiv Δ₂) : Δ₂.Equiv Δ₁ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  exact ⟨setEq_symm h₁, setEq_symm h₂, setEq_symm h₃, setEq_symm h₄, setEq_symm h₅,
    setEq_symm h₆, setEq_symm h₇, setEq_symm h₈, setEq_symm h₉, setEq_symm h₁₀⟩

theorem edges (h : Δ₁.Equiv Δ₂) : SetEq Δ₁.edges Δ₂.edges := h.2.2.2.2.2.1

theorem mem_edges (h : Δ₁.Equiv Δ₂) {e : Edge} : e ∈ Δ₁.edges ↔ e ∈ Δ₂.edges :=
  ⟨fun he => (edges h).1 he, fun he => (edges h).2 he⟩

theorem outgoing (h : Δ₁.Equiv Δ₂) (v : NodeId) : SetEq (Δ₁.outgoing v) (Δ₂.outgoing v) :=
  setEq_filter_map (edges h) _ _

theorem incoming (h : Δ₁.Equiv Δ₂) (v : NodeId) : SetEq (Δ₁.incoming v) (Δ₂.incoming v) :=
  setEq_filter_map (edges h) _ _

theorem nodeDef? (h : Δ₁.Equiv Δ₂) (h₂ : Δ₂.Admitted) (v : NodeId) :
    Δ₁.nodeDef? v = Δ₂.nodeDef? v :=
  find?_key_eq (key := NodeDef.node) h.2.2.2.2.2.2.1 h₂.nodeDefs_nodup v

theorem edgeDef? (h : Δ₁.Equiv Δ₂) (h₂ : Δ₂.Admitted) (e : EdgeId) :
    Δ₁.edgeDef? e = Δ₂.edgeDef? e :=
  find?_key_eq (key := EdgeDef.edge) h.2.2.2.2.2.2.2.1 h₂.edgeDefs_nodup e

theorem contract? (h : Δ₁.Equiv Δ₂) (h₂ : Δ₂.Admitted) (c : ContractId) :
    Δ₁.contract? c = Δ₂.contract? c :=
  find?_key_eq (key := Contract.id) h.2.2.2.1 h₂.contracts_nodup c

end Equiv

/-! ## Affected holders -/

/-- A current node that a rewrite `Δ ⟶ Δ'` does not affect survives with the same outgoing
edge identities and, when it is an `All` receiver of `Δ'`, the same incoming ones. -/
theorem not_affected {Δ Δ' : Definition} {v : NodeId} (hv : v ∈ Δ.nodes)
    (h : ¬ Affected Δ Δ' v) :
    v ∈ Δ'.nodes ∧ SetEq (Δ.outgoing v) (Δ'.outgoing v) ∧
      ∀ nd, Δ'.nodeDef? v = some nd → nd.ingress = .all →
        SetEq (Δ.incoming v) (Δ'.incoming v) :=
  ⟨Classical.byContradiction fun hn => h ⟨hv, .inl hn⟩,
    Classical.byContradiction fun hn => h ⟨hv, .inr (.inl hn)⟩,
    fun nd hnd hall => Classical.byContradiction fun hn =>
      h ⟨hv, .inr (.inr ⟨⟨nd, hnd, hall⟩, hn⟩)⟩⟩

/-! ## The replacement of a successful `structural?` -/

/-- What cleanup depends on in a successful `structural? Δ S pr m`: the deleted nodes are the
ones `m` binds outside the interface; the replacement is admitted, keeps the contracts and
every node, edge, and annotation outside the deleted part, and its new nodes and edges have
identities unused in `S`. -/
structure Shape (Δ : Definition) (S : State) (pr : Production) (m : Match)
    (rep : Replacement) : Prop where
  deleted : rep.deleted = (m.nodes.filter (·.1 ∉ pr.interfaceNodes)).map (·.2)
  admitted : rep.next.Admitted
  contracts : rep.next.contracts = Δ.contracts
  nodes : rep.next.nodes = Δ.nodes.filter (· ∉ rep.deleted) ++ rep.freshNodes
  freshNodes : ∀ v ∈ rep.freshNodes, v ∉ S.usedNodes
  nodeDefs : ∃ added, rep.next.nodeDefs = Δ.nodeDefs.filter (·.node ∉ rep.deleted) ++ added
  edges : ∃ gone : List EdgeId,
    rep.next.edges = Δ.edges.filter (·.id ∉ gone) ++ rep.freshEdges ∧
      ∃ added, rep.next.edgeDefs = Δ.edgeDefs.filter (·.edge ∉ gone) ++ added
  freshEdges : ∀ e ∈ rep.freshEdges, e.id ∉ S.usedEdges

/-- A successful `structural?` has the shape cleanup relies on. -/
theorem shape {Δ : Definition} {S : State} {pr : Production} {m : Match} {rep : Replacement}
    (h : structural? Δ S pr m = some rep) : Shape Δ S pr m rep := by
  simp only [structural?, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const, pure,
    Option.some.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hfn, hfe, -, hadm, rfl⟩ := h
  refine ⟨rfl, hadm, rfl, rfl, ?_, ⟨_, rfl⟩, ⟨_, rfl, _, rfl⟩, ?_⟩
  · intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
    exact hfn b hb
  · intro e he
    obtain ⟨b, hb, hbe⟩ := List.mem_filterMap.1 he
    obtain ⟨re, -, rfl⟩ := Option.map_eq_some_iff.1 hbe
    exact hfe b hb

namespace Shape

variable {Δ : Definition} {S : State} {pr : Production} {m : Match} {rep : Replacement}

/-- A current node survives exactly when it is not deleted. -/
theorem mem_nodes (hs : Shape Δ S pr m rep) (hS : WF Δ S) {v : NodeId} (hv : v ∈ Δ.nodes) :
    v ∈ rep.next.nodes ↔ v ∉ rep.deleted := by
  rw [hs.nodes, List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨-, hd⟩ | hf)
    · simpa using hd
    · exact absurd (hS.used_nodes hv) (hs.freshNodes v hf)
  · intro hd
    exact .inl ⟨hv, by simpa using hd⟩

/-- A retained node keeps its definition. -/
theorem nodeDef?_eq (hs : Shape Δ S pr m rep) (hΔ : Δ.Admitted) {v : NodeId}
    (hv : v ∈ Δ.nodes) (hd : v ∉ rep.deleted) : rep.next.nodeDef? v = Δ.nodeDef? v := by
  obtain ⟨added, hdefs⟩ := hs.nodeDefs
  obtain ⟨nd, hnd⟩ := nodeDef?_isSome hΔ hv
  rw [hnd]
  unfold Definition.nodeDef? at hnd ⊢
  rw [hdefs]
  apply find?_append_of_some
  rw [find?_filter_of_imp, hnd]
  intro a _ ha
  simp only [beq_iff_eq] at ha
  simpa [ha] using hd

/-- An edge identity present before and after names the same edge: a fresh edge has an
unused identity. -/
theorem edge_eq (hs : Shape Δ S pr m rep) (hΔ : Δ.Admitted) (hS : WF Δ S) {e e' : Edge}
    (he : e ∈ Δ.edges) (he' : e' ∈ rep.next.edges) (hid : e.id = e'.id) : e = e' := by
  obtain ⟨gone, hedges, -⟩ := hs.edges
  rw [hedges, List.mem_append] at he'
  rcases he' with he' | he'
  · exact eq_of_map_nodup hΔ.edges_nodup he (List.mem_filter.1 he').1 hid
  · exact (hs.freshEdges e' he' (hid ▸ List.mem_map_of_mem (hS.edge_log he))).elim

/-- A retained edge keeps its annotation. -/
theorem edgeDef?_eq (hs : Shape Δ S pr m rep) (hΔ : Δ.Admitted) (hS : WF Δ S) {e : Edge}
    (he : e ∈ Δ.edges) (he' : e ∈ rep.next.edges) :
    rep.next.edgeDef? e.id = Δ.edgeDef? e.id := by
  obtain ⟨gone, hedges, added, hdefs⟩ := hs.edges
  have hkept : e.id ∉ gone := by
    rw [hedges, List.mem_append] at he'
    rcases he' with he' | he'
    · simpa using (List.mem_filter.1 he').2
    · exact (hs.freshEdges e he' (List.mem_map_of_mem (hS.edge_log he))).elim
  obtain ⟨ed, hed⟩ := edgeDef?_isSome hΔ he
  rw [hed]
  unfold Definition.edgeDef? at hed ⊢
  rw [hdefs]
  apply find?_append_of_some
  rw [find?_filter_of_imp, hed]
  intro a _ ha
  simp only [beq_iff_eq] at ha
  simpa [ha] using hkept

/-- The contract registry is unchanged. -/
theorem contract?_eq (hs : Shape Δ S pr m rep) (c : ContractId) :
    rep.next.contract? c = Δ.contract? c := by
  unfold Definition.contract?
  rw [hs.contracts]

end Shape

/-! ## Cleanup -/

section Cleanup

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {evidence : List (Digest × Bytes)}

/-- Locality: cleanup keeps a live package whose holder the rewrite does not affect. -/
theorem cleanup_keep {Δ : Definition} {S : State} {pr : Production} {m : Match}
    {rep : Replacement} (hΔ : Δ.Admitted) (hS : WF Δ S) (hs : Shape Δ S pr m rep)
    {q : PackageId} {r : PackageRecord} (hr : S.packages q = some r) (hlive : r.status = .live)
    (hna : ¬ Affected Δ rep.next r.holder) :
    cleanup? accepts H Δ rep.next rep.deleted evidence r = some none := by
  have hv := hS.custody q r hr hlive
  obtain ⟨hmem, hout, hin⟩ := not_affected hv hna
  have hdel : r.holder ∉ rep.deleted := (hs.mem_nodes hS hv).1 hmem
  have hnd := hs.nodeDef?_eq hΔ hv hdel
  obtain ⟨nd, hnd'⟩ := nodeDef?_isSome hΔ hv
  unfold cleanup?
  rw [ite_eq_right hdel]
  cases hd : r.delivery with
  | none => exact ite_eq_left hout
  | some d =>
    have hholder : r.holder = d.receiver := by simp [PackageRecord.holder, hd]
    simp only [hnd, hnd']
    cases hing : nd.ingress with
    | any => rfl
    | all =>
      have hroute := hS.all_routes q r d nd hr hlive hd (hholder ▸ hnd') hing
      rw [← hholder] at hroute
      exact ite_eq_left ((hin nd (hnd.trans hnd') hing).1 hroute)

/-- Cleanup of `r` reads only whether its holder is deleted, the outgoing edge test, the
candidate edges leaving the holder with their annotations and contracts, the holder's
definition, and, for an `All` receipt, whether its edge is incoming. -/
theorem cleanup?_congr {Δ Δ' next next' : Definition} {deleted : List NodeId}
    {r : PackageRecord}
    (hout : SetEq (Δ.outgoing r.holder) (next.outgoing r.holder) ↔
      SetEq (Δ'.outgoing r.holder) (next'.outgoing r.holder))
    (hedges : ∀ e : Edge, e.source = r.holder → (e ∈ next.edges ↔ e ∈ next'.edges))
    (hdefs : ∀ e ∈ next.edges, e.source = r.holder → next.edgeDef? e.id = next'.edgeDef? e.id)
    (hcontracts : ∀ c, next.contract? c = next'.contract? c)
    (hnode : next.nodeDef? r.holder = next'.nodeDef? r.holder)
    (hin : ∀ d, r.delivery = some d → ∀ nd, next.nodeDef? r.holder = some nd →
      nd.ingress = .all → (d.edge ∈ next.incoming r.holder ↔ d.edge ∈ next'.incoming r.holder)) :
    cleanup? accepts H Δ next deleted evidence r =
      cleanup? accepts H Δ' next' deleted evidence r := by
  unfold cleanup?
  by_cases hdel : r.holder ∈ deleted
  · rw [ite_eq_left hdel, ite_eq_left hdel]
  rw [ite_eq_right hdel, ite_eq_right hdel]
  cases hd : r.delivery with
  | none =>
    by_cases ht : SetEq (Δ.outgoing r.holder) (next.outgoing r.holder)
    · rw [ite_eq_left ht, ite_eq_left (hout.1 ht)]
    rw [ite_eq_right ht, ite_eq_right (mt hout.2 ht)]
    dsimp only
    generalize hA : List.filter (fun x => decide (next.MetadataAccepts x r))
      (List.filter (fun x => x.source == r.holder) next.edges) = candA
    generalize hB : List.filter (fun x => decide (next'.MetadataAccepts x r))
      (List.filter (fun x => x.source == r.holder) next'.edges) = candB
    have hsrc : ∀ e ∈ candA, e ∈ next.edges ∧ e.source = r.holder := by
      intro e he
      rw [← hA] at he
      simp only [List.mem_filter, beq_iff_eq] at he
      exact he.1
    have hmem : ∀ e, e ∈ candA ↔ e ∈ candB := by
      intro e
      rw [← hA, ← hB]
      simp only [List.mem_filter, beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨he, hs⟩, hacc⟩
        exact ⟨⟨(hedges e hs).1 he, hs⟩,
          (metadataAccepts_congr (hdefs e he hs) hcontracts).1 hacc⟩
      · rintro ⟨⟨he, hs⟩, hacc⟩
        have he' := (hedges e hs).2 he
        exact ⟨⟨he', hs⟩, (metadataAccepts_congr (hdefs e he' hs) hcontracts).2 hacc⟩
    by_cases hc : candA = []
    · rw [ite_eq_left hc, ite_eq_left ((eq_nil_congr hmem).1 hc)]
    rw [ite_eq_right hc, ite_eq_right (mt (eq_nil_congr hmem).2 hc)]
    have hany : ∀ bytes : Bytes,
        (candA.any fun e => (next.edgeDef? e.id).any fun ed => accepts ed.packageContract bytes) =
          candB.any fun e => (next'.edgeDef? e.id).any fun ed =>
            accepts ed.packageContract bytes :=
      fun _ => any_congr hmem fun e he => by rw [hdefs e (hsrc e he).1 (hsrc e he).2]
    simp only [hany]
  | some d =>
    dsimp only
    rw [hnode]
    cases hnd : next'.nodeDef? r.holder with
    | none => rfl
    | some nd =>
      dsimp only
      cases hing : nd.ingress with
      | any => rfl
      | all =>
        dsimp only
        have hiff := hin d hd nd (hnode.trans hnd) hing
        by_cases hmem : d.edge ∈ next.incoming r.holder
        · rw [ite_eq_left hmem, ite_eq_left (hiff.1 hmem)]
        · rw [ite_eq_right hmem, ite_eq_right (mt hiff.2 hmem)]

/-- A rewrite decides the same fate for a package before and after a second rewrite that
does not affect its holder. The first applies `pr` at `m`, to `Δ` as `repA` and to `Δb` as
`repBA`; `Δb` keeps the holder's outgoing edges; the second takes `repA.next` to `repAB.next`
without affecting the holder; and both orders end in equivalent definitions. -/
theorem cleanup_eq {Δ Δb : Definition} {S Sa Sb : State} {pr pr' : Production} {m m' : Match}
    {repA repBA repAB : Replacement} (hS : WF Δ S) (hsA : Shape Δ S pr m repA)
    (hsBA : Shape Δb Sb pr m repBA) (hSa : WF repA.next Sa)
    (hsAB : Shape repA.next Sa pr' m' repAB) (hsame : repAB.next.Equiv repBA.next)
    {r : PackageRecord} (hv : r.holder ∈ Δ.nodes)
    (hout : SetEq (Δ.outgoing r.holder) (Δb.outgoing r.holder))
    (hna : ¬ Affected repA.next repAB.next r.holder) :
    cleanup? accepts H Δ repA.next repA.deleted evidence r =
      cleanup? accepts H Δb repBA.next repBA.deleted evidence r := by
  rw [hsBA.deleted, ← hsA.deleted]
  by_cases hdel : r.holder ∈ repA.deleted
  · unfold cleanup?
    rw [ite_eq_left hdel, ite_eq_left hdel]
  have hΔa := hsA.admitted
  have hΔba := hsBA.admitted
  have hva : r.holder ∈ repA.next.nodes := (hsA.mem_nodes hS hv).2 hdel
  obtain ⟨hvab, hout', hin'⟩ := not_affected hva hna
  have hdab : r.holder ∉ repAB.deleted := (hsAB.mem_nodes hSa hva).1 hvab
  -- The second rewrite keeps every edge leaving the holder, and adds none.
  have hkeep : ∀ e : Edge, e.source = r.holder →
      (e ∈ repA.next.edges ↔ e ∈ repAB.next.edges) := by
    intro e hs
    constructor
    · intro he
      have hid : e.id ∈ repA.next.outgoing r.holder := hs ▸ mem_outgoing_of_mem he
      obtain ⟨e', he', -, hid'⟩ := mem_outgoing.1 (hout'.1 hid)
      rwa [hsAB.edge_eq hΔa hSa he he' hid'.symm]
    · intro he
      have hid : e.id ∈ repAB.next.outgoing r.holder := hs ▸ mem_outgoing_of_mem he
      obtain ⟨e', he', -, hid'⟩ := mem_outgoing.1 (hout'.2 hid)
      rwa [← hsAB.edge_eq hΔa hSa he' he hid']
  apply cleanup?_congr
  · exact setEq_congr hout (setEq_trans hout' (Equiv.outgoing hsame _))
  · intro e hs
    exact (hkeep e hs).trans (Equiv.mem_edges hsame)
  · intro e he hs
    rw [← hsAB.edgeDef?_eq hΔa hSa he ((hkeep e hs).1 he), Equiv.edgeDef? hsame hΔba]
  · intro c
    rw [← hsAB.contract?_eq, Equiv.contract? hsame hΔba]
  · rw [← hsAB.nodeDef?_eq hΔa hva hdab, Equiv.nodeDef? hsame hΔba]
  · intro d _ nd hnd hall
    have hnd' : repAB.next.nodeDef? r.holder = some nd :=
      (hsAB.nodeDef?_eq hΔa hva hdab).trans hnd
    have hab := hin' nd hnd' hall
    exact ⟨fun h => (Equiv.incoming hsame _).1 (hab.1 h),
      fun h => hab.2 ((Equiv.incoming hsame _).2 h)⟩

end Cleanup

end Ontography.Proofs.Commute
