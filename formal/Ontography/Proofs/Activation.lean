import Ontography.Proofs.ActivationLemmas

/-!
# Activation preserves well-formedness

`wf_accept` checks every field of `WF` for the successor of an admissible activation, and
`wf_activate` combines it with the inversion `activate_inv`.
-/

namespace Ontography.Proofs.Activation

variable {Δ : Definition} {S : State} {a : ActivationId} {act : Activation} {α : Authority}
  {outs : List (Output × PackageRecord)}

/-- The successor of an admissible activation of a well-formed state is well formed. -/
theorem wf_accept (hΔ : Δ.Admitted) (hS : WF Δ S) (hA : Admissible Δ S a act α outs) :
    WF Δ (S.accept a act (outs.map Prod.snd)) where
  activationIds_nodup := by
    show (S.activationIds ++ [a]).Nodup
    have ha := fresh_not_mem hS hA.fresh
    rw [List.nodup_append]
    refine ⟨hS.activationIds_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    subst hy
    subst hxy
    exact ha hx
  activations_dom := by
    intro b
    rw [accept_activations]
    show _ ↔ b ∈ S.activationIds ++ [a]
    rw [List.mem_append, List.mem_singleton]
    by_cases hb : b = a
    · subst hb
      simp
    · rw [ite_eq_right hb, hS.activations_dom b]
      simp [hb]
  packageIds_nodup := by
    show (S.packageIds ++ (List.range (outs.map Prod.snd).length).map (PackageId.mk a)).Nodup
    rw [List.nodup_append]
    refine ⟨hS.packageIds_nodup,
      List.Pairwise.map _ (fun i j hij h => hij (PackageId.mk.inj h).2) List.nodup_range, ?_⟩
    intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨r, hr⟩ := packages_of_mem hS hp
    exact producer_ne hS hA.fresh hr (by rw [hpq])
  packages_dom := by
    intro q
    show _ ↔ q ∈ S.packageIds ++ (List.range (outs.map Prod.snd).length).map (PackageId.mk a)
    rw [accept_packages, List.mem_append]
    by_cases hqa : q.producer = a
    · rw [ite_eq_left hqa]
      have hq : q ∉ S.packageIds := fun hq => by
        obtain ⟨r, hr⟩ := packages_of_mem hS hq
        exact producer_ne hS hA.fresh hr hqa
      obtain ⟨b, i⟩ := q
      dsimp only at hqa
      subst hqa
      simp [hq, List.mem_map, List.mem_range, List.getElem?_map]
    · rw [ite_eq_right hqa]
      have hq : q ∉ (List.range (outs.map Prod.snd).length).map (PackageId.mk a) := by
        intro hq
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
        exact hqa rfl
      rw [or_iff_left hq, ← hS.packages_dom q]
      split <;> simp
  ownership := by
    intro p r h
    rcases pkg_cases hA h with ⟨o, hpa, hx, hspec⟩ |
        ⟨r₀, hpa, _, h0, _, _, rfl⟩ | ⟨hpa, _, h0⟩
    · refine ⟨act, o, ?_, ?_, hspec.objectType, hspec.authority, hspec.digest,
        hspec.producerNode⟩
      · rw [accept_activations, ite_eq_left hpa]
      · rw [hA.outputs_eq, List.getElem?_map, hx]
        rfl
    · obtain ⟨act', o, hact, ho, h1, h2, h3, h4⟩ := hS.ownership p r₀ h0
      exact ⟨act', o, by rw [accept_activations, ite_eq_right hpa, hact], ho, h1, h2, h3, h4⟩
    · obtain ⟨act', o, hact, ho, h1, h2, h3, h4⟩ := hS.ownership p r h0
      exact ⟨act', o, by rw [accept_activations, ite_eq_right hpa, hact], ho, h1, h2, h3, h4⟩
  outputs_recorded := by
    intro b act' hb i hi
    rw [accept_activations] at hb
    by_cases hba : b = a
    · rw [ite_eq_left hba, Option.some.injEq] at hb
      subst hb hba
      rw [hA.outputs_eq, List.length_map] at hi
      rw [accept_packages, ite_eq_left rfl]
      simp [List.getElem?_map, List.getElem?_eq_getElem hi]
    · rw [ite_eq_right hba] at hb
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hS.outputs_recorded b act' hb i hi)
      rw [accept_packages, ite_eq_right hba]
      split <;> simp [hr]
  consumed := by
    intro p r b h hst
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, hin, _, _, _, rfl⟩ |
        ⟨_, _, h0⟩
    · rw [hspec.status] at hst
      cases hst
    · cases hst
      exact ⟨act, by rw [accept_activations, ite_eq_left rfl], hin⟩
    · obtain ⟨act', hact, hmem⟩ := hS.consumed p r b h0 hst
      have hba : b ≠ a := fun e => by
        rw [e, hA.fresh] at hact
        cases hact
      exact ⟨act', by rw [accept_activations, ite_eq_right hba, hact], hmem⟩
  inputs := by
    intro b act' hb p hp
    rw [accept_activations] at hb
    by_cases hba : b = a
    · rw [ite_eq_left hba, Option.some.injEq] at hb
      subst hb hba
      obtain ⟨r₀, d, h0, _, hd, hrecv, _⟩ := hA.trigger.inputs p hp
      refine ⟨{ r₀ with status := .consumed b }, d, ?_, rfl, hd, hrecv⟩
      rw [accept_packages, ite_eq_right (producer_ne hS hA.fresh h0), ite_eq_left hp, h0]
      rfl
    · rw [ite_eq_right hba] at hb
      obtain ⟨r, d, h0, hst, hd, hrecv⟩ := hS.inputs b act' hb p hp
      exact ⟨r, d, accept_of_not_live hS hA h0 (by rw [hst]; simp), hst, hd, hrecv⟩
  join_authority := by
    intro b act' hb p hp q hq r s hr hs
    rw [accept_activations] at hb
    by_cases hba : b = a
    · rw [ite_eq_left hba, Option.some.injEq] at hb
      subst hb
      have key : ∀ p r, p ∈ act.trigger.inputs →
          (S.accept a act (outs.map Prod.snd)).packages p = some r → SetEq r.authority α := by
        intro p r hp hr
        rcases pkg_cases hA hr with ⟨_, hpa, _, _⟩ | ⟨r₀, _, _, _, _, hauth, rfl⟩ |
            ⟨_, hin, _⟩
        · obtain ⟨_, _, h0, _⟩ := hA.trigger.inputs p hp
          exact absurd hpa (producer_ne hS hA.fresh h0)
        · exact hauth
        · exact absurd hp hin
      exact setEq_trans (key p r hp hr) (setEq_symm (key q s hq hs))
    · rw [ite_eq_right hba] at hb
      obtain ⟨r₀, _, h0, hst, _⟩ := hS.inputs b act' hb p hp
      obtain ⟨s₀, _, h0', hst', _⟩ := hS.inputs b act' hb q hq
      rw [accept_of_not_live hS hA h0 (by rw [hst]; simp), Option.some.injEq] at hr
      rw [accept_of_not_live hS hA h0' (by rw [hst']; simp), Option.some.injEq] at hs
      subst hr hs
      exact hS.join_authority b act' hb p hp q hq r₀ s₀ h0 h0'
  triggers := by
    intro b act' hb
    rw [accept_activations] at hb
    by_cases hba : b = a
    · rw [ite_eq_left hba, Option.some.injEq] at hb
      subst hb
      exact ⟨fun I h => ⟨hA.trigger.pkgs_ne I h, hA.trigger.pkgs_nodup I h⟩,
        fun w β h => ⟨hA.trigger.orig_node w β h, hA.trigger.orig_sub w β h⟩⟩
    · rw [ite_eq_right hba] at hb
      exact hS.triggers b act' hb
  delivery := by
    intro p r d h hd
    show _ ∈ S.edgeLog
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, h0, _, _, rfl⟩ | ⟨_, _, h0⟩
    · rcases hspec.route with ⟨_, hnone⟩ | ⟨edge, hedge, hsrc, _, hdel⟩
      · rw [hnone] at hd
        cases hd
      · rw [hdel, Option.some.injEq] at hd
        subst hd
        rw [hspec.producerNode, ← hsrc]
        exact hS.edge_log hedge
    · exact hS.delivery p r₀ d h0 hd
    · exact hS.delivery p r d h0 hd
  birth_edge := by
    intro p r o e h ho he
    rw [accept_output] at ho
    rcases pkg_cases hA h with ⟨o', hpa, hx, hspec⟩ | ⟨r₀, hpa, _, h0, _, _, rfl⟩ |
        ⟨hpa, _, h0⟩
    · rw [ite_eq_left hpa, hA.outputs_eq, List.getElem?_map, hx, Option.map_some,
        Option.some.injEq] at ho
      subst ho
      rcases hspec.route with ⟨hnone, _⟩ | ⟨edge, _, _, hoe, hdel⟩
      · rw [hnone] at he
        cases he
      · rw [hoe, Option.some.injEq] at he
        subst he
        exact ⟨_, hdel⟩
    · rw [ite_eq_right hpa] at ho
      exact hS.birth_edge p r₀ o e h0 ho he
    · rw [ite_eq_right hpa] at ho
      exact hS.birth_edge p r o e h0 ho he
  retirement := by
    intro p r ret h hst
    have h0 := pre_of_retired hA h hst
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hS.retirement p r ret h0 hst
    exact ⟨h1, h2, h3, fun b hb => accept_activations_isSome (h4 b hb), h5,
      Nat.le_succ_of_le h6, h7, h8⟩
  explicit_stamps := by
    intro p q r s ρ σ hp hq hr hs h1 h2 h3
    exact hS.explicit_stamps p q r s ρ σ (pre_of_retired hA hp hr)
      (pre_of_retired hA hq hs) hr hs h1 h2 h3
  custody := by
    intro p r h hlive
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, _, _, _, rfl⟩ | ⟨_, _, h0⟩
    · unfold PackageRecord.holder
      rcases hspec.route with ⟨_, hnone⟩ | ⟨edge, hedge, _, _, hdel⟩
      · rw [hnone, hspec.producerNode]
        exact hA.node_mem
      · rw [hdel]
        exact (hΔ.endpoints edge hedge).2
    · cases hlive
    · exact hS.custody p r h0 hlive
  all_routes := by
    intro p r d nd h hlive hd hnd hall
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, _, _, _, rfl⟩ | ⟨_, _, h0⟩
    · rcases hspec.route with ⟨_, hnone⟩ | ⟨edge, hedge, _, _, hdel⟩
      · rw [hnone] at hd
        cases hd
      · rw [hdel, Option.some.injEq] at hd
        subst hd
        exact mem_incoming hedge
    · cases hlive
    · exact hS.all_routes p r d nd h0 hlive hd hnd hall
  revision := by
    rw [explicitTransfers_eq hS hA, explicitRetirements_eq hS hA]
    show S.revision + 1 = (S.activationIds ++ [a]).length + _ + _ + S.changeLog.length
    rw [List.length_append, List.length_singleton, hS.revision]
    unfold State.definitionChanges
    omega
  changeLog_nodup := hS.changeLog_nodup
  changeLog_le := fun n hn =>
    ⟨(hS.changeLog_le n hn).1, Nat.le_succ_of_le (hS.changeLog_le n hn).2⟩
  used_nodes := hS.used_nodes
  edge_log := hS.edge_log
  edge_log_ids := hS.edge_log_ids
  activation_nodes_used := by
    intro b act' hb
    rw [accept_activations] at hb
    split at hb
    · rw [Option.some.injEq] at hb
      subst hb
      exact hS.used_nodes hA.node_mem
    · exact hS.activation_nodes_used b act' hb
  edge_log_nodes := hS.edge_log_nodes
  used_nonempty := hS.used_nonempty
  causal_order := by
    intro p r b h hst
    show (S.activationIds ++ [a]).idxOf p.producer < (S.activationIds ++ [a]).idxOf b
    have ha := fresh_not_mem hS hA.fresh
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, h0, _, _, rfl⟩ |
        ⟨_, _, h0⟩
    · rw [hspec.status] at hst
      cases hst
    · cases hst
      have hp := producer_mem hS h0
      rw [List.idxOf_append, ite_eq_left hp, List.idxOf_append, ite_eq_right ha]
      simp only [List.idxOf_cons_self, Nat.zero_add]
      exact List.idxOf_lt_length_of_mem hp
    · have hp := producer_mem hS h0
      obtain ⟨act', hact, _⟩ := hS.consumed p r b h0 hst
      have hb : b ∈ S.activationIds := (hS.activations_dom b).mp (by rw [hact]; rfl)
      rw [List.idxOf_append, ite_eq_left hp, List.idxOf_append, ite_eq_left hb]
      exact hS.causal_order p r b h0 hst
  schema_closure := by
    intro p r h
    rcases pkg_cases hA h with ⟨_, _, _, hspec⟩ | ⟨r₀, _, _, h0, _, _, rfl⟩ | ⟨_, _, h0⟩
    · exact ⟨hspec.objectType_mem, hspec.authority_sub⟩
    · exact hS.schema_closure p r₀ h0
    · exact hS.schema_closure p r h0

end Ontography.Proofs.Activation

namespace Ontography.Proofs

/-- Activation preserves every invariant. -/
theorem wf_activate {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
    {Δ : Definition} {S S' : State} (hΔ : Δ.Admitted) (hS : WF Δ S) {a : ActivationId}
    {prop : Proposal} (h : activate accepts H Δ S a prop = some S') : WF Δ S' := by
  obtain ⟨act, α, outs, hA, rfl⟩ := Activation.activate_inv hΔ h
  exact Activation.wf_accept hΔ hS hA

end Ontography.Proofs
