import Ontography.Rewrite
import Ontography.Proofs.Basic

/-!
# Vocabulary extension preserves the invariants

An extension replaces the schema and the contract registry by larger ones, admits the
result, and records one definition change at the successor revision. `extend_spec` states
this exactly: nodes, edges, annotations, transition rules, and roots stay, and of the state
only `changeLog` and `revision` change.

Every invariant then carries over. The two fields that name the schema, the authority of a
root trigger and schema closure, weaken along the grown vocabulary. The new change
revision `S.revision + 1` exceeds every recorded change and every retirement stamp, so the
change log stays duplicate-free and I4 still tells explicit retirements from structural ones.
I6 gains one definition change for its one revision.
-/

namespace Ontography.Proofs

variable {Δ Δ' : Definition} {S S' : State}

namespace Sys

/-- The premises of an extension: the vocabulary and the registry only grow, and the extended
definition is admitted. -/
theorem extend_guards {schema : Schema} {contracts : List Contract}
    (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ.schema.nodeTypes ⊆ schema.nodeTypes ∧ Δ.schema.objectTypes ⊆ schema.objectTypes ∧
      Δ.schema.tags ⊆ schema.tags ∧ Δ.contracts ⊆ contracts ∧
      ({ Δ with schema := schema, contracts := contracts } : Definition).Admitted := by
  simp only [extend, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨⟨hn, ho, ht⟩, hc, -, hadm, -⟩ := h
  exact ⟨hn, ho, ht, hc, hadm⟩

end Sys

/-- The extension rule, exactly (§6): only the vocabulary and the counters change. -/
theorem extend_spec {schema : Schema} {contracts : List Contract}
    (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ' = { Δ with schema := schema, contracts := contracts } ∧
      S' = { S with changeLog := S.changeLog ++ [S.revision + 1], revision := S.revision + 1 } := by
  simp only [extend, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, -, -, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

-- The extended definition is admitted by the rule's own guard, so `hΔ` is unused; it is kept
-- so that the statement is exactly `Ontography.wf_extend`.
set_option linter.unusedVariables false in
/-- An extension admits its replacement definition and preserves every invariant under it. -/
theorem wf_extend (hΔ : Δ.Admitted) (hS : WF Δ S) {schema : Schema}
    {contracts : List Contract} (h : extend Δ S schema contracts = some (Δ', S')) :
    Δ'.Admitted ∧ WF Δ' S' := by
  obtain ⟨-, hobj, htags, -, hadm⟩ := Sys.extend_guards h
  obtain ⟨rfl, rfl⟩ := extend_spec h
  refine ⟨hadm, ?_⟩
  -- The new change revision is later than every recorded one.
  have hnew : ∀ n ∈ S.changeLog, n ≠ S.revision + 1 := fun n hn => by
    have := (hS.changeLog_le n hn).2
    omega
  exact
    { activationIds_nodup := hS.activationIds_nodup
      activations_dom := hS.activations_dom
      packageIds_nodup := hS.packageIds_nodup
      packages_dom := hS.packages_dom
      ownership := hS.ownership
      outputs_recorded := hS.outputs_recorded
      consumed := hS.consumed
      inputs := hS.inputs
      join_authority := hS.join_authority
      triggers := fun b act hb => by
        -- A root's authority stays in the grown tag vocabulary.
        obtain ⟨hpkgs, horig⟩ := hS.triggers b act hb
        exact ⟨hpkgs, fun v α ht =>
          ⟨(horig v α ht).1, List.Subset.trans (horig v α ht).2 htags⟩⟩
      delivery := hS.delivery
      birth_edge := hS.birth_edge
      retirement := fun p r ret hr hs => by
        -- Every stamp predates the new change, so I4's phase test is unchanged.
        obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hS.retirement p r ret hr hs
        refine ⟨h₁, h₂, h₃, h₄, h₅, Nat.le_succ_of_le h₆, h₇, ?_⟩
        have hne : ret.revision ≠ S.revision + 1 := by omega
        show _ ↔ ret.revision ∉ S.changeLog ++ [S.revision + 1]
        rw [List.mem_append, List.mem_singleton, or_iff_left hne]
        exact h₈
      explicit_stamps := hS.explicit_stamps
      custody := hS.custody
      all_routes := hS.all_routes
      revision := by
        -- One more definition change, and no other count moves.
        show S.revision + 1 = S.activationIds.length + S.explicitTransfers +
          S.explicitRetirements + (S.changeLog ++ [S.revision + 1]).length
        have := hS.revision
        rw [State.definitionChanges] at this
        rw [List.length_append, List.length_singleton]
        omega
      changeLog_nodup := by
        show (S.changeLog ++ [S.revision + 1]).Nodup
        rw [List.nodup_append]
        refine ⟨hS.changeLog_nodup, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro n hn m hm
        rw [List.mem_singleton] at hm
        subst hm
        exact hnew n hn
      changeLog_le := fun n hn => by
        rcases List.mem_append.1 hn with hn | hn
        · have := hS.changeLog_le n hn
          exact ⟨this.1, Nat.le_succ_of_le this.2⟩
        · rw [List.mem_singleton] at hn
          subst hn
          exact ⟨Nat.le_add_left _ _, Nat.le_refl _⟩
      used_nodes := hS.used_nodes
      edge_log := hS.edge_log
      edge_log_ids := hS.edge_log_ids
      activation_nodes_used := hS.activation_nodes_used
      edge_log_nodes := hS.edge_log_nodes
      used_nonempty := hS.used_nonempty
      causal_order := hS.causal_order
      schema_closure := fun p r hr => by
        -- Object types and authorities stay in the grown vocabulary.
        obtain ⟨ho, ht⟩ := hS.schema_closure p r hr
        exact ⟨hobj ho, List.Subset.trans ht htags⟩ }

end Ontography.Proofs
