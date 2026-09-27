import Ontography.Invariants

/-!
# The empty state is well formed

The empty state has no activations and no packages, so every field quantified over them holds
vacuously. Its lifetime identities are exactly the definition's nodes and edges, so I7 reduces
to admission: edge identities are unique and every endpoint is a node.
-/

namespace Ontography.Proofs

variable {Δ : Definition}

/-- The empty state of an admitted definition is well formed. -/
theorem wf_initial (hΔ : Δ.Admitted) : WF Δ (State.initial Δ) where
  activationIds_nodup := List.nodup_nil
  activations_dom _ := by simp [State.initial]
  packageIds_nodup := List.nodup_nil
  packages_dom _ := by simp [State.initial]
  ownership _ _ h := nomatch h
  outputs_recorded _ _ h := nomatch h
  consumed _ _ _ h := nomatch h
  inputs _ _ h := nomatch h
  join_authority _ _ h := nomatch h
  triggers _ _ h := nomatch h
  delivery _ _ _ h := nomatch h
  birth_edge _ _ _ _ h := nomatch h
  retirement _ _ _ h := nomatch h
  explicit_stamps _ _ _ _ _ _ h := nomatch h
  custody _ _ h := nomatch h
  all_routes _ _ _ _ h := nomatch h
  revision := rfl
  changeLog_nodup := List.nodup_nil
  changeLog_le _ h := nomatch h
  used_nodes := List.Subset.refl _
  edge_log := List.Subset.refl _
  edge_log_ids := hΔ.edges_nodup
  activation_nodes_used _ _ h := nomatch h
  edge_log_nodes := hΔ.endpoints
  causal_order _ _ _ h := nomatch h
  schema_closure _ _ h := nomatch h

end Ontography.Proofs
