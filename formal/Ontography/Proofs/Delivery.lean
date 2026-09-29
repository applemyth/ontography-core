import Ontography.Proofs.Runs

/-!
# I3 at the time of delivery

Two rules make deliveries, and each looks its edge up in the definition it applies to.
Activation delivers an output at birth over the edge its emission names, which `emission?`
requires to leave the executing node, the output's producer node. Transfer delivers a package
that has no delivery over an edge it requires to leave the package's producer node.

Every other change to a record keeps its delivery: activation only consumes its inputs,
explicit retirement and rewrites only retire live packages, and a rewrite records no new
package. An extension changes no record.
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {permits : Policy} {Δ Δ' : Definition} {S S' : State}

namespace Delivery

/-- An admitted output is born delivered only over an edge of the definition, from the
output's producer node to the receiver. -/
theorem emission_delivery {v : NodeId} {α : Authority} {em : Emission}
    {x : Output × PackageRecord} (h : emission? accepts H Δ v α em = some x) {d : Delivery}
    (hd : x.2.delivery = some d) :
    (⟨d.edge, x.2.producerNode, d.receiver⟩ : Edge) ∈ Δ.edges := by
  obtain ⟨dest, auth, payload⟩ := em
  cases dest with
  | delivered e =>
    -- The emission's edge leaves the executing node.
    cases auth <;>
      simp only [emission?, bind, Option.bind_eq_some_iff, Common.guard_eq_some, pure,
        Option.some.injEq] at h
    all_goals
      obtain ⟨_, _, _, _, edge, hedge, _, rfl, _, _, _, _, _, _, _, _, rfl⟩ := h
      cases hd
      obtain ⟨hmem, rfl⟩ := Common.edge?_mem hedge
      exact hmem
  | outbound o =>
    -- An outbound output is born undelivered.
    cases auth <;>
      simp only [emission?, bind, Option.bind_eq_some_iff, Common.guard_eq_some, pure,
        Option.some.injEq] at h
    all_goals
      obtain ⟨_, _, _, _, _, _, rfl⟩ := h
      cases hd

end Delivery

/-- I3 at the time of delivery: a transition keeps every delivery already made and makes new
ones only over an edge of the definition it applies to, from the producer's node to the
receiver. -/
theorem sysStep_delivery {op : SysOp} (h : sysStep accepts H permits Δ S op = some (Δ', S'))
    {p : PackageId} {r' : PackageRecord} {d : Delivery} (hr' : S'.packages p = some r')
    (hd : r'.delivery = some d) :
    (∃ r, S.packages p = some r ∧ r.delivery = some d) ∨
      (⟨d.edge, r'.producerNode, d.receiver⟩ : Edge) ∈ Δ.edges := by
  cases op with
  | step op =>
    obtain ⟨-, hstep⟩ := Sys.step_eq_some h
    cases op with
    | activate a prop =>
      simp only [step, activate, bind, Option.bind_eq_some_iff, Common.guard_eq_some,
        exists_const, pure, Option.some.injEq] at hstep
      obtain ⟨-, ⟨v, α⟩, -, nd, -, -, outs, houts, rfl⟩ := hstep
      rw [Activation.accept_packages] at hr'
      split at hr'
      · -- A new output is delivered at birth over the edge its emission names.
        rw [List.getElem?_map] at hr'
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hr'
        obtain ⟨em, -, hem⟩ := (Activation.mapM_some houts).2 x (List.mem_of_getElem? hx)
        exact .inr (Delivery.emission_delivery hem hd)
      · split at hr'
        · -- A consumed input keeps its delivery.
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hr'
          exact .inl ⟨r, hr, hd⟩
        · exact .inl ⟨r', hr', hd⟩
    | transfer q e payload =>
      obtain ⟨r, edge, hr, -, -, hedge, hsrc, rfl⟩ := Common.transfer_eq_some hstep
      rcases Common.setRecord_packages_eq_some.1 hr' with ⟨rfl, rfl⟩ | ⟨-, hr'⟩
      · -- The transferred package crosses an edge leaving its producer's node.
        cases hd
        obtain ⟨hmem, rfl⟩ := Common.edge?_mem hedge
        refine .inr ?_
        show (⟨edge.id, r.producerNode, edge.target⟩ : Edge) ∈ Δ.edges
        rw [← hsrc]
        exact hmem
      · exact .inl ⟨r', hr', hd⟩
    | retire q evidence =>
      -- Explicit retirement changes only a status.
      obtain ⟨r, hr, -, -, rfl⟩ := Common.retire_eq_some hstep
      rcases Common.setRecord_packages_eq_some.1 hr' with ⟨rfl, rfl⟩ | ⟨-, hr'⟩
      · exact .inl ⟨r, hr, hd⟩
      · exact .inl ⟨r', hr', hd⟩
  | rewrite req evidence =>
    -- A rewrite records no new package and changes a recorded one at most by retiring it.
    obtain ⟨-, -, -, -, hpkg, -⟩ := Sys.rewrite_eq_some h
    cases hr : S.packages p with
    | none =>
      rw [Runs.rewrite_absent h hr] at hr'
      cases hr'
    | some r =>
      refine .inl ⟨r, rfl, ?_⟩
      rcases hpkg p r hr with h' | ⟨-, ret, h'⟩ <;> rw [h'] at hr' <;> cases hr' <;> exact hd
  | extend schema contracts =>
    -- An extension changes no record.
    obtain ⟨-, rfl⟩ := extend_spec h
    exact .inl ⟨r', hr', hd⟩

end Ontography.Proofs
