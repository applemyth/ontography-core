import Ontography.Proofs.Transfer
import Ontography.Proofs.Retire

/-!
# Each transition advances the revision once

Every successful rule returns a successor whose revision is one more: activation through
`State.accept`, and transfer and explicit retirement through `Frame.setRecord`.
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S S' : State}

namespace Frame

/-- An admitted activation's successor is an acceptance. -/
theorem activate_eq_some {a : ActivationId} {prop : Proposal}
    (h : activate accepts H Δ S a prop = some S') :
    ∃ act records, S' = S.accept a act records := by
  simp only [activate, bind, Option.bind_eq_some_iff, guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨-, _, -, _, -, -, _, -, rfl⟩ := h
  exact ⟨_, _, rfl⟩

end Frame

/-- Each transition advances the revision exactly once. -/
theorem step_revision {op : Op} (h : step accepts H Δ S op = some S') :
    S'.revision = S.revision + 1 := by
  cases op with
  | activate a prop =>
    obtain ⟨_, _, rfl⟩ := Frame.activate_eq_some h
    rfl
  | transfer p e payload =>
    obtain ⟨_, _, -, -, -, -, -, rfl⟩ := Frame.transfer_eq_some h
    rfl
  | retire p evidence =>
    obtain ⟨_, -, -, -, rfl⟩ := Frame.retire_eq_some h
    rfl

end Ontography.Proofs
