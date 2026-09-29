import Ontography.SystemTheorems

/-!
# Runs (T6)

Facts about whole runs of a workflow rather than single transitions: an accepted activation
never changes, and an identity that has left the definition never returns (TRANSITIONS §5,
T6). They follow from the frame and freshness theorems by induction over the run.
-/

namespace Ontography

section

variable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (permits : Policy)

/-- `(Δ', S')` follows `(Δ, S)` by zero or more transitions. -/
inductive SysSteps : Definition → State → Definition → State → Prop
  | refl {Δ : Definition} {S : State} : SysSteps Δ S Δ S
  | tail {Δ Δ₁ Δ₂ : Definition} {S S₁ S₂ : State} (op : SysOp) :
    SysSteps Δ S Δ₁ S₁ → sysStep accepts H permits Δ₁ S₁ op = some (Δ₂, S₂) →
      SysSteps Δ S Δ₂ S₂

end

end Ontography
