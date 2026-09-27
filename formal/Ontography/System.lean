import Ontography.Rewrite

/-!
# Running workflows

A running workflow is a definition together with a state bound to it. Its transitions are
the fixed-definition steps of `Step`, rewrites, and extensions; the last two replace the
definition. The rewrite grammar is a trusted policy supplied with the workflow.
-/

namespace Ontography

/-- The five transition kinds, grouped by whether they keep the definition. -/
inductive SysOp where
  | step (op : Op)
  | rewrite (request : RewriteRequest) (evidence : List (Digest × Bytes))
  | extend (schema : Schema) (contracts : List Contract)
  deriving DecidableEq, Repr

section

variable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest)
  (grammar : List Production)

/-- One transition of a running workflow `(Δ, S)`. -/
def sysStep (Δ : Definition) (S : State) : SysOp → Option (Definition × State)
  | .step op => (step accepts H Δ S op).map ((Δ, ·))
  | .rewrite req evidence => rewrite accepts H grammar Δ S req evidence
  | .extend schema contracts => extend Δ S schema contracts

/-- Running workflows reachable from the empty state of an admitted definition. -/
inductive SysReachable : Definition → State → Prop
  | initial {Δ : Definition} : Δ.Admitted → SysReachable Δ (State.initial Δ)
  | next {Δ Δ' : Definition} {S S' : State} (op : SysOp) :
    SysReachable Δ S → sysStep accepts H grammar Δ S op = some (Δ', S') →
      SysReachable Δ' S'

end

end Ontography
