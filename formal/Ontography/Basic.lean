/-!
# Identifiers, payloads, and finite sets

The vocabulary shared by every part of the model. Identifiers are strings, as
in the Rust kernel. Activation identities are natural numbers standing for the
kernel's `u128` values, and a package identity pairs its producing activation
with an output ordinal.

Lists stand for finite sets throughout: only membership matters. `⊆` is list
inclusion and `SetEq` is equality as sets, so an authority stored in one order
equals the same tags stored in another.
-/

namespace Ontography

abbrev NodeId := String
abbrev EdgeId := String
abbrev NodeType := String
abbrev ObjectType := String
abbrev Tag := String
abbrev ContractId := String
abbrev ActivationId := Nat
abbrev Digest := String
abbrev Bytes := List UInt8

/-- A package occurrence `p = (a, i)`: output `i` of activation `a`. -/
structure PackageId where
  producer : ActivationId
  output : Nat
  deriving DecidableEq, Repr

/-- Two lists have the same elements. -/
def SetEq {α : Type} (a b : List α) : Prop := a ⊆ b ∧ b ⊆ a

instance {α : Type} [DecidableEq α] (a b : List α) : Decidable (SetEq a b) :=
  inferInstanceAs (Decidable (a ⊆ b ∧ b ⊆ a))

/-- An authority `α ⊆ U` is a finite set of tags. -/
abbrev Authority := List Tag

/-- `f` updated so that `k ↦ v`. -/
def update {α β : Type} [DecidableEq α] (f : α → Option β) (k : α) (v : β) : α → Option β :=
  fun x => if x = k then some v else f x

end Ontography
