import Ontography.Theorems

/-!
# Fixed-graph replay (T5)

`Kernel::restore_state` rebuilds a state from its activation records alone, re-proving each
activation's admission with payload evidence. The model's `replay` re-derives each recorded
activation's proposal and admits it with `activate`, in acceptance order. For a state reached
by activations alone, replaying its history with the payloads it was built from reproduces
it exactly.

The evidence hypothesis also carries the collision-freedom the kernel assumes of SHA-256:
if two payloads of the run shared a commitment, evidence could not return both.
-/

namespace Ontography

/-- The accepted activations of `S`, in acceptance order. -/
def State.history (S : State) : List (ActivationId × Activation) :=
  S.activationIds.filterMap fun a => (S.activations a).map ((a, ·))

/-- The governing authority of a recorded trigger in `S`: a root's, or its first input's. -/
def governing? (S : State) : Trigger → Option Authority
  | .orig _ α => some α
  | .pkgs I => do
    let p ← I.head?
    let r ← S.packages p
    pure r.authority

/-- The proposal a recorded activation was admitted from: each output keeps its destination
and authority, and its payload comes from the evidence for its commitment. -/
def Activation.replayProposal (act : Activation) (α : Authority)
    (evidence : Digest → Option Bytes) : Option Proposal := do
  let emissions ← act.outputs.mapM fun o => do
    let bytes ← evidence o.digest
    pure ⟨match o.edge with
        | some e => .delivered e
        | none => .outbound o.objectType,
      if o.authority = α then .carry else .transition o.authority, bytes⟩
  pure ⟨act.trigger, act.result, emissions⟩

section

variable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)

/-- Fixed-graph replay: admit the recorded activations in order, each re-derived from its
record and the payload evidence. -/
def replay (history : List (ActivationId × Activation)) (evidence : Digest → Option Bytes) :
    Option State :=
  history.foldlM (fun S entry => do
    let α ← governing? S entry.2.trigger
    let prop ← entry.2.replayProposal α evidence
    activate accepts H Δ S entry.1 prop) (State.initial Δ)

/-- States reached by activations alone, with the payloads their outputs were built from. -/
inductive ActivationRun : State → List Bytes → Prop
  | initial : ActivationRun (State.initial Δ) []
  | activate {S S' : State} {payloads : List Bytes} {a : ActivationId} {prop : Proposal} :
    ActivationRun S payloads → Ontography.activate accepts H Δ S a prop = some S' →
      ActivationRun S' (payloads ++ prop.emissions.map (·.payload))

end

end Ontography
