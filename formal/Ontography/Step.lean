import Ontography.State

/-!
# The law: activation, transfer, and explicit retirement

MATHEMATICAL_DEFINITION §3–§4 under a fixed definition. Each rule is a
function returning the successor state when every premise holds and `none`
otherwise. Which premise fails is not part of the law, so rejections carry no
reason.

The rules are parameterized by the validators `accepts` and the payload
commitment `H`. Nothing is assumed about either, so every theorem holds for
all validators and all commitment functions.

The model takes the fresh activation identity as an input, as the kernel's
evaluators do; the kernel draws it at random. Output `i` of activation `a` is
package `(a, i)`, which is how live evaluation allocates them. Revisions are
unbounded naturals, so the kernel's `u64` headroom check has no counterpart.
-/

namespace Ontography

inductive Destination where
  | delivered (edge : EdgeId)
  | outbound (objectType : ObjectType)
  deriving DecidableEq, Repr

inductive OutputAuthority where
  | carry
  | transition (target : Authority)
  deriving DecidableEq, Repr

/-- One requested output: `(e, β, bytes)` or `(o, β, bytes)`. -/
structure Emission where
  destination : Destination
  authority : OutputAuthority
  payload : Bytes
  deriving DecidableEq, Repr

structure Proposal where
  trigger : Trigger
  result : Bytes
  emissions : List Emission
  deriving DecidableEq, Repr

/-- The transitions of a fixed definition. -/
inductive Op where
  | activate (id : ActivationId) (proposal : Proposal)
  | transfer (package : PackageId) (edge : EdgeId) (payload : Bytes)
  | retire (package : PackageId) (evidence : Option ActivationId)
  deriving DecidableEq, Repr

/-- Accept activation `a`: record it, consume its inputs, and insert its outputs live. -/
def State.accept (S : State) (a : ActivationId) (act : Activation)
    (records : List PackageRecord) : State :=
  { S with
    activations := update S.activations a act
    packages := fun q =>
      if q.producer = a then records[q.output]?
      else if q ∈ act.trigger.inputs then
        (S.packages q).map fun r => { r with status := .consumed a }
      else S.packages q
    activationIds := S.activationIds ++ [a]
    packageIds := S.packageIds ++ (List.range records.length).map (PackageId.mk a)
    revision := S.revision + 1 }

section Rules

variable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest) (Δ : Definition)

/-- `Orig(v, α)`: `v ∈ dom(ρ)` and `α ⊆ ρ(v)`, with `α` in the schema. -/
def rootTrigger? (v : NodeId) (α : Authority) : Option (NodeId × Authority) := do
  guard (v ∈ Δ.nodes)
  guard (α ⊆ Δ.schema.tags)
  let c ← Δ.ceiling? v
  guard (α ⊆ c)
  pure (v, α)

/-- One input of `Pkgs(I)`: live, delivered to `v`, carrying `α`. Returns its delivery edge. -/
def inputEdge? (S : State) (v : NodeId) (α : Authority) (p : PackageId) : Option EdgeId := do
  let r ← S.packages p
  guard (r.status = .live)
  let d ← r.delivery
  guard (d.receiver = v)
  guard (SetEq r.authority α)
  pure d.edge

/-- `Pkgs(I)`: nonempty, live, delivered inputs with one receiver `v` and one authority `α`,
over distinct edges, in the shape `ingress_v` requires. Returns `(v, α)`. -/
def packageTrigger? (S : State) (I : List PackageId) : Option (NodeId × Authority) := do
  let p₀ ← I.head?
  let r₀ ← S.packages p₀
  let d₀ ← r₀.delivery
  let v := d₀.receiver
  let α := r₀.authority
  guard I.Nodup
  let edges ← I.mapM (inputEdge? S v α)
  guard edges.Nodup
  let nd ← Δ.nodeDef? v
  match nd.ingress with
  | .any => guard (I.length = 1)
  | .all => guard (SetEq edges (Δ.incoming v))
  pure (v, α)

/-- The executing node and governing authority of an admissible trigger. -/
def trigger? (S : State) : Trigger → Option (NodeId × Authority)
  | .orig v α => rootTrigger? Δ v α
  | .pkgs I => packageTrigger? Δ S I

/-- One output of an activation at `v` governed by `α`: its authority obeys `Carry` or an
exact transition rule, and a delivered output also needs an edge from `v` whose authority
condition and package contract accept it. -/
def emission? (v : NodeId) (α : Authority) (em : Emission) :
    Option (Output × PackageRecord) := do
  let (β, explicit) : Authority × Bool :=
    match em.authority with
    | .carry => (α, false)
    | .transition β => (β, true)
  guard (β ⊆ Δ.schema.tags)
  guard ((explicit = true ∨ ¬ SetEq β α) → Δ.AllowsTransition v α β)
  let digest := H em.payload
  match em.destination with
  | .delivered e => do
    let edge ← Δ.edge? e
    guard (edge.source = v)
    let ed ← Δ.edgeDef? e
    guard (ed.Allows β)
    let c ← Δ.contract? ed.packageContract
    guard (accepts ed.packageContract em.payload = true)
    pure (⟨some e, c.objectType, β, digest⟩,
      ⟨c.objectType, β, digest, v, some ⟨e, edge.target⟩, .live⟩)
  | .outbound o => do
    guard (o ∈ Δ.schema.objectTypes)
    pure (⟨none, o, β, digest⟩, ⟨o, β, digest, v, none, .live⟩)

/-- Activation admission (§3): a fresh identity, an admissible trigger, an accepted result,
and admissible outputs. -/
def activate (S : State) (a : ActivationId) (prop : Proposal) : Option State := do
  guard (S.activations a = none)
  let (v, α) ← trigger? Δ S prop.trigger
  let nd ← Δ.nodeDef? v
  guard (accepts nd.resultContract prop.result = true)
  let outs ← prop.emissions.mapM (emission? accepts H Δ v α)
  pure (S.accept a ⟨v, prop.trigger, prop.result, outs.map Prod.fst⟩ (outs.map Prod.snd))

/-- Transfer (§4): a live outbound package crosses an edge leaving its producer whose type,
authority condition, and contract accept it, with bytes matching its commitment. -/
def transfer (S : State) (p : PackageId) (e : EdgeId) (payload : Bytes) : Option State := do
  let r ← S.packages p
  guard (r.status = .live)
  guard (r.delivery = none)
  let edge ← Δ.edge? e
  guard (edge.source = r.producerNode)
  let ed ← Δ.edgeDef? e
  let c ← Δ.contract? ed.packageContract
  guard (r.objectType = c.objectType)
  guard (ed.Allows r.authority)
  guard (H payload = r.digest)
  guard (accepts ed.packageContract payload = true)
  pure { S with
    packages := update S.packages p { r with delivery := some ⟨e, edge.target⟩ }
    revision := S.revision + 1 }

/-- Explicit retirement (§4): a live package retires, citing an accepted activation if any. -/
def retire (S : State) (p : PackageId) (evidence : Option ActivationId) : Option State := do
  let r ← S.packages p
  guard (r.status = .live)
  guard (evidence.all fun a => (S.activations a).isSome)
  pure { S with
    packages := update S.packages p
      { r with status := .retired ⟨.explicit, S.revision + 1, evidence⟩ }
    revision := S.revision + 1 }

/-- One transition of a fixed definition. -/
def step (S : State) : Op → Option State
  | .activate a prop => activate accepts H Δ S a prop
  | .transfer p e payload => transfer accepts H Δ S p e payload
  | .retire p evidence => retire S p evidence

end Rules

end Ontography
