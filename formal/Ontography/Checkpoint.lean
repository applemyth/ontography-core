import Ontography.Theorems

/-!
# Checkpoint restoration

The kernel restores a trusted store's checkpoint by checking the invariants a state records
(TRANSITIONS §4, `Kernel::restore_checkpoint`). `CheckpointValid` states those checks. It
reads only what a checkpoint holds: the activation and package maps, the lifetime identities,
the definition-change count, and the revision. The model's incidence log and change log are
invisible to it.

The checks are exactly the invariants. Every well-formed state passes them, and every
checkpoint that passes is recorded by some well-formed state, one that may differ in its
acceptance order and ghost logs. A checkpoint cannot record the incidence of an edge that
every receipt names consistently, but every such incidence is consistent with some
well-formed history, so restoration establishes the integrity of a trusted store, not its
reachability.
-/

namespace Ontography

/-- Two states record the same checkpoint: they differ at most in the incidence and change
logs, beyond the identities and counts those logs determine. -/
def SameCheckpoint (S S' : State) : Prop :=
  S.activations = S'.activations ∧ S.packages = S'.packages ∧
    S.activationIds = S'.activationIds ∧ S.packageIds = S'.packageIds ∧
    S.usedNodes = S'.usedNodes ∧ S.usedEdges = S'.usedEdges ∧
    S.definitionChanges = S'.definitionChanges ∧ S.revision = S'.revision

/-- The checks of checkpoint restoration, grouped by the kernel's error families. -/
structure CheckpointValid (Δ : Definition) (S : State) : Prop where
  /-- The activation and package maps have the listed domains. -/
  activationIds_nodup : S.activationIds.Nodup
  activations_dom : ∀ a, (S.activations a).isSome ↔ a ∈ S.activationIds
  packageIds_nodup : S.packageIds.Nodup
  packages_dom : ∀ p, (S.packages p).isSome ↔ p ∈ S.packageIds
  /-- Identity: lifetime identities are nonempty and include the current graph's; edge
  identities are distinct, and some node identity exists for their endpoints. -/
  used_nonempty : (∀ v ∈ S.usedNodes, v ≠ "") ∧ ∀ e ∈ S.usedEdges, e ≠ ""
  current_used : Δ.nodes ⊆ S.usedNodes ∧ Δ.edges.map (·.id) ⊆ S.usedEdges
  used_edges : S.usedEdges.Nodup ∧ (S.usedEdges ≠ [] → S.usedNodes ≠ [])
  activation_nodes_used : ∀ a act, S.activations a = some act → act.node ∈ S.usedNodes
  /-- Ownership: packages are exactly the outputs, agree with their birth metadata, and lie in
  the schema. -/
  ownership : ∀ p r, S.packages p = some r →
    ∃ act o, S.activations p.producer = some act ∧ act.outputs[p.output]? = some o ∧
      r.objectType = o.objectType ∧ r.authority = o.authority ∧ r.digest = o.digest ∧
      r.producerNode = act.node
  outputs_recorded : ∀ a act, S.activations a = some act →
    ∀ i < act.outputs.length, (S.packages ⟨a, i⟩).isSome
  schema_closure : ∀ p r, S.packages p = some r →
    r.objectType ∈ Δ.schema.objectTypes ∧ r.authority ⊆ Δ.schema.tags
  /-- Cycle: the causal history is acyclic. -/
  acyclic : ∀ b, ¬ Relation.TransGen (DependsOn S) b b
  /-- Activation and Consumption: triggers, their inputs, and their consumers agree. -/
  triggers : ∀ b act, S.activations b = some act →
    (∀ I, act.trigger = .pkgs I → I ≠ [] ∧ I.Nodup) ∧
      ∀ v α, act.trigger = .orig v α → act.node = v ∧ α ⊆ Δ.schema.tags
  consumed : ∀ p r b, S.packages p = some r → r.status = .consumed b →
    ∃ act, S.activations b = some act ∧ p ∈ act.trigger.inputs
  inputs : ∀ b act, S.activations b = some act → ∀ p ∈ act.trigger.inputs,
    ∃ r d, S.packages p = some r ∧ r.status = .consumed b ∧ r.delivery = some d ∧
      d.receiver = act.node
  join_authority : ∀ b act, S.activations b = some act →
    ∀ p ∈ act.trigger.inputs, ∀ q ∈ act.trigger.inputs, ∀ r s,
      S.packages p = some r → S.packages q = some s → SetEq r.authority s.authority
  /-- Delivery: a delivery names lifetime identities, matches its edge's incidence while that
  edge is current, agrees with every other delivery over that edge, and is the birth edge
  when one was named. -/
  delivery_used : ∀ p r d, S.packages p = some r → r.delivery = some d →
    d.edge ∈ S.usedEdges ∧ d.receiver ∈ S.usedNodes
  delivery_current : ∀ p r d e, S.packages p = some r → r.delivery = some d →
    Δ.edge? d.edge = some e → e.source = r.producerNode ∧ e.target = d.receiver
  delivery_consistent : ∀ p q r s d d', S.packages p = some r → S.packages q = some s →
    r.delivery = some d → s.delivery = some d' → d.edge = d'.edge →
      r.producerNode = s.producerNode ∧ d.receiver = d'.receiver
  birth_edge : ∀ p r o e, S.packages p = some r → S.output? p = some o → o.edge = some e →
    ∃ v, r.delivery = some ⟨e, v⟩
  /-- Custody: live holders are nodes, and a live `All` receipt keeps a current route. -/
  custody : ∀ p r, S.packages p = some r → r.status = .live → r.holder ∈ Δ.nodes
  all_routes : ∀ p r d nd, S.packages p = some r → r.status = .live → r.delivery = some d →
    Δ.nodeDef? d.receiver = some nd → nd.ingress = .all → d.edge ∈ Δ.incoming d.receiver
  /-- Retirement: reasons admit phases, evidence is explicit and accepted, stamps are past
  revisions, and a removed holder is not a current node. -/
  retirement : ∀ p r ret, S.packages p = some r → r.status = .retired ret →
    (ret.reason = .noAcceptingEdge → r.delivery = none) ∧
    (ret.reason = .routeRemoved → r.delivery ≠ none) ∧
    (ret.evidence ≠ none → ret.reason = .explicit) ∧
    (∀ a, ret.evidence = some a → (S.activations a).isSome) ∧
    1 ≤ ret.revision ∧ ret.revision ≤ S.revision ∧
    (ret.reason = .holderRemoved → r.holder ∉ Δ.nodes)
  /-- Retirement: explicit stamps are distinct and never a structural stamp. -/
  explicit_stamps : ∀ p q r s ρ σ, S.packages p = some r → S.packages q = some s →
    r.status = .retired ρ → s.status = .retired σ → ρ.reason = .explicit →
      ρ.revision = σ.revision → σ.reason = .explicit ∧ p = q
  /-- Revision: the distinct structural stamps are at most the definition changes, and the
  revision accounts for every transition. -/
  structural_stamps : ∃ stamps : List Nat, stamps.Nodup ∧
    stamps.length ≤ S.definitionChanges ∧ ∀ p r ret, S.packages p = some r →
      r.status = .retired ret → ret.reason ≠ .explicit → ret.revision ∈ stamps
  revision : S.revision =
    S.activationIds.length + S.explicitTransfers + S.explicitRetirements + S.definitionChanges

end Ontography
