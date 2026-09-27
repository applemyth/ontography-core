import Ontography.Step

/-!
# Well-formed states

`WF Δ S` collects the invariants I1–I7 of TRANSITIONS §1, causal acyclicity,
and the admission consequences checkpoint restoration also checks, as
properties of one state bound to `Δ`. The fields are grouped by invariant.
-/

namespace Ontography

/-- The invariants of every reachable state. -/
structure WF (Δ : Definition) (S : State) : Prop where
  /-- `activationIds` and `packageIds` list `dom(A)` and `dom(P)` without repetition. -/
  activationIds_nodup : S.activationIds.Nodup
  activations_dom : ∀ a, (S.activations a).isSome ↔ a ∈ S.activationIds
  packageIds_nodup : S.packageIds.Nodup
  packages_dom : ∀ p, (S.packages p).isSome ↔ p ∈ S.packageIds
  /-- I1 Ownership: every package is an output of its producer, and its immutable facts are
  the output's birth metadata and the producer's node. -/
  ownership : ∀ p r, S.packages p = some r →
    ∃ act o, S.activations p.producer = some act ∧ act.outputs[p.output]? = some o ∧
      r.objectType = o.objectType ∧ r.authority = o.authority ∧ r.digest = o.digest ∧
      r.producerNode = act.node
  /-- Every output of an accepted activation is a recorded package. -/
  outputs_recorded : ∀ a act, S.activations a = some act →
    ∀ i < act.outputs.length, (S.packages ⟨a, i⟩).isSome
  /-- I2 Consumption: a consumed package is an input of its accepted consumer. -/
  consumed : ∀ p r b, S.packages p = some r → r.status = .consumed b →
    ∃ act, S.activations b = some act ∧ p ∈ act.trigger.inputs
  /-- I2: every input of an activation was delivered to its node and is consumed by it. -/
  inputs : ∀ b act, S.activations b = some act → ∀ p ∈ act.trigger.inputs,
    ∃ r d, S.packages p = some r ∧ r.status = .consumed b ∧ r.delivery = some d ∧
      d.receiver = act.node
  /-- I2: the inputs of an activation carry one authority. -/
  join_authority : ∀ b act, S.activations b = some act →
    ∀ p ∈ act.trigger.inputs, ∀ q ∈ act.trigger.inputs, ∀ r s,
      S.packages p = some r → S.packages q = some s → SetEq r.authority s.authority
  /-- I2: a package trigger is nonempty, and a root's recorded node is its trigger node. -/
  triggers : ∀ b act, S.activations b = some act →
    (∀ I, act.trigger = .pkgs I → I ≠ []) ∧ ∀ v α, act.trigger = .orig v α → act.node = v
  /-- I3 Delivery: a delivery names an edge admitted from the producer's node to the
  receiver, and a birth edge is the package's delivery edge. -/
  delivery : ∀ p r d, S.packages p = some r → r.delivery = some d →
    (⟨d.edge, r.producerNode, d.receiver⟩ : Edge) ∈ S.edgeLog
  birth_edge : ∀ p r o e, S.packages p = some r → S.output? p = some o → o.edge = some e →
    ∃ v, r.delivery = some ⟨e, v⟩
  /-- I4 Retirement: reasons admit the phase, evidence is explicit and accepted, and stamps
  are past revisions — definition changes for structural reasons, and never one for an
  explicit retirement. A removed holder is absent from the graph. -/
  retirement : ∀ p r ret, S.packages p = some r → r.status = .retired ret →
    (ret.reason = .noAcceptingEdge → r.delivery = none) ∧
    (ret.reason = .routeRemoved → r.delivery ≠ none) ∧
    (ret.evidence ≠ none → ret.reason = .explicit) ∧
    (∀ a, ret.evidence = some a → (S.activations a).isSome) ∧
    1 ≤ ret.revision ∧ ret.revision ≤ S.revision ∧
    (ret.reason = .holderRemoved → r.holder ∉ Δ.nodes) ∧
    (ret.reason = .explicit ↔ ret.revision ∉ S.changeLog)
  /-- I4: explicit retirements have distinct stamps. -/
  explicit_stamps : ∀ p q r s ρ σ, S.packages p = some r → S.packages q = some s →
    r.status = .retired ρ → s.status = .retired σ → ρ.reason = .explicit →
      σ.reason = .explicit → ρ.revision = σ.revision → p = q
  /-- I5 Custody: every live holder is a node, and a live receipt at an `All` node names a
  current incoming edge. -/
  custody : ∀ p r, S.packages p = some r → r.status = .live → r.holder ∈ Δ.nodes
  all_routes : ∀ p r d nd, S.packages p = some r → r.status = .live → r.delivery = some d →
    Δ.nodeDef? d.receiver = some nd → nd.ingress = .all → d.edge ∈ Δ.incoming d.receiver
  /-- I6 Revision: each transition accounts for exactly one term. -/
  revision : S.revision =
    S.activationIds.length + S.explicitTransfers + S.explicitRetirements + S.definitionChanges
  /-- I6: definition changes happened at distinct past revisions. -/
  changeLog_nodup : S.changeLog.Nodup
  changeLog_le : ∀ n ∈ S.changeLog, 1 ≤ n ∧ n ≤ S.revision
  /-- I7 Identity: current identities are lifetime identities, admitted once. -/
  used_nodes : Δ.nodes ⊆ S.usedNodes
  edge_log : Δ.edges ⊆ S.edgeLog
  edge_log_ids : (S.edgeLog.map (·.id)).Nodup
  /-- I7: every node an activation or a logged edge names is a lifetime identity, so a fresh
  identity can never alias one. -/
  activation_nodes_used : ∀ a act, S.activations a = some act → act.node ∈ S.usedNodes
  edge_log_nodes : ∀ e ∈ S.edgeLog, e.source ∈ S.usedNodes ∧ e.target ∈ S.usedNodes
  /-- Causal acyclicity: every input was produced by an earlier activation. -/
  causal_order : ∀ p r b, S.packages p = some r → r.status = .consumed b →
    S.activationIds.idxOf p.producer < S.activationIds.idxOf b
  /-- Schema closure: object types and carried authority are in the schema. -/
  schema_closure : ∀ p r, S.packages p = some r →
    r.objectType ∈ Δ.schema.objectTypes ∧ r.authority ⊆ Δ.schema.tags

/-- `b` consumed an output of `a`: the arcs `a → p → b` of the causal history `H_S`. -/
def DependsOn (S : State) (b a : ActivationId) : Prop :=
  ∃ p r, p.producer = a ∧ S.packages p = some r ∧ r.status = .consumed b

/-- States reachable from the empty state of `Δ` by transitions of `Δ`. -/
inductive Reachable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest)
    (Δ : Definition) : State → Prop
  | initial : Reachable accepts H Δ (State.initial Δ)
  | next {S S' : State} (op : Op) :
    Reachable accepts H Δ S → Ontography.step accepts H Δ S op = some S' →
      Reachable accepts H Δ S'

end Ontography
