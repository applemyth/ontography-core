import Ontography.Checkpoint
import Ontography.Proofs.Basic

/-!
# Checkpoint restoration

`CheckpointValid` reads a state only through its checkpoint. Besides the recorded components,
it reads the birth metadata `output?`, the revision-accounting counts, and the causal history,
and these are functions of the activation map, the package map, and the package list. Two
states that record the same checkpoint therefore pass or fail together.

Every well-formed state passes. Most checks are fields of `WF`, acyclicity is
`causal_acyclic`, and the rest follow from the logs `WF` keeps. A delivery's edge is logged,
so its identity is used. A current edge is logged too, and logged identities are unique, so a
delivery on a current edge agrees with its incidence. The change log is a duplicate-free list
of `definitionChanges` stamps that holds every structural stamp and no explicit one.

The converse fails. Two root packages crossed one edge identity `e`, from `A` to `B` and from
`C` to `D`, and `e` is no longer in the definition. The checkpoint records only that `e` was
used, so it passes every check, but a well-formed state would log both incidences under `e`.
-/

namespace Ontography.Proofs

namespace Ckpt

/-- `f` is injective on a list whose image under `f` has no duplicates. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (hxy ▸ List.mem_map_of_mem hy') h.1
    · exact absurd (hxy.symm ▸ List.mem_map_of_mem hx') h.1
    · exact ih h.2 hx' hy'

end Ckpt

variable {Δ : Definition} {S : State}

/-- The checks read only the checkpoint. -/
theorem checkpointValid_congr {S' : State} (hsame : SameCheckpoint S S')
    (h : CheckpointValid Δ S) : CheckpointValid Δ S' := by
  obtain ⟨activations, packages, activationIds, packageIds, usedNodes, edgeLog, changeLog,
    revision⟩ := S
  obtain ⟨activations', packages', activationIds', packageIds', usedNodes', edgeLog',
    changeLog', revision'⟩ := S'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hedges, hchanges, rfl⟩ := hsame
  -- The states now differ only in their logs. `output?`, the revision-accounting counts, and
  -- `DependsOn` read neither, so only the checks that read the used edge identities or the
  -- definition-change count need rewriting.
  exact { h with
    used_nonempty := hedges ▸ h.used_nonempty
    current_used := hedges ▸ h.current_used
    delivery_used := hedges ▸ h.delivery_used
    structural_stamps := hchanges ▸ h.structural_stamps
    revision := hchanges ▸ h.revision }

-- Restoration needs nothing of `Δ` beyond `WF`: `hΔ` is unused, and kept so that the
-- statement is exactly `Ontography.checkpoint_of_wf`.
set_option linter.unusedVariables false in
/-- Restoration accepts every well-formed state, so it never rejects a reachable one. -/
theorem checkpoint_of_wf (hΔ : Δ.Admitted) (hS : WF Δ S) : CheckpointValid Δ S where
  activationIds_nodup := hS.activationIds_nodup
  activations_dom := hS.activations_dom
  packageIds_nodup := hS.packageIds_nodup
  packages_dom := hS.packages_dom
  used_nonempty := ⟨hS.used_nonempty.1, fun e he => by
    obtain ⟨edge, hedge, rfl⟩ := List.mem_map.1 he
    exact hS.used_nonempty.2 edge hedge⟩
  current_used := ⟨hS.used_nodes, List.map_subset _ hS.edge_log⟩
  activation_nodes_used := hS.activation_nodes_used
  ownership := hS.ownership
  outputs_recorded := hS.outputs_recorded
  schema_closure := hS.schema_closure
  acyclic := Ontography.causal_acyclic hS
  triggers := hS.triggers
  consumed := hS.consumed
  inputs := hS.inputs
  join_authority := hS.join_authority
  delivery_used p r d hr hd :=
    have hlog := hS.delivery p r d hr hd
    ⟨List.mem_map_of_mem hlog, (hS.edge_log_nodes _ hlog).2⟩
  delivery_current p r d e hr hd he := by
    -- The current edge and the delivery's incidence are both logged under the identity `d.edge`.
    obtain ⟨hmem, hid⟩ := Common.edge?_mem he
    obtain rfl := Ckpt.eq_of_nodup_map hS.edge_log_ids (hS.edge_log hmem)
      (hS.delivery p r d hr hd) hid
    exact ⟨rfl, rfl⟩
  birth_edge := hS.birth_edge
  custody := hS.custody
  all_routes := hS.all_routes
  retirement p r ret hr hs :=
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, _⟩ := hS.retirement p r ret hr hs
    ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  explicit_stamps p q r s ρ σ hr hs hρ hσ he hrev := by
    -- An explicit stamp is no definition change, so a retirement sharing it is explicit too.
    obtain ⟨-, -, -, -, -, -, -, hρs⟩ := hS.retirement p r ρ hr hρ
    obtain ⟨-, -, -, -, -, -, -, hσs⟩ := hS.retirement q s σ hs hσ
    have hσe : σ.reason = .explicit := hσs.2 (hrev ▸ hρs.1 he)
    exact ⟨hσe, hS.explicit_stamps p q r s ρ σ hr hs hρ hσ he hσe hrev⟩
  structural_stamps := ⟨S.changeLog, hS.changeLog_nodup, Nat.le_refl _,
    fun p r ret hr hs hne => by
      -- A stamp outside the change log would make the retirement explicit.
      obtain ⟨-, -, -, -, -, -, -, hstamp⟩ := hS.retirement p r ret hr hs
      exact Decidable.byContradiction fun hmem => hne (hstamp.2 hmem)⟩
  revision := hS.revision

namespace Ckpt

/-! ## A checkpoint that no well-formed state records -/

/-- Four nodes of type `n` and no edges; `A` and `C` are roots with ceiling `{run}`. -/
def gapDef : Definition where
  schema := ⟨["n"], ["t"], ["run"]⟩
  contracts := [⟨"result", "t"⟩]
  nodes := ["A", "B", "C", "D"]
  edges := []
  nodeDefs := ["A", "B", "C", "D"].map fun v => ⟨v, ["n"], "result", .any⟩
  edgeDefs := []
  transitions := []
  roots := [⟨"A", ["run"]⟩, ⟨"C", ["run"]⟩]

/-- A root activation at `v` whose one output was born on the edge `e`. -/
def gapActivation (v : NodeId) : Activation :=
  ⟨v, .orig v ["run"], [], [⟨some "e", "t", ["run"], "d"⟩]⟩

/-- That output, live, having crossed `e` from `v` to `w`. -/
def gapRecord (v w : NodeId) : PackageRecord :=
  ⟨"t", ["run"], "d", v, some ⟨"e", w⟩, .live⟩

/-- Root activations at `A` and `C`, whose packages crossed the one edge identity `e` to `B`
and to `D`, followed by a definition change at revision 3. The incidence log records only the
first crossing. -/
def gapState : State where
  activations a :=
    if a = 1 then some (gapActivation "A") else if a = 2 then some (gapActivation "C") else none
  packages p :=
    if p = ⟨1, 0⟩ then some (gapRecord "A" "B")
    else if p = ⟨2, 0⟩ then some (gapRecord "C" "D") else none
  activationIds := [1, 2]
  packageIds := [⟨1, 0⟩, ⟨2, 0⟩]
  usedNodes := ["A", "B", "C", "D"]
  edgeLog := [⟨"e", "A", "B"⟩]
  changeLog := [3]
  revision := 3

/-- The accepted activations are `1` at `A` and `2` at `C`. -/
theorem gapState_activations {a : ActivationId} {act : Activation}
    (h : gapState.activations a = some act) :
    a = 1 ∧ act = gapActivation "A" ∨ a = 2 ∧ act = gapActivation "C" := by
  simp only [gapState] at h
  split at h
  · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
  · split at h
    · exact .inr ⟨‹_›, (Option.some.inj h).symm⟩
    · cases h

/-- The packages are `⟨1, 0⟩`, held by `B`, and `⟨2, 0⟩`, held by `D`. -/
theorem gapState_packages {p : PackageId} {r : PackageRecord}
    (h : gapState.packages p = some r) :
    p = ⟨1, 0⟩ ∧ r = gapRecord "A" "B" ∨ p = ⟨2, 0⟩ ∧ r = gapRecord "C" "D" := by
  simp only [gapState] at h
  split at h
  · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
  · split at h
    · exact .inr ⟨‹_›, (Option.some.inj h).symm⟩
    · cases h

/-- Every node has `Any` ingress. -/
theorem gapDef_ingress : ∀ nd ∈ gapDef.nodeDefs, nd.ingress = .any := by decide

/-- The definition is admitted. -/
theorem gapDef_admitted : gapDef.Admitted where
  nodes_nonempty := by decide
  nodes_nodup := by decide
  edges_nonempty := by decide
  edges_nodup := by decide
  endpoints := by decide
  vocabulary_nonempty := by decide
  contracts_nodup := by decide
  contracts_wf := by decide
  nodeDefs_nodup := by decide
  nodeDefs_nodes := by decide
  nodes_defined := by decide
  nodeDefs_wf := by decide
  edgeDefs_nodup := by decide
  edgeDefs_edges := by decide
  edges_defined := by decide
  edgeDefs_wf := by decide
  requirements := by decide
  transitions_wf := by decide
  roots_nodup := by decide
  roots_wf := by decide

/-- The checkpoint passes every check: `e` is a used identity, and no current edge constrains
either delivery. -/
theorem gapState_valid : CheckpointValid gapDef gapState where
  activationIds_nodup := by decide
  activations_dom a := by
    by_cases h₁ : a = 1
    · subst h₁; decide
    by_cases h₂ : a = 2
    · subst h₂; decide
    simp [gapState, h₁, h₂]
  packageIds_nodup := by decide
  packages_dom p := by
    by_cases h₁ : p = ⟨1, 0⟩
    · subst h₁; decide
    by_cases h₂ : p = ⟨2, 0⟩
    · subst h₂; decide
    simp [gapState, h₁, h₂]
  used_nonempty := by decide
  current_used := by decide
  activation_nodes_used a act h := by
    rcases gapState_activations h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  ownership p r h := by
    rcases gapState_packages h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  outputs_recorded a act h i hi := by
    rcases gapState_activations h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      obtain rfl := Nat.lt_one_iff.1 hi <;> rfl
  schema_closure p r h := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  acyclic b h := by
    -- Nothing is consumed, so nothing depends on anything.
    have hnone : ∀ x y, ¬ DependsOn gapState x y := by
      rintro x y ⟨p, r, -, hp, hs⟩
      rcases gapState_packages hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
    cases h with
    | single hd => exact hnone _ _ hd
    | tail _ hd => exact hnone _ _ hd
  triggers b act h := by
    rcases gapState_activations h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact ⟨fun I hI => (by cases hI), fun v α hv => (by cases hv; decide)⟩
  consumed p r b h hs := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  inputs b act h p hp := by
    rcases gapState_activations h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hp
  join_authority b act h p hp := by
    rcases gapState_activations h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hp
  delivery_used p r d h hd := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hd <;> decide
  delivery_current _ _ _ _ _ _ he := by cases he
  birth_edge p r o e h ho he := by
    rcases gapState_packages h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases ho <;> cases he <;>
      exact ⟨_, rfl⟩
  custody p r h _ := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  all_routes _ _ _ nd _ _ _ hnd hall := by
    rw [gapDef_ingress nd (Common.nodeDef?_mem hnd).1] at hall
    cases hall
  retirement p r ret h hs := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs
  explicit_stamps p q r s ρ σ h _ hρ := by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hρ
  structural_stamps := ⟨[], List.nodup_nil, Nat.zero_le _, fun p r ret h hs => by
    rcases gapState_packages h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases hs⟩
  revision := by decide

end Ckpt

open Ckpt in
/-- The checks are strictly weaker than well-formedness: some admitted definition has a
checkpoint that passes every check yet belongs to no well-formed state, because two receipts
on a removed edge disagree about its endpoints. -/
theorem checkpoint_gap : ∃ (Δ : Definition) (S : State), Δ.Admitted ∧ CheckpointValid Δ S ∧
    ∀ S', SameCheckpoint S S' → ¬ WF Δ S' := by
  refine ⟨gapDef, gapState, gapDef_admitted, gapState_valid, fun S' hsame hS' => ?_⟩
  -- A well-formed state with these packages logs both incidences under the identity `e`.
  obtain ⟨-, hpackages, -⟩ := hsame
  have hAB := hS'.delivery ⟨1, 0⟩ (gapRecord "A" "B") ⟨"e", "B"⟩ (hpackages ▸ rfl) rfl
  have hCD := hS'.delivery ⟨2, 0⟩ (gapRecord "C" "D") ⟨"e", "D"⟩ (hpackages ▸ rfl) rfl
  have := eq_of_nodup_map hS'.edge_log_ids hAB hCD rfl
  exact absurd (Edge.mk.inj this).2.1 (by decide)

end Ontography.Proofs
