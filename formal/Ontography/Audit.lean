import Lean
import Ontography.Theorems
import Ontography.SystemTheorems
import Ontography.Metatheory

/-!
# Axiom audit

Building this module fails unless each headline theorem depends only on Lean's standard
axioms. An unfinished proof depends on `sorryAx` and an asserted fact on its own axiom, so
neither can pass.
-/

open Lean Elab Command

/-- Fails unless the named theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. -/
elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← Lean.collectAxioms name
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := axioms.filter (!standard.contains ·)
  unless extra.isEmpty do
    throwError m!"{name} depends on non-standard axioms {extra.toList}"

#assert_standard_axioms Ontography.wf_initial
#assert_standard_axioms Ontography.wf_step
#assert_standard_axioms Ontography.wf_of_reachable
#assert_standard_axioms Ontography.step_revision
#assert_standard_axioms Ontography.step_frame
#assert_standard_axioms Ontography.causal_acyclic
#assert_standard_axioms Ontography.wf_extend
#assert_standard_axioms Ontography.extend_spec
#assert_standard_axioms Ontography.sysStep_revision
#assert_standard_axioms Ontography.sysStep_frame
#assert_standard_axioms Ontography.sysStep_fresh
#assert_standard_axioms Ontography.replay_history
#assert_standard_axioms Ontography.wf_rewrite
#assert_standard_axioms Ontography.rewrite_spec
#assert_standard_axioms Ontography.wf_sysStep
#assert_standard_axioms Ontography.wf_of_sysReachable
#assert_standard_axioms Ontography.activation_persists
#assert_standard_axioms Ontography.removed_node_never_returns
#assert_standard_axioms Ontography.removed_edge_never_returns
#assert_standard_axioms Ontography.checkpointValid_congr
#assert_standard_axioms Ontography.checkpoint_of_wf
#assert_standard_axioms Ontography.rewrite_local
#assert_standard_axioms Ontography.rewrite_commute
#assert_standard_axioms Ontography.sysSteps_frame
#assert_standard_axioms Ontography.accepted_not_reaccepted
#assert_standard_axioms Ontography.sysStep_newborn
#assert_standard_axioms Ontography.replay_sound
#assert_standard_axioms Ontography.activationRun_of_revision
#assert_standard_axioms Ontography.replay_causal
#assert_standard_axioms Ontography.checkpoint_sound
