import Lean
import Ontography.Theorems
import Ontography.SystemTheorems

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
