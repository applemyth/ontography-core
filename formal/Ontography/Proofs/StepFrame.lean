import Ontography.Proofs.ActivationLemmas
import Ontography.Proofs.Revision

/-!
# What a transition keeps

No transition of a fixed definition changes an accepted activation, a package's immutable
facts, a delivery once made, or a status once no longer live, and none touches the lifetime
records.

Activation accepts a fresh identity `a`. The update at `a` keeps every accepted activation, and
by ownership no recorded package has producer `a`, so each recorded package keeps its record
or, as a live input, changes only its status to `consumed a`. Transfer and explicit retirement
replace the record of one live package through `Common.setRecord`: transfer gives a delivery
to a package with none, and retirement changes the status of a live package.
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest} {Δ : Definition}
  {S S' : State}

namespace Common

/-- Replacing the record `r` of `p` by `r'` frames the state when `r'` keeps the immutable
facts of `r`, its delivery once made, and its status once no longer live. -/
theorem setRecord_frame {p : PackageId} {r r' : PackageRecord} (hr : S.packages p = some r)
    (hr' : r'.objectType = r.objectType ∧ r'.authority = r.authority ∧ r'.digest = r.digest ∧
      r'.producerNode = r.producerNode ∧ (r.delivery ≠ none → r'.delivery = r.delivery) ∧
      (r.status ≠ .live → r'.status = r.status)) :
    Frame S (setRecord S p r') where
  activations _ _ h := h
  packages q x hx := by
    by_cases hq : q = p
    · subst hq
      rw [hr, Option.some.injEq] at hx
      subst hx
      exact ⟨r', update_self, hr'⟩
    · exact ⟨x, by rw [setRecord_packages, update_of_ne hq, hx], rfl, rfl, rfl, rfl,
        fun _ => rfl, fun _ => rfl⟩
  usedNodes := List.Subset.refl _
  edgeLog := List.Subset.refl _
  changeLog := List.Subset.refl _

end Common

/-- Activation keeps every accepted activation and changes a recorded package only by
consuming it, when it is a live input; the lifetime records stay. -/
theorem activate_frame (hS : WF Δ S) {a : ActivationId} {prop : Proposal}
    (h : activate accepts H Δ S a prop = some S') :
    Frame S S' ∧ S'.usedNodes = S.usedNodes ∧ S'.edgeLog = S.edgeLog ∧
      S'.changeLog = S.changeLog := by
  obtain ⟨act, α, records, hfresh, htrig, rfl⟩ := Common.activate_eq_some h
  refine ⟨⟨fun b act' hb => ?_, fun p r hr => ?_, List.Subset.refl _, List.Subset.refl _,
    List.Subset.refl _⟩, rfl, rfl, rfl⟩
  · -- `b` is accepted, so it is not the fresh `a`.
    have hba : b ≠ a := by
      rintro rfl
      rw [hfresh] at hb
      cases hb
    rw [Activation.accept_activations, ite_eq_right hba, hb]
  · -- `p` is recorded, so by ownership its producer is not the fresh `a`.
    rw [Activation.accept_packages, ite_eq_right (Activation.producer_ne hS hfresh hr)]
    by_cases hin : p ∈ act.trigger.inputs
    · -- An input is live, and only its status changes.
      obtain ⟨r₀, _, h0, hlive, _⟩ := (Activation.trigger_spec htrig).inputs p hin
      rw [hr, Option.some.injEq] at h0
      subst h0
      rw [ite_eq_left hin, hr, Option.map_some]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun hs => absurd hlive hs⟩
    · rw [ite_eq_right hin, hr]
      exact ⟨r, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- Transfer changes only the delivery of a package that had none; the lifetime records stay. -/
theorem transfer_frame {p : PackageId} {e : EdgeId} {payload : Bytes}
    (h : transfer accepts H Δ S p e payload = some S') :
    Frame S S' ∧ S'.usedNodes = S.usedNodes ∧ S'.edgeLog = S.edgeLog ∧
      S'.changeLog = S.changeLog := by
  obtain ⟨r, _, hr, -, hnone, -, -, rfl⟩ := Common.transfer_eq_some h
  exact ⟨Common.setRecord_frame hr
    ⟨rfl, rfl, rfl, rfl, fun hd => absurd hnone hd, fun _ => rfl⟩, rfl, rfl, rfl⟩

/-- Explicit retirement changes only the status of a live package; the lifetime records
stay. -/
theorem retire_frame {p : PackageId} {evidence : Option ActivationId}
    (h : retire S p evidence = some S') :
    Frame S S' ∧ S'.usedNodes = S.usedNodes ∧ S'.edgeLog = S.edgeLog ∧
      S'.changeLog = S.changeLog := by
  obtain ⟨r, hr, hlive, -, rfl⟩ := Common.retire_eq_some h
  exact ⟨Common.setRecord_frame hr
    ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun hs => absurd hlive hs⟩, rfl, rfl, rfl⟩

/-- A transition changes no accepted activation, no package's immutable facts, no delivery
once made, and no status once no longer live; a fixed-definition transition keeps the
lifetime records. -/
theorem step_frame (hS : WF Δ S) {op : Op} (h : step accepts H Δ S op = some S') :
    Frame S S' ∧ S'.usedNodes = S.usedNodes ∧ S'.edgeLog = S.edgeLog ∧
      S'.changeLog = S.changeLog := by
  cases op with
  | activate a prop => exact activate_frame hS h
  | transfer p e payload => exact transfer_frame h
  | retire p evidence => exact retire_frame h

end Ontography.Proofs
