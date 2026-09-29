import Ontography.System
import Ontography.Proofs.Extension
import Ontography.Proofs.StepFrame
import Ontography.Proofs.Structural

/-!
# Revision, frame, and freshness of the dynamic calculus

A running workflow moves by a fixed-definition step, a rewrite, or an extension. A step keeps
the definition, so `step_revision` and `step_frame` cover it. An extension changes only the
vocabulary and the counters (`extend_spec`).

A rewrite is inverted here directly from `rewrite` and `structuralEdit?`. It keeps every
accepted activation, changes a recorded package at most by retiring it when it was live,
appends the fresh allocations to the lifetime records and the successor revision to the change
log, and advances the revision once. Its replacement definition keeps the current nodes and
edges the edit does not remove and adds the ones it allocates, which the edit must draw from
outside the lifetime identities.
-/

namespace Ontography.Proofs

variable {accepts : ContractId → Bytes → Bool} {H : Bytes → Digest}
  {permits : Policy} {Δ Δ' : Definition} {S S' : State}

namespace Sys

/-- A fixed-definition step keeps the definition. -/
theorem step_eq_some {op : Op}
    (h : sysStep accepts H permits Δ S (.step op) = some (Δ', S')) :
    Δ' = Δ ∧ step accepts H Δ S op = some S' := by
  simp only [sysStep, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨S'', hstep, rfl, rfl⟩ := h
  exact ⟨rfl, hstep⟩

/-- Every node of a structural replacement is a current node or a fresh allocation, and every
edge a current edge or a fresh allocation; fresh identities are outside the lifetime
records. -/
theorem structuralEdit?_fresh {e : Edit} {rep : Replacement}
    (h : structuralEdit? Δ S e = some rep) :
    (∀ v ∈ rep.next.nodes, v ∈ Δ.nodes ∨ v ∈ rep.freshNodes) ∧
      (∀ v ∈ rep.freshNodes, v ∉ S.usedNodes) ∧
      (∀ e ∈ rep.next.edges, e ∈ Δ.edges ∨ e ∈ rep.freshEdges) ∧
      ∀ e ∈ rep.freshEdges, e.id ∉ S.usedEdges := by
  obtain ⟨hv, rfl⟩ := Structural.structuralEdit?_eq_some.1 h
  refine ⟨fun v hv => ?_, hv.freshNodes, fun e he => ?_, hv.freshEdges⟩
  · exact (Structural.mem_apply_nodes.1 hv).imp_left And.left
  · exact (Structural.mem_apply_edges.1 he).imp_left And.left

/-- What a rewrite does, short of the cleanup table: the definition becomes a structural
replacement; accepted activations stay; a recorded package keeps its record or, when live,
only retires; the lifetime records and the change log grow by appending; and the revision
advances once. -/
theorem rewrite_eq_some {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) :
    ∃ rep, structuralEdit? Δ S req.edit = some rep ∧ Δ' = rep.next ∧
      S'.activations = S.activations ∧
      (∀ q r, S.packages q = some r → S'.packages q = some r ∨
        r.status = .live ∧ ∃ ret, S'.packages q = some { r with status := .retired ret }) ∧
      S'.usedNodes = S.usedNodes ++ rep.freshNodes ∧ S'.edgeLog = S.edgeLog ++ rep.freshEdges ∧
      S'.changeLog = S.changeLog ++ [S.revision + 1] ∧ S'.revision = S.revision + 1 := by
  simp only [rewrite, bind, Option.bind_eq_some_iff, Common.guard_eq_some, exists_const,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rep, hrep, fates, hfates, -, rfl, rfl⟩ := h
  refine ⟨rep, hrep, rfl, rfl, fun q r hr => ?_, rfl, rfl, rfl, rfl⟩
  dsimp only
  split
  · -- A retired package was named by the cleanup table, which names only live ones.
    rename_i reason hlookup
    refine .inr ⟨?_, _, by rw [hr, Option.map_some]⟩
    obtain ⟨_, _, hsplit, -⟩ := List.lookup_eq_some_iff.1 hlookup
    obtain ⟨f, hf, hfq⟩ :=
      List.mem_filterMap.1 (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
    obtain ⟨x, hx, hxq⟩ := Option.map_eq_some_iff.1 hfq
    obtain ⟨p, -, hp⟩ := (Activation.mapM_some hfates).2 f hf
    split at hp
    · rename_i r₀ hr₀
      split at hp
      · rename_i hlive
        obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hp
        obtain ⟨rfl, -⟩ := Prod.mk.inj hxq
        rw [hr₀, Option.some.injEq] at hr
        exact hr ▸ hlive
      · cases hp
        cases hx
    · cases hp
      cases hx
  · exact .inl hr

/-- A rewrite frames the state: only live packages change, and only their status. -/
theorem rewrite_frame {req : RewriteRequest} {evidence : List (Digest × Bytes)}
    (h : rewrite accepts H permits Δ S req evidence = some (Δ', S')) : Frame S S' := by
  obtain ⟨rep, -, -, hact, hpkg, hused, hlog, hchange, -⟩ := rewrite_eq_some h
  refine ⟨fun a act ha => hact ▸ ha, fun q r hr => ?_, ?_, ?_, ?_⟩
  · rcases hpkg q r hr with h' | ⟨hlive, ret, h'⟩
    · exact ⟨r, h', rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
    · exact ⟨_, h', rfl, rfl, rfl, rfl, fun _ => rfl, fun hs => absurd hlive hs⟩
  · rw [hused]
    exact List.subset_append_left _ _
  · rw [hlog]
    exact List.subset_append_left _ _
  · rw [hchange]
    exact List.subset_append_left _ _

/-- An extension frames the state: no record changes, and the change log grows. -/
theorem extend_frame {schema : Schema} {contracts : List Contract}
    (h : extend Δ S schema contracts = some (Δ', S')) : Frame S S' := by
  obtain ⟨-, rfl⟩ := extend_spec h
  exact ⟨fun _ _ h => h, fun _ r hr => ⟨r, hr, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩,
    List.Subset.refl _, List.Subset.refl _, List.subset_append_left _ _⟩

end Sys

/-- Every transition of a running workflow advances the revision exactly once. -/
theorem sysStep_revision {op : SysOp} (h : sysStep accepts H permits Δ S op = some (Δ', S')) :
    S'.revision = S.revision + 1 := by
  cases op with
  | step op => exact step_revision (Sys.step_eq_some h).2
  | rewrite req evidence =>
    obtain ⟨_, -, -, -, -, -, -, -, hrev⟩ := Sys.rewrite_eq_some h
    exact hrev
  | extend schema contracts =>
    obtain ⟨-, rfl⟩ := extend_spec h
    rfl

/-- Rewrites and extensions change no accepted activation, no package's immutable facts, no
delivery once made, and no status once no longer live; lifetime records only grow. -/
theorem sysStep_frame (hS : WF Δ S) {op : SysOp}
    (h : sysStep accepts H permits Δ S op = some (Δ', S')) : Frame S S' := by
  cases op with
  | step op => exact (step_frame hS (Sys.step_eq_some h).2).1
  | rewrite req evidence => exact Sys.rewrite_frame h
  | extend schema contracts => exact Sys.extend_frame h

/-- T6 Freshness: a new definition's nodes and edges are current ones or identities never
used before, so a deleted identity never returns. -/
theorem sysStep_fresh {op : SysOp} (h : sysStep accepts H permits Δ S op = some (Δ', S')) :
    (∀ v ∈ Δ'.nodes, v ∈ Δ.nodes ∨ v ∉ S.usedNodes) ∧
      ∀ e ∈ Δ'.edges, e ∈ Δ.edges ∨ e.id ∉ S.usedEdges := by
  cases op with
  | step op =>
    obtain ⟨rfl, -⟩ := Sys.step_eq_some h
    exact ⟨fun _ hv => .inl hv, fun _ he => .inl he⟩
  | rewrite req evidence =>
    obtain ⟨_, hrep, rfl, -⟩ := Sys.rewrite_eq_some h
    obtain ⟨hnodes, hfreshNodes, hedges, hfreshEdges⟩ := Sys.structuralEdit?_fresh hrep
    exact ⟨fun v hv => (hnodes v hv).imp_right (hfreshNodes v),
      fun e he => (hedges e he).imp_right (hfreshEdges e)⟩
  | extend schema contracts =>
    obtain ⟨rfl, -⟩ := extend_spec h
    exact ⟨fun _ hv => .inl hv, fun _ he => .inl he⟩

end Ontography.Proofs
