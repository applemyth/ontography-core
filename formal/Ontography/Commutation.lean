import Ontography.SystemTheorems

/-!
# Locality and commutation of rewrites (T4)

A rewrite decides the fate of a live package from its holder's neighborhood alone: whether
the holder is deleted, its outgoing edges before and after, and, for a receipt at an `All`
node, its incoming edges after. So two rewrites whose affected holders are disjoint decide
disjoint sets of packages, and applying them in either order yields the same frontier and
the same retirements, up to the revision each retirement is stamped with (TRANSITIONS §5, T4).

Graph independence is not enough, which is why affected holders are the hypothesis. Two edge
additions from one holder can retire its waiting package in one order and keep it in the
other; `Examples.lean` replays that counterexample.
-/

namespace Ontography

/-- The same admitted definition: equal as sets, component by component, which is what the
kernel's fingerprint compares. -/
def Definition.Equiv (Δ₁ Δ₂ : Definition) : Prop :=
  SetEq Δ₁.schema.nodeTypes Δ₂.schema.nodeTypes ∧
    SetEq Δ₁.schema.objectTypes Δ₂.schema.objectTypes ∧ SetEq Δ₁.schema.tags Δ₂.schema.tags ∧
    SetEq Δ₁.contracts Δ₂.contracts ∧ SetEq Δ₁.nodes Δ₂.nodes ∧ SetEq Δ₁.edges Δ₂.edges ∧
    SetEq Δ₁.nodeDefs Δ₂.nodeDefs ∧ SetEq Δ₁.edgeDefs Δ₂.edgeDefs ∧
    SetEq Δ₁.transitions Δ₂.transitions ∧ SetEq Δ₁.roots Δ₂.roots

/-- A record with its retirement revision erased. -/
def PackageRecord.unstamped (r : PackageRecord) : PackageRecord :=
  match r.status with
  | .retired ret => { r with status := .retired { ret with revision := 0 } }
  | _ => r

/-- The holders a rewrite `Δ ⟶ Δ'` can affect: deleted nodes, surviving sources whose outgoing
edge identities change, and surviving `All` receivers whose incoming edge identities change. -/
def Affected (Δ Δ' : Definition) (v : NodeId) : Prop :=
  v ∈ Δ.nodes ∧
    (v ∉ Δ'.nodes ∨ ¬ SetEq (Δ.outgoing v) (Δ'.outgoing v) ∨
      ((∃ nd, Δ'.nodeDef? v = some nd ∧ nd.ingress = .all) ∧
        ¬ SetEq (Δ.incoming v) (Δ'.incoming v)))

end Ontography
