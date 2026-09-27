import Ontography.Invariants

/-!
# Graph rewriting and vocabulary extension

MATHEMATICAL_DEFINITION §5–§6. A rewrite applies a registered production `L ← K → R` at
an injective, annotation-exact match, allocates fresh identities for `R ∖ K`, admits the
complete replacement definition, and retires the live packages its cleanup table names. An
extension enlarges the schema and the contract registry and changes nothing else.

The construction follows the kernel's `structural_rewrite`, `evaluate_rewrite`, and
`evaluate_extension`. Every comparison is a set comparison, as the kernel's sorted
collections make it. Payload evidence is a list of `(digest, bytes)` pairs; cleanup asks for
the bytes of a package only when some candidate edge's metadata accepts it, and a missing or
mismatched payload aborts the rewrite.
-/

namespace Ontography

namespace Definition

set_option synthInstance.maxSize 4096 in
instance (Δ : Definition) : Decidable Δ.Admitted :=
  decidable_of_iff
    ((∀ v ∈ Δ.nodes, v ≠ "") ∧ Δ.nodes.Nodup ∧ (∀ e ∈ Δ.edges, e.id ≠ "") ∧
      (Δ.edges.map (·.id)).Nodup ∧
      (∀ e ∈ Δ.edges, e.source ∈ Δ.nodes ∧ e.target ∈ Δ.nodes) ∧
      ((∀ t ∈ Δ.schema.nodeTypes, t ≠ "") ∧ (∀ o ∈ Δ.schema.objectTypes, o ≠ "") ∧
        ∀ t ∈ Δ.schema.tags, t ≠ "") ∧
      (Δ.contracts.map (·.id)).Nodup ∧
      (∀ c ∈ Δ.contracts, c.id ≠ "" ∧ c.objectType ∈ Δ.schema.objectTypes) ∧
      (Δ.nodeDefs.map (·.node)).Nodup ∧ (∀ d ∈ Δ.nodeDefs, d.node ∈ Δ.nodes) ∧
      (∀ v ∈ Δ.nodes, ∃ d ∈ Δ.nodeDefs, d.node = v) ∧
      (∀ d ∈ Δ.nodeDefs, d.types ≠ [] ∧ d.types ⊆ Δ.schema.nodeTypes ∧
        ∃ c ∈ Δ.contracts, c.id = d.resultContract) ∧
      (Δ.edgeDefs.map (·.edge)).Nodup ∧ (∀ d ∈ Δ.edgeDefs, ∃ e ∈ Δ.edges, e.id = d.edge) ∧
      (∀ e ∈ Δ.edges, ∃ d ∈ Δ.edgeDefs, d.edge = e.id) ∧
      (∀ d ∈ Δ.edgeDefs, d.types ≠ [] ∧ (∀ t ∈ d.types, t ≠ "") ∧ d.tags ≠ [] ∧
        d.tags ⊆ Δ.schema.tags ∧ ∃ c ∈ Δ.contracts, c.id = d.packageContract) ∧
      (∀ e ∈ Δ.edges, ∀ d ∈ Δ.edgeDefs, d.edge = e.id →
        ∀ s ∈ Δ.nodeDefs, s.node = e.source → ∀ t ∈ Δ.nodeDefs, t.node = e.target →
          d.sourceRequirements ⊆ s.types ∧ d.targetRequirements ⊆ t.types) ∧
      (∀ r ∈ Δ.transitions,
        r.node ∈ Δ.nodes ∧ r.source ⊆ Δ.schema.tags ∧ r.target ⊆ Δ.schema.tags) ∧
      (Δ.roots.map (·.node)).Nodup ∧
      (∀ r ∈ Δ.roots, r.node ∈ Δ.nodes ∧ r.ceiling ⊆ Δ.schema.tags))
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
          h19, h20⟩ =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
          h20⟩,
      fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
          h19, h20⟩ =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
          h20⟩⟩

/-- `v`'s authority-transition pairs. -/
def rulesOf (Δ : Definition) (v : NodeId) : List (Authority × Authority) :=
  (Δ.transitions.filter (·.node == v)).map fun r => (r.source, r.target)

/-- The outgoing edge identities of `v`. -/
def outgoing (Δ : Definition) (v : NodeId) : List EdgeId :=
  (Δ.edges.filter (·.source == v)).map (·.id)

end Definition

/-- Equal as sets of pairs of authority sets. -/
def PairSetEq (rs ss : List (Authority × Authority)) : Prop :=
  (∀ r ∈ rs, ∃ s ∈ ss, SetEq r.1 s.1 ∧ SetEq r.2 s.2) ∧
    ∀ s ∈ ss, ∃ r ∈ rs, SetEq r.1 s.1 ∧ SetEq r.2 s.2

instance (rs ss : List (Authority × Authority)) : Decidable (PairSetEq rs ss) := by
  unfold PairSetEq; infer_instance

/-- Equal root ceilings: both absent, or equal as sets. -/
def CeilingEq : Option Authority → Option Authority → Prop
  | none, none => True
  | some a, some b => SetEq a b
  | _, _ => False

instance : (a b : Option Authority) → Decidable (CeilingEq a b)
  | none, none => isTrue trivial
  | some a, some b => inferInstanceAs (Decidable (SetEq a b))
  | none, some _ => isFalse id
  | some _, none => isFalse id

/-- Node `a` of `Δ₁` and node `b` of `Δ₂` have the same local definition: types, result
contract, ingress, root ceiling, and authority transitions. -/
def SameNode (Δ₁ : Definition) (a : NodeId) (Δ₂ : Definition) (b : NodeId) : Prop :=
  match Δ₁.nodeDef? a, Δ₂.nodeDef? b with
  | some d₁, some d₂ =>
    SetEq d₁.types d₂.types ∧ d₁.resultContract = d₂.resultContract ∧
      d₁.ingress = d₂.ingress ∧ CeilingEq (Δ₁.ceiling? a) (Δ₂.ceiling? b) ∧
      PairSetEq (Δ₁.rulesOf a) (Δ₂.rulesOf b)
  | _, _ => False

instance (Δ₁ : Definition) (a : NodeId) (Δ₂ : Definition) (b : NodeId) :
    Decidable (SameNode Δ₁ a Δ₂ b) := by
  unfold SameNode; split <;> infer_instance

/-- Edge `a` of `Δ₁` and edge `b` of `Δ₂` have the same annotation. -/
def SameEdge (Δ₁ : Definition) (a : EdgeId) (Δ₂ : Definition) (b : EdgeId) : Prop :=
  match Δ₁.edgeDef? a, Δ₂.edgeDef? b with
  | some d₁, some d₂ =>
    SetEq d₁.types d₂.types ∧ SetEq d₁.sourceRequirements d₂.sourceRequirements ∧
      SetEq d₁.targetRequirements d₂.targetRequirements ∧
      d₁.packageContract = d₂.packageContract ∧ SetEq d₁.tags d₂.tags ∧
      d₁.authorityMatch = d₂.authorityMatch
  | _, _ => False

instance (Δ₁ : Definition) (a : EdgeId) (Δ₂ : Definition) (b : EdgeId) :
    Decidable (SameEdge Δ₁ a Δ₂ b) := by
  unfold SameEdge; split <;> infer_instance

/-- An annotated graph fragment whose identifiers are rule-local symbols. -/
structure Fragment where
  nodes : List NodeId
  edges : List Edge
  nodeDefs : List NodeDef
  edgeDefs : List EdgeDef
  transitions : List TransitionRule
  roots : List RootRule
  deriving DecidableEq, Repr

/-- The fragment as a complete definition under `Δ`'s schema and contracts. -/
def Fragment.under (F : Fragment) (Δ : Definition) : Definition :=
  { schema := Δ.schema, contracts := Δ.contracts, nodes := F.nodes, edges := F.edges,
    nodeDefs := F.nodeDefs, edgeDefs := F.edgeDefs, transitions := F.transitions,
    roots := F.roots }

/-- A production `L ← K → R`, with `K` given by its node and edge symbols. -/
structure Production where
  id : String
  left : Fragment
  interfaceNodes : List NodeId
  interfaceEdges : List EdgeId
  right : Fragment
  deriving DecidableEq, Repr

/-- A match: `L`'s symbols bound to current identities, and `R ∖ K`'s to fresh ones. -/
structure Match where
  nodes : List (NodeId × NodeId)
  edges : List (EdgeId × EdgeId)
  freshNodes : List (NodeId × NodeId)
  freshEdges : List (EdgeId × EdgeId)
  deriving DecidableEq, Repr

structure RewriteRequest where
  production : String
  matching : Match
  deriving DecidableEq, Repr

/-- `m` binds exactly the symbols `expected`, injectively, to nonempty identities. -/
def ExactBindings (m : List (String × String)) (expected : List String) : Prop :=
  (m.map Prod.fst).Nodup ∧ SetEq (m.map Prod.fst) expected ∧ (m.map Prod.snd).Nodup ∧
    ∀ x ∈ m.map Prod.snd, x ≠ ""

instance (m : List (String × String)) (expected : List String) :
    Decidable (ExactBindings m expected) := by
  unfold ExactBindings; infer_instance

/-- The admitted structural result of a rewrite. -/
structure Replacement where
  next : Definition
  deleted : List NodeId
  freshNodes : List NodeId
  freshEdges : List Edge

/-- The replacement definition for a match of `pr` in `Δ`, when the production is well
shaped, the match is exact, the allocations are fresh, no deleted node keeps an edge, and the
result is admitted (§5). -/
def structural? (Δ : Definition) (S : State) (pr : Production) (m : Match) :
    Option Replacement := do
  let L := pr.left.under Δ
  let R := pr.right.under Δ
  -- The production: a nonempty identity, admitted sides, and a preserved interface.
  guard (pr.id ≠ "")
  guard L.Admitted
  guard R.Admitted
  guard (∀ k ∈ pr.interfaceNodes, k ∈ L.nodes ∧ k ∈ R.nodes)
  guard (∀ k ∈ pr.interfaceEdges, ∃ a ∈ L.edges, a.id = k ∧ a ∈ R.edges ∧
    a.source ∈ pr.interfaceNodes ∧ a.target ∈ pr.interfaceNodes)
  guard (∀ k ∈ pr.interfaceNodes, SameNode L k R k)
  guard (∀ k ∈ pr.interfaceEdges, SameEdge L k R k)
  -- The match: exact, annotation-preserving bindings and unused fresh identities.
  let newNodes := R.nodes.filter (· ∉ pr.interfaceNodes)
  let newEdges := (R.edges.map (·.id)).filter (· ∉ pr.interfaceEdges)
  guard (ExactBindings m.nodes L.nodes)
  guard (ExactBindings m.edges (L.edges.map (·.id)))
  guard (ExactBindings m.freshNodes newNodes)
  guard (ExactBindings m.freshEdges newEdges)
  guard (∀ b ∈ m.nodes, SameNode L b.1 Δ b.2)
  guard (∀ le ∈ L.edges, ∃ he ∈ Δ.edges, m.edges.lookup le.id = some he.id ∧
    m.nodes.lookup le.source = some he.source ∧ m.nodes.lookup le.target = some he.target ∧
    SameEdge L le.id Δ he.id)
  guard (∀ b ∈ m.freshNodes, b.2 ∉ S.usedNodes)
  guard (∀ b ∈ m.freshEdges, b.2 ∉ S.usedEdges)
  -- Deletion: matched elements outside `K`, with no dangling edge.
  let deleted := (m.nodes.filter (·.1 ∉ pr.interfaceNodes)).map (·.2)
  let deletedEdges := (m.edges.filter (·.1 ∉ pr.interfaceEdges)).map (·.2)
  guard (∀ e ∈ Δ.edges, (e.source ∈ deleted ∨ e.target ∈ deleted) → e.id ∈ deletedEdges)
  -- The replacement: the current definition without the deleted part, plus `R ∖ K`.
  let place (s : NodeId) : NodeId :=
    (if s ∈ pr.interfaceNodes then m.nodes.lookup s else m.freshNodes.lookup s).getD s
  let freshEdges := m.freshEdges.filterMap fun b =>
    (R.edge? b.1).map fun re => ⟨b.2, place re.source, place re.target⟩
  let next : Definition := { Δ with
    nodes := Δ.nodes.filter (· ∉ deleted) ++ m.freshNodes.map (·.2)
    edges := Δ.edges.filter (·.id ∉ deletedEdges) ++ freshEdges
    nodeDefs := Δ.nodeDefs.filter (·.node ∉ deleted) ++
      m.freshNodes.filterMap fun b => (R.nodeDef? b.1).map fun d => { d with node := b.2 }
    edgeDefs := Δ.edgeDefs.filter (·.edge ∉ deletedEdges) ++
      m.freshEdges.filterMap fun b => (R.edgeDef? b.1).map fun d => { d with edge := b.2 }
    transitions := Δ.transitions.filter (·.node ∉ deleted) ++
      m.freshNodes.flatMap fun b =>
        (R.transitions.filter (·.node == b.1)).map fun r => { r with node := b.2 }
    roots := Δ.roots.filter (·.node ∉ deleted) ++
      m.freshNodes.filterMap fun b => (R.ceiling? b.1).map fun c => ⟨b.2, c⟩ }
  guard next.Admitted
  pure ⟨next, deleted, m.freshNodes.map (·.2), freshEdges⟩

/-- Edge `e` of `Δ` accepts `r` on metadata: its contract's object type and its authority
condition. -/
def Definition.MetadataAccepts (Δ : Definition) (e : Edge) (r : PackageRecord) : Prop :=
  match Δ.edgeDef? e.id with
  | some ed =>
    match Δ.contract? ed.packageContract with
    | some c => r.objectType = c.objectType ∧ ed.Allows r.authority
    | none => False
  | none => False

instance (Δ : Definition) (e : Edge) (r : PackageRecord) : Decidable (Δ.MetadataAccepts e r) := by
  unfold Definition.MetadataAccepts; split
  · split <;> infer_instance
  · infer_instance

section Rules

variable (accepts : ContractId → Bytes → Bool) (H : Bytes → Digest)

/-- The cleanup table of §5 for one live package `r` under `Δ ⟶ next`. `none` aborts the
rewrite, `some none` keeps the package, and `some (some reason)` retires it. -/
def cleanup? (Δ next : Definition) (deleted : List NodeId) (evidence : List (Digest × Bytes))
    (r : PackageRecord) : Option (Option Reason) :=
  if r.holder ∈ deleted then some (some .holderRemoved)
  else
    match r.delivery with
    | none =>
      if SetEq (Δ.outgoing r.holder) (next.outgoing r.holder) then some none
      else
        let candidates :=
          (next.edges.filter (·.source == r.holder)).filter (next.MetadataAccepts · r)
        if candidates = [] then some (some .noAcceptingEdge)
        else do
          let bytes ← evidence.lookup r.digest
          guard (H bytes = r.digest)
          if candidates.any fun e =>
              (next.edgeDef? e.id).any fun ed => accepts ed.packageContract bytes then
            some none
          else some (some .noAcceptingEdge)
    | some d =>
      match next.nodeDef? r.holder with
      | none => none
      | some nd =>
        match nd.ingress with
        | .any => some none
        | .all =>
          if d.edge ∈ next.incoming r.holder then some none else some (some .routeRemoved)

/-- A rewrite (§5): the registered production's admitted replacement, with every live package
kept or retired by the cleanup table, all at the successor revision. -/
def rewrite (grammar : List Production) (Δ : Definition) (S : State) (req : RewriteRequest)
    (evidence : List (Digest × Bytes)) : Option (Definition × State) := do
  guard (grammar.map (·.id)).Nodup
  let pr ← grammar.find? (·.id == req.production)
  let rep ← structural? Δ S pr req.matching
  let fates ← S.packageIds.mapM fun p =>
    match S.packages p with
    | some r =>
      if r.status = .live then
        (cleanup? accepts H Δ rep.next rep.deleted evidence r).map ((p, ·))
      else some (p, none)
    | none => some (p, none)
  let retired := fates.filterMap fun f => f.2.map ((f.1, ·))
  pure (rep.next, { S with
    packages := fun q =>
      match retired.lookup q with
      | some reason =>
        (S.packages q).map fun r => { r with status := .retired ⟨reason, S.revision + 1, none⟩ }
      | none => S.packages q
    usedNodes := S.usedNodes ++ rep.freshNodes
    edgeLog := S.edgeLog ++ rep.freshEdges
    changeLog := S.changeLog ++ [S.revision + 1]
    revision := S.revision + 1 })

end Rules

/-- A vocabulary extension (§6): the schema and contract registry grow, something is added,
the result is admitted, and nothing else changes. -/
def extend (Δ : Definition) (S : State) (schema : Schema) (contracts : List Contract) :
    Option (Definition × State) := do
  let next : Definition := { Δ with schema := schema, contracts := contracts }
  guard (Δ.schema.nodeTypes ⊆ schema.nodeTypes ∧ Δ.schema.objectTypes ⊆ schema.objectTypes ∧
    Δ.schema.tags ⊆ schema.tags)
  guard (Δ.contracts ⊆ contracts)
  guard (¬ (SetEq Δ.schema.nodeTypes schema.nodeTypes ∧
    SetEq Δ.schema.objectTypes schema.objectTypes ∧ SetEq Δ.schema.tags schema.tags ∧
    SetEq Δ.contracts contracts))
  guard next.Admitted
  pure (next, { S with changeLog := S.changeLog ++ [S.revision + 1], revision := S.revision + 1 })

end Ontography
