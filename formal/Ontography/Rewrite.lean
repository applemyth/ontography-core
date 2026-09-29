import Ontography.Invariants

/-!
# Graph rewriting and vocabulary extension

MATHEMATICAL_DEFINITION §5–§6. A rewrite applies an explicit edit: it removes current nodes
and edges, adds a fragment under identities never used before, admits the complete
replacement definition, retires the live packages its cleanup table names, and takes effect
only if the policy permits the principal that asks for it. An extension enlarges the schema
and the contract registry and changes nothing else.

The construction follows the kernel's `structural_edit`, `evaluate_rewrite`, and
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

/-- The outgoing edge identities of `v`. -/
def outgoing (Δ : Definition) (v : NodeId) : List EdgeId :=
  (Δ.edges.filter (·.source == v)).map (·.id)

end Definition

/-! ## Edits -/

/-- An annotated graph fragment: the six graph fields of a definition, without its schema and
contracts. -/
structure Fragment where
  nodes : List NodeId
  edges : List Edge
  nodeDefs : List NodeDef
  edgeDefs : List EdgeDef
  transitions : List TransitionRule
  roots : List RootRule
  deriving DecidableEq, Repr

/-- Who asks for a rewrite. The host names principals; the law never interprets one, and only
the policy reads it. -/
abbrev Principal := String

/-- An explicit graph edit (§5): the current nodes and edges it removes, and the fragment it
adds. The fragment names the identities it allocates, and its edges may end at surviving
nodes as well as added ones. -/
structure Edit where
  removeNodes : List NodeId
  removeEdges : List EdgeId
  add : Fragment
  deriving DecidableEq, Repr

/-- A rewrite request: an edit, and the principal asking for it. -/
structure RewriteRequest where
  principal : Principal
  edit : Edit
  deriving DecidableEq, Repr

namespace Edit

/-- `Δ` without what `e` removes, plus what `e` adds. Removing a node removes its definition,
transition rules, and root rule; removing an edge removes its annotation. -/
def apply (e : Edit) (Δ : Definition) : Definition :=
  { Δ with
    nodes := Δ.nodes.filter (· ∉ e.removeNodes) ++ e.add.nodes
    edges := Δ.edges.filter (·.id ∉ e.removeEdges) ++ e.add.edges
    nodeDefs := Δ.nodeDefs.filter (·.node ∉ e.removeNodes) ++ e.add.nodeDefs
    edgeDefs := Δ.edgeDefs.filter (·.edge ∉ e.removeEdges) ++ e.add.edgeDefs
    transitions := Δ.transitions.filter (·.node ∉ e.removeNodes) ++ e.add.transitions
    roots := Δ.roots.filter (·.node ∉ e.removeNodes) ++ e.add.roots }

/-- `e` defines only what it adds: every node definition, transition rule, and root rule it
carries belongs to an added node, and every edge annotation to an added edge. A surviving
node or edge therefore keeps its own; changing one means replacing it. -/
def DefinesOnlyAdded (e : Edit) : Prop :=
  (∀ d ∈ e.add.nodeDefs, d.node ∈ e.add.nodes) ∧
    (∀ d ∈ e.add.edgeDefs, d.edge ∈ e.add.edges.map (·.id)) ∧
    (∀ r ∈ e.add.transitions, r.node ∈ e.add.nodes) ∧ ∀ r ∈ e.add.roots, r.node ∈ e.add.nodes

instance (e : Edit) : Decidable e.DefinesOnlyAdded := by
  unfold DefinesOnlyAdded; infer_instance

end Edit

/-- The admitted structural result of a rewrite. -/
structure Replacement where
  next : Definition
  deleted : List NodeId
  freshNodes : List NodeId
  freshEdges : List Edge

/-- The replacement an edit `e` makes of `Δ` in state `S` (§5): it removes distinct current
nodes and edges and leaves no edge dangling, allocates only identities `S` has never used,
defines only what it adds, and yields an admitted definition. Admission also makes the
allocated identities distinct and nonempty. -/
def structuralEdit? (Δ : Definition) (S : State) (e : Edit) : Option Replacement := do
  -- Removal: distinct current nodes and edges, including every edge at a removed node.
  guard (e.removeNodes.Nodup ∧ ∀ v ∈ e.removeNodes, v ∈ Δ.nodes)
  guard (e.removeEdges.Nodup ∧ ∀ x ∈ e.removeEdges, x ∈ Δ.edges.map (·.id))
  guard (∀ ed ∈ Δ.edges,
    (ed.source ∈ e.removeNodes ∨ ed.target ∈ e.removeNodes) → ed.id ∈ e.removeEdges)
  -- Addition: identities never used, defining only what is added.
  guard (∀ v ∈ e.add.nodes, v ∉ S.usedNodes)
  guard (∀ ed ∈ e.add.edges, ed.id ∉ S.usedEdges)
  guard e.DefinesOnlyAdded
  -- The result.
  guard (e.apply Δ).Admitted
  pure ⟨e.apply Δ, e.removeNodes, e.add.nodes, e.add.edges⟩

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

/-- A rewrite policy: whether a principal may take `Δ` to `next` by an edit that retires the
listed packages. It is trusted, like the validators: the law takes it as a parameter, and every
theorem holds for every policy. -/
abbrev Policy := Principal → Definition → Edit → Definition → List (PackageId × Reason) → Bool

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

/-- A rewrite (§5): the edit's admitted replacement, with every live package kept or retired by
the cleanup table, all at the successor revision, provided the policy permits the principal
the edit and the retirements it makes. -/
def rewrite (permits : Policy) (Δ : Definition) (S : State) (req : RewriteRequest)
    (evidence : List (Digest × Bytes)) : Option (Definition × State) := do
  let rep ← structuralEdit? Δ S req.edit
  let fates ← S.packageIds.mapM fun p =>
    match S.packages p with
    | some r =>
      if r.status = .live then
        (cleanup? accepts H Δ rep.next rep.deleted evidence r).map ((p, ·))
      else some (p, none)
    | none => some (p, none)
  let retired := fates.filterMap fun f => f.2.map ((f.1, ·))
  guard (permits req.principal Δ req.edit rep.next retired)
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
