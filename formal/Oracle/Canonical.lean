import Oracle.Codec
import Ontography.State

/-!
# Canonical state encoding

Encodes a running workflow, a definition and a state bound to it, in the canonical form of
`TRACE_FORMAT.md`, the form the kernel's current definition and checkpoint are encoded in.
Maps are arrays of entries in ascending key order, and every set is sorted and
deduplicated, since the model's lists stand for sets: authorities, trigger inputs, lifetime
identities, and each component of the definition.

The ghost fields map to what the kernel records: `usedEdges` (the identities of `edgeLog`) to
`used_edges` and `definitionChanges` (the length of `changeLog`) to `definition_changes`. Edge
incidence, the `changeLog` revisions, and the order of `activationIds` and `packageIds` have
no kernel counterpart and are not encoded. The domains of `A` and `P` are read from
`activationIds` and `packageIds`; an identity listed there without a record encodes as
`null`, which a well-formed state never produces.
-/

namespace Oracle

open Lean (Json)
open Ontography

def sortStrings (xs : List String) : List String :=
  xs.mergeSort fun a b => compare a b != .gt

/-- Removes adjacent repeats, so a sorted list becomes a sorted set. -/
def dedupSorted [BEq α] (xs : List α) : List α :=
  xs.foldr (init := []) fun x acc =>
    match acc with
    | y :: _ => if x == y then acc else x :: acc
    | [] => [x]

/-- A set of identifiers: sorted and deduplicated. -/
def canonicalStrings (xs : List String) : List String := dedupSorted (sortStrings xs)

def sortPackageIds (ps : List PackageId) : List PackageId :=
  ps.mergeSort fun p q =>
    decide (p.producer < q.producer) || (p.producer == q.producer && decide (p.output ≤ q.output))

/-- Lexicographic comparison of lists. -/
def lexCompare (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmp a b with
    | .eq => lexCompare cmp as bs
    | order => order

def jstr (s : String) : Json := .str s

def jarr (xs : List Json) : Json := .arr xs.toArray

def jopt (x : Option α) (f : α → Json) : Json :=
  match x with
  | some a => f a
  | none => .null

/-- An authority, or any set of identifiers: sorted and deduplicated. -/
def jset (xs : List String) : Json := jarr ((canonicalStrings xs).map jstr)

/-- A set of structured entries, each paired with its sort key: sorted by key, lexicographic
on lists of identifiers, with repeated entries removed. -/
def jentries (entries : List (List (List String) × Json)) : Json :=
  let sorted := entries.mergeSort fun a b => lexCompare (lexCompare compare) a.1 b.1 != .gt
  jarr ((dedupSorted sorted).map (·.2))

def jid (a : ActivationId) : Json := jstr (decimal a)

def jpackage (p : PackageId) : Json := jarr [jid p.producer, jnat p.output]

/-! ## The definition -/

def encodeSchema (s : Schema) : Json :=
  Json.mkObj [
    ("node_types", jset s.nodeTypes),
    ("object_types", jset s.objectTypes),
    ("tags", jset s.tags)]

def encodeNodeDef (d : NodeDef) : Json :=
  Json.mkObj [
    ("node", jstr d.node),
    ("types", jset d.types),
    ("result_contract", jstr d.resultContract),
    ("ingress", jstr (match d.ingress with | .any => "any" | .all => "all"))]

def encodeEdgeDef (d : EdgeDef) : Json :=
  Json.mkObj [
    ("edge", jstr d.edge),
    ("types", jset d.types),
    ("source_requirements", jset d.sourceRequirements),
    ("target_requirements", jset d.targetRequirements),
    ("package_contract", jstr d.packageContract),
    ("tags", jset d.tags),
    ("authority_match", jstr (match d.authorityMatch with | .anyOf => "any_of" | .allOf => "all_of"))]

/-- The definition, component by component, each as a canonical set. -/
def encodeDefinition (Δ : Definition) : Json :=
  Json.mkObj [
    ("schema", encodeSchema Δ.schema),
    ("contracts", jentries (Δ.contracts.map fun c =>
      ([[c.id]], Json.mkObj [("id", jstr c.id), ("object_type", jstr c.objectType)]))),
    ("nodes", jset Δ.nodes),
    ("edges", jentries (Δ.edges.map fun e =>
      ([[e.id]], Json.mkObj [("id", jstr e.id), ("source", jstr e.source),
        ("target", jstr e.target)]))),
    ("node_definitions", jentries (Δ.nodeDefs.map fun d => ([[d.node]], encodeNodeDef d))),
    ("edge_definitions", jentries (Δ.edgeDefs.map fun d => ([[d.edge]], encodeEdgeDef d))),
    ("transitions", jentries (Δ.transitions.map fun r =>
      ([[r.node], canonicalStrings r.source, canonicalStrings r.target],
        Json.mkObj [("node", jstr r.node), ("source", jset r.source),
          ("target", jset r.target)]))),
    ("roots", jentries (Δ.roots.map fun r =>
      ([[r.node]], Json.mkObj [("node", jstr r.node), ("ceiling", jset r.ceiling)])))]

/-! ## The state -/

def encodeTrigger : Trigger → Json
  | .orig v α => Json.mkObj [("orig", Json.mkObj [("node", jstr v), ("authority", jset α)])]
  | .pkgs inputs => Json.mkObj [("pkgs", jarr ((sortPackageIds inputs).map jpackage))]

def encodeOutput (a : ActivationId) (o : Output) (i : Nat) : Json :=
  Json.mkObj [
    ("package", jpackage ⟨a, i⟩),
    ("edge", jopt o.edge jstr),
    ("object_type", jstr o.objectType),
    ("authority", jset o.authority),
    ("digest", jstr o.digest)]

def encodeActivation (a : ActivationId) : Option Activation → Json
  | none => .null
  | some act => Json.mkObj [
      ("id", jid a),
      ("node", jstr act.node),
      ("trigger", encodeTrigger act.trigger),
      ("result", jstr (hexOfBytes act.result)),
      ("outputs", jarr (act.outputs.zipIdx.map fun (o, i) => encodeOutput a o i))]

def reasonName : Reason → String
  | .holderRemoved => "holder_removed"
  | .noAcceptingEdge => "no_accepting_edge"
  | .routeRemoved => "route_removed"
  | .explicit => "explicit"

def encodeStatus : Status → Json
  | .live => jstr "live"
  | .consumed b => Json.mkObj [("consumed", jid b)]
  | .retired ret => Json.mkObj [("retired", Json.mkObj [
      ("reason", jstr (reasonName ret.reason)),
      ("revision", jnat ret.revision),
      ("evidence", jopt ret.evidence jid)])]

def encodeDelivery (d : Delivery) : Json :=
  Json.mkObj [("edge", jstr d.edge), ("receiver", jstr d.receiver)]

def encodePackage (p : PackageId) : Option PackageRecord → Json
  | none => .null
  | some r => Json.mkObj [
      ("id", jpackage p),
      ("object_type", jstr r.objectType),
      ("authority", jset r.authority),
      ("digest", jstr r.digest),
      ("producer_node", jstr r.producerNode),
      ("delivery", jopt r.delivery encodeDelivery),
      ("status", encodeStatus r.status)]

/-- The running workflow `(Δ, S)`. -/
def encodeState (Δ : Definition) (S : State) : Json :=
  Json.mkObj [
    ("definition", encodeDefinition Δ),
    ("activations", jarr ((S.activationIds.mergeSort).map fun a => encodeActivation a (S.activations a))),
    ("packages", jarr ((sortPackageIds S.packageIds).map fun p => encodePackage p (S.packages p))),
    ("used_nodes", jset S.usedNodes),
    ("used_edges", jset S.usedEdges),
    ("definition_changes", jnat S.definitionChanges),
    ("revision", jnat S.revision)]

end Oracle
