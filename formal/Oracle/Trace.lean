import Oracle.Codec
import Ontography.System

/-!
# Trace decoding

A trace (`TRACE_FORMAT.md`) carries the three parameters of a running workflow's law, which
stay fixed for the whole run: the validator each contract identity names (`accepts`), the
payload commitment computed by the kernel (`H`), and the rewrite grammar. It also carries the
initial definition and the operations to replay. Decoding turns them into the model's
`Definition`, `Production`, and `SysOp` values. It checks only the trace's own
well-formedness, never a premise of the law.
-/

namespace Oracle

open Lean (Json)
open Ontography

/-- The fixed validator menu both implementations provide. -/
inductive Validator where
  | acceptAll
  | rejectAll
  | bytesEqual (expected : Bytes)
  | firstByteEven

def Validator.accepts : Validator → Bytes → Bool
  | .acceptAll, _ => true
  | .rejectAll, _ => false
  | .bytesEqual expected, payload => payload == expected
  | .firstByteEven, payload =>
    match payload with
    | [] => false
    | b :: _ => b.toNat % 2 == 0

structure Trace where
  /-- The validator each contract identity names, for the whole run. -/
  validators : List (ContractId × Validator)
  /-- The kernel's commitment of each payload, keyed by the payload's lowercase hex. -/
  digests : List (String × Digest)
  grammar : List Production
  definition : Definition
  ops : List SysOp

/-- The validators `accepts` of the law. An identity with no validator names no predicate;
decoding has checked that every registered contract has one. -/
def Trace.accepts (t : Trace) (c : ContractId) (payload : Bytes) : Bool :=
  match t.validators.lookup c with
  | some v => v.accepts payload
  | none => false

/-- The commitment `H` of the law, read from the table. Decoding has checked that every
payload an operation carries has an entry. -/
def Trace.commit (t : Trace) (payload : Bytes) : Digest :=
  (t.digests.lookup (hexOfBytes payload)).getD ""

/-! ## Definitions and productions -/

def decodeValidator (j : Json) : Except String Validator := do
  match ← variant j with
  | ("accept_all", .null) => pure .acceptAll
  | ("reject_all", .null) => pure .rejectAll
  | ("first_byte_even", .null) => pure .firstByteEven
  | ("bytes_equal", bytes) => return .bytesEqual (← bytesOfHex (← string bytes))
  | (tag, _) => throw s!"unknown validator \"{tag}\""

def decodeValidators (j : Json) : Except String (List (ContractId × Validator)) := do
  match j with
  | .obj kvs => kvs.toList.mapM fun (id, v) => within s!"validator {id}" do
      return (id, ← decodeValidator v)
  | _ => throw "expected an object from contract identity to validator"

def decodeSchema (j : Json) : Except String Schema := do
  return ⟨← strings (← field j "node_types"), ← strings (← field j "object_types"),
    ← strings (← field j "tags")⟩

def decodeContract (j : Json) : Except String Contract := do
  return ⟨← string (← field j "id"), ← string (← field j "object_type")⟩

def decodeEdge (j : Json) : Except String Edge := do
  return ⟨← string (← field j "id"), ← string (← field j "source"), ← string (← field j "target")⟩

def decodeNodeDef (j : Json) : Except String NodeDef := do
  let node ← string (← field j "node")
  within s!"node definition {node}" do
    let ingress ← match ← string (← field j "ingress") with
      | "any" => pure Ingress.any
      | "all" => pure Ingress.all
      | other => throw s!"unknown ingress \"{other}\""
    return {
      node
      types := ← strings (← field j "types")
      resultContract := ← string (← field j "result_contract")
      ingress }

def decodeEdgeDef (j : Json) : Except String EdgeDef := do
  let edge ← string (← field j "edge")
  within s!"edge definition {edge}" do
    let authorityMatch ← match ← string (← field j "authority_match") with
      | "any_of" => pure AuthorityMatch.anyOf
      | "all_of" => pure AuthorityMatch.allOf
      | other => throw s!"unknown authority match \"{other}\""
    return {
      edge
      types := ← strings (← field j "types")
      sourceRequirements := ← strings (← field j "source_requirements")
      targetRequirements := ← strings (← field j "target_requirements")
      packageContract := ← string (← field j "package_contract")
      tags := ← strings (← field j "tags")
      authorityMatch }

def decodeTransition (j : Json) : Except String TransitionRule := do
  return ⟨← string (← field j "node"), ← strings (← field j "source"),
    ← strings (← field j "target")⟩

def decodeRoot (j : Json) : Except String RootRule := do
  return ⟨← string (← field j "node"), ← strings (← field j "ceiling")⟩

/-- The graph and annotations shared by a definition and a production side. -/
def decodeFragment (j : Json) : Except String Fragment := do
  return {
    nodes := ← within "nodes" (strings (← field j "nodes"))
    edges := ← within "edges" do (← array (← field j "edges")).mapM decodeEdge
    nodeDefs := ← (← array (← field j "node_definitions")).mapM decodeNodeDef
    edgeDefs := ← (← array (← field j "edge_definitions")).mapM decodeEdgeDef
    transitions := ← within "transitions" do
      (← array (← field j "transitions")).mapM decodeTransition
    roots := ← within "roots" do (← array (← field j "roots")).mapM decodeRoot }

def decodeDefinition (j : Json) : Except String Definition := do
  let schema ← within "schema" (decodeSchema (← field j "schema"))
  let contracts ← within "contracts" do (← array (← field j "contracts")).mapM decodeContract
  let F ← decodeFragment j
  return {
    schema
    contracts
    nodes := F.nodes
    edges := F.edges
    nodeDefs := F.nodeDefs
    edgeDefs := F.edgeDefs
    transitions := F.transitions
    roots := F.roots }

def decodeProduction (j : Json) : Except String Production := do
  let id ← string (← field j "id")
  within s!"production {id}" do
    return {
      id
      left := ← within "left" (decodeFragment (← field j "left"))
      interfaceNodes := ← strings (← field j "interface_nodes")
      interfaceEdges := ← strings (← field j "interface_edges")
      right := ← within "right" (decodeFragment (← field j "right")) }

/-! ## Operations -/

def decodeActivationId (j : Json) : Except String ActivationId := do
  natOfDecimal (← string j)

/-- `[producer, output]`: the producer as a decimal string, the output as a number. -/
def decodePackageId (j : Json) : Except String PackageId := do
  match ← array j with
  | [producer, output] => return ⟨← decodeActivationId producer, ← natural output⟩
  | _ => throw s!"expected a package id [producer, output], found {j.compress}"

def decodeTrigger (j : Json) : Except String Trigger := do
  match ← variant j with
  | ("orig", o) => return .orig (← string (← field o "node")) (← strings (← field o "authority"))
  | ("pkgs", inputs) => return .pkgs (← (← array inputs).mapM decodePackageId)
  | (tag, _) => throw s!"unknown trigger \"{tag}\""

def decodeEmission (j : Json) : Except String Emission := do
  let destination ← match ← variant (← field j "destination") with
    | ("delivered", edge) => pure (Destination.delivered (← string edge))
    | ("outbound", objectType) => pure (Destination.outbound (← string objectType))
    | (tag, _) => throw s!"unknown destination \"{tag}\""
  let authority ← match ← variant (← field j "authority") with
    | ("carry", .null) => pure OutputAuthority.carry
    | ("transition", target) => pure (OutputAuthority.transition (← strings target))
    | (tag, _) => throw s!"unknown output authority \"{tag}\""
  return ⟨destination, authority, ← bytesOfHex (← string (← field j "payload"))⟩

/-- Symbol bindings `[[symbol, identity], ...]`. -/
def decodeBindings (j : Json) : Except String (List (String × String)) := do
  (← array j).mapM fun pair => do
    match ← array pair with
    | [symbol, identity] => return (← string symbol, ← string identity)
    | _ => throw s!"expected a binding [symbol, identity], found {pair.compress}"

def decodeMatch (j : Json) : Except String Match := do
  return {
    nodes := ← within "nodes" (decodeBindings (← field j "nodes"))
    edges := ← within "edges" (decodeBindings (← field j "edges"))
    freshNodes := ← within "fresh_nodes" (decodeBindings (← field j "fresh_nodes"))
    freshEdges := ← within "fresh_edges" (decodeBindings (← field j "fresh_edges")) }

/-- Payload evidence `{digest: bytes}`: the bytes offered for each commitment. -/
def decodeEvidence (j : Json) : Except String (List (Digest × Bytes)) := do
  match j with
  | .obj kvs =>
    kvs.toList.mapM fun (digest, bytes) => do
      let key ← bytesOfHex digest
      if hexOfBytes key != digest then
        throw s!"evidence key \"{digest}\" is not lowercase hex"
      return (digest, ← bytesOfHex (← string bytes))
  | _ => throw "expected an object from digest to payload"

/-- One operation. Its `expect` field, if any, is the kernel's and is ignored. -/
def decodeOp (j : Json) : Except String SysOp := do
  match ← string (← field j "op") with
  | "activate" =>
    let id ← decodeActivationId (← field j "id")
    let trigger ← decodeTrigger (← field j "trigger")
    let result ← bytesOfHex (← string (← field j "result"))
    let emissions ← (← array (← field j "emissions")).mapM decodeEmission
    return .step (.activate id ⟨trigger, result, emissions⟩)
  | "transfer" =>
    return .step (.transfer (← decodePackageId (← field j "package"))
      (← string (← field j "edge")) (← bytesOfHex (← string (← field j "payload"))))
  | "retire" =>
    let evidence ← match ← field j "evidence" with
      | .null => pure none
      | a => pure (some (← decodeActivationId a))
    return .step (.retire (← decodePackageId (← field j "package")) evidence)
  | "rewrite" =>
    let production ← string (← field j "production")
    let matching ← within "match" (decodeMatch (← field j "match"))
    let evidence ← within "evidence" (decodeEvidence (← field j "evidence"))
    return .rewrite ⟨production, matching⟩ evidence
  | "extend" =>
    let schema ← within "schema" (decodeSchema (← field j "schema"))
    let contracts ← within "contracts" do (← array (← field j "contracts")).mapM decodeContract
    return .extend schema contracts
  | other => throw s!"unknown op \"{other}\""

/-- The payloads an operation commits to, checks against a commitment, or offers as
evidence. -/
def opPayloads : SysOp → List Bytes
  | .step (.activate _ proposal) => proposal.emissions.map (·.payload)
  | .step (.transfer _ _ payload) => [payload]
  | .step (.retire _ _) => []
  | .rewrite _ evidence => evidence.map (·.2)
  | .extend _ _ => []

/-- The contracts an operation registers. -/
def opContracts : SysOp → List Contract
  | .extend _ contracts => contracts
  | _ => []

/-! ## Trace -/

def traceFormat : String := "ontography-lean-trace/2"

def decodeDigests (j : Json) : Except String (List (String × Digest)) := do
  match j with
  | .obj kvs =>
    kvs.toList.mapM fun (payload, digest) => do
      let bytes ← bytesOfHex payload
      if hexOfBytes bytes != payload then
        throw s!"payload key \"{payload}\" is not lowercase hex"
      return (payload, ← string digest)
  | _ => throw "expected an object from payload hex to digest hex"

def decodeTrace (input : String) : Except String Trace := do
  let j ← Json.parse input
  let format ← within "format" (string (← field j "format"))
  if format != traceFormat then
    throw s!"unsupported trace format \"{format}\", expected \"{traceFormat}\""
  let validators ← within "validators" (decodeValidators (← field j "validators"))
  let digests ← within "digests" (decodeDigests (← field j "digests"))
  let grammar ← within "grammar" do (← array (← field j "grammar")).mapM decodeProduction
  let definition ← within "definition" (decodeDefinition (← field j "definition"))
  let ops ← (← array (← field j "ops")).zipIdx.mapM fun (op, i) => within s!"op {i}" (decodeOp op)
  for c in definition.contracts do
    if (validators.lookup c.id).isNone then
      throw s!"contract {c.id} has no validator"
  for (op, i) in ops.zipIdx do
    for payload in opPayloads op do
      if (digests.lookup (hexOfBytes payload)).isNone then
        throw s!"op {i}: payload {hexOfBytes payload} has no entry in the digest table"
    for c in opContracts op do
      if (validators.lookup c.id).isNone then
        throw s!"op {i}: contract {c.id} has no validator"
  return { validators, digests, grammar, definition, ops }

end Oracle
