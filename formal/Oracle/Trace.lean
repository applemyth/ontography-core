import Oracle.Codec
import Ontography.Step

/-!
# Trace decoding

A trace (`TRACE_FORMAT.md`) carries a definition, a validator for each
contract drawn from a fixed menu, a payload-commitment table computed by the
kernel, and the operations to replay. Decoding turns it into the model's
`Definition` and `Op` values plus the two parameters of the law: the
validators `accepts` and the commitment function `H`. It checks only the
trace's own well-formedness, never a premise of the law.
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
  definition : Definition
  /-- The validator of each contract, by contract identity. -/
  validators : List (ContractId × Validator)
  /-- The kernel's commitment of each payload, keyed by the payload's lowercase hex. -/
  digests : List (String × Digest)
  ops : List Op

/-- The validators `accepts` of the law. An identity outside the registry
names no predicate; an admitted definition never asks for one. -/
def Trace.accepts (t : Trace) (c : ContractId) (payload : Bytes) : Bool :=
  match t.validators.find? (·.1 == c) with
  | some (_, v) => v.accepts payload
  | none => false

/-- The commitment `H` of the law, read from the table. Decoding has checked
that every payload an operation carries has an entry. -/
def Trace.commit (t : Trace) (payload : Bytes) : Digest :=
  (t.digests.lookup (hexOfBytes payload)).getD ""

/-! ## Definition -/

def decodeValidator (j : Json) : Except String Validator := do
  match ← variant j with
  | ("accept_all", .null) => pure .acceptAll
  | ("reject_all", .null) => pure .rejectAll
  | ("first_byte_even", .null) => pure .firstByteEven
  | ("bytes_equal", bytes) => return .bytesEqual (← bytesOfHex (← string bytes))
  | (tag, _) => throw s!"unknown validator \"{tag}\""

def decodeContract (j : Json) : Except String (Contract × Validator) := do
  let id ← string (← field j "id")
  within s!"contract {id}" do
    let objectType ← string (← field j "object_type")
    let validator ← decodeValidator (← field j "validator")
    return (⟨id, objectType⟩, validator)

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

def decodeDefinition (j : Json) : Except String (Definition × List (ContractId × Validator)) := do
  let schema ← within "schema" do
    let s ← field j "schema"
    return (⟨← strings (← field s "node_types"), ← strings (← field s "object_types"),
      ← strings (← field s "tags")⟩ : Schema)
  let contracts ← (← array (← field j "contracts")).mapM decodeContract
  let definition : Definition := {
    schema
    contracts := contracts.map (·.1)
    nodes := ← within "nodes" (strings (← field j "nodes"))
    edges := ← within "edges" do (← array (← field j "edges")).mapM decodeEdge
    nodeDefs := ← (← array (← field j "node_definitions")).mapM decodeNodeDef
    edgeDefs := ← (← array (← field j "edge_definitions")).mapM decodeEdgeDef
    transitions := ← within "transitions" do
      (← array (← field j "transitions")).mapM decodeTransition
    roots := ← within "roots" do (← array (← field j "roots")).mapM decodeRoot }
  return (definition, contracts.map fun (c, v) => (c.id, v))

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

/-- One operation. Its `expect` field, if any, is the kernel's and is ignored. -/
def decodeOp (j : Json) : Except String Op := do
  match ← string (← field j "op") with
  | "activate" =>
    let id ← decodeActivationId (← field j "id")
    let trigger ← decodeTrigger (← field j "trigger")
    let result ← bytesOfHex (← string (← field j "result"))
    let emissions ← (← array (← field j "emissions")).mapM decodeEmission
    return .activate id ⟨trigger, result, emissions⟩
  | "transfer" =>
    return .transfer (← decodePackageId (← field j "package")) (← string (← field j "edge"))
      (← bytesOfHex (← string (← field j "payload")))
  | "retire" =>
    let evidence ← match ← field j "evidence" with
      | .null => pure none
      | a => pure (some (← decodeActivationId a))
    return .retire (← decodePackageId (← field j "package")) evidence
  | other => throw s!"unknown op \"{other}\""

/-- The payloads an operation commits to or checks against a commitment. -/
def opPayloads : Op → List Bytes
  | .activate _ proposal => proposal.emissions.map (·.payload)
  | .transfer _ _ payload => [payload]
  | .retire _ _ => []

/-! ## Trace -/

def traceFormat : String := "ontography-lean-trace/1"

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
  let (definition, validators) ← within "definition" (decodeDefinition (← field j "definition"))
  let digests ← within "digests" (decodeDigests (← field j "digests"))
  let ops ← (← array (← field j "ops")).zipIdx.mapM fun (op, i) => within s!"op {i}" (decodeOp op)
  for (op, i) in ops.zipIdx do
    for payload in opPayloads op do
      if (digests.lookup (hexOfBytes payload)).isNone then
        throw s!"op {i}: payload {hexOfBytes payload} has no entry in the digest table"
  return { definition, validators, digests, ops }

end Oracle
