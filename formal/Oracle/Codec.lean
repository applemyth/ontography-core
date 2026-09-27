import Lean.Data.Json
import Ontography.Basic

/-!
# Codec primitives for the trace oracle

Hexadecimal bytes, decimal naturals, and checked access to JSON values. The
trace format is specified in `TRACE_FORMAT.md`; nothing here knows the law.
-/

namespace Oracle

open Lean (Json JsonNumber)
open Ontography (Bytes)

/-! ## Hexadecimal bytes -/

/-- The lowercase hexadecimal digit of a nibble `n < 16`. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- Lowercase hexadecimal, two digits per byte. -/
def hexOfBytes (bytes : Bytes) : String :=
  bytes.foldl (fun s b => (s.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

def nibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decodes hexadecimal of either case, two digits per byte. -/
def bytesOfHex (s : String) : Except String Bytes :=
  go s.toList
where
  go : List Char → Except String Bytes
    | [] => pure []
    | [_] => throw s!"hex string \"{s}\" has odd length"
    | hi :: lo :: rest => do
      let some h := nibble? hi | throw s!"invalid hex digit '{hi}' in \"{s}\""
      let some l := nibble? lo | throw s!"invalid hex digit '{lo}' in \"{s}\""
      return UInt8.ofNat (h * 16 + l) :: (← go rest)

/-! ## Decimal naturals -/

/-- The decimal digits of `n`. A large value is printed in 18-digit chunks, so
a `u128` costs a few big-number divisions rather than one per digit. -/
partial def decimal (n : Nat) : String :=
  let chunk := 1000000000000000000
  if n < chunk then
    toString n
  else
    let low := toString (n % chunk)
    (decimal (n / chunk)).pushn '0' (18 - low.length) ++ low

/-- A nonempty string of decimal digits, as the kernel prints a `u128`. -/
def natOfDecimal (s : String) : Except String Nat :=
  if !s.isEmpty && s.all Char.isDigit then
    pure (s.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  else
    throw s!"expected a decimal natural number, found \"{s}\""

#guard decimal 0 = "0"
#guard decimal 999999999999999999 = toString 999999999999999999
#guard decimal 1000000000000000000 = toString 1000000000000000000
#guard decimal 1000000000000000007000000000000000001 = toString 1000000000000000007000000000000000001
#guard decimal 340282366920938463463374607431768211455 = "340282366920938463463374607431768211455"
#guard (natOfDecimal "340282366920938463463374607431768211455").toOption =
  some 340282366920938463463374607431768211455
#guard (natOfDecimal "1_0").toOption = none
#guard hexOfBytes [0, 1, 171, 255] = "0001abff"
#guard (bytesOfHex "0001ABff").toOption = some [0, 1, 171, 255]
#guard (bytesOfHex "abc").toOption = none

/-! ## JSON access -/

/-- Prefixes an error with the location it arose at. -/
def within (context : String) (x : Except String α) : Except String α :=
  x.mapError fun e => s!"{context}: {e}"

def field (j : Json) (key : String) : Except String Json :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | some v => pure v
    | none => throw s!"missing field \"{key}\""
  | _ => throw s!"expected an object with field \"{key}\""

def string (j : Json) : Except String String :=
  match j with
  | .str s => pure s
  | _ => throw s!"expected a string, found {j.compress}"

def natural (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"expected a natural number, found {j.compress}"

def array (j : Json) : Except String (List Json) :=
  match j with
  | .arr elems => pure elems.toList
  | _ => throw s!"expected an array, found {j.compress}"

def strings (j : Json) : Except String (List String) := do
  (← array j).mapM string

/-- An externally tagged variant: a bare string names a unit variant, and a
one-key object names a variant carrying the key's value. -/
def variant (j : Json) : Except String (String × Json) :=
  match j with
  | .str tag => pure (tag, .null)
  | .obj kvs =>
    match kvs.toList with
    | [(tag, value)] => pure (tag, value)
    | _ => throw s!"expected a one-key object, found {j.compress}"
  | _ => throw s!"expected a variant, found {j.compress}"

/-- A JSON number from a natural. -/
def jnat (n : Nat) : Json := .num (JsonNumber.fromNat n)

end Oracle
