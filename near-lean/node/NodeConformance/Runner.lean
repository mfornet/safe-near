import Lean.Data.Json
import NearNode.Borsh

/-!
# Fixture runner

One fixture line is `{"type", "name", "borsh", "hash", ...}` or, for inputs both
decoders must reject, `{"type", "name", "borsh", "reject": true}`. A line may
carry `"canonical"`: the bytes the value re-encodes to, when the input was
accepted but is not the canonical encoding. Derived values are further hex
fields (`"hash"`, `"hashes"`, `"sigData"`, `"root"`, ...); the test computes each
one and fails on a field it does not compute, or that the line lacks.
-/

namespace Near.Node.Conformance

open Lean Borsh

/-- Lowercase hex of `b`. -/
def toHex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat)
  b.foldl (fun s x => (s.push (digit (x >>> 4))).push (digit (x &&& 15))) ""

/-- Parse hex; `none` on odd length or a non-hex character. -/
def ofHex (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then
    none
  let nibble (c : Char) : Option UInt8 :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87).toUInt8 else none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push ((← nibble cs[2 * i]!) <<< 4 ||| (← nibble cs[2 * i + 1]!))
  pure out

/-- A fixture line, decoded. -/
structure Line where
  name : String
  borsh : ByteArray
  reject : Bool
  canonical : Option ByteArray
  /-- The derived hash fields present on the line. -/
  hashes : List (String × Option String)

/-- Fields other than these are derived hashes. -/
private def reserved (key : String) : List String :=
  ["type", "name", key, "reject", "canonical"]

/-- Parses a line whose input is in the field `key` (`borsh`; `proto` for protobuf messages). -/
def parseLine (s : String) (key : String := "borsh") : Except String Line := do
  let j ← Json.parse s
  let str (k : String) : Except String String := j.getObjValAs? String k
  let borsh ←
    match ofHex (← str key) with
    | some b =>
      pure b
    | none =>
      throw s!"{key} is not hex"
  let canonical ←
    match j.getObjValAs? String "canonical" with
    | .ok c =>
      match ofHex c with
      | some b =>
        pure (some b)
      | none =>
        throw "canonical is not hex"
    | .error _ =>
      pure none
  let fields ← j.getObj?
  let hashes :=
    fields.toList.filterMap fun (k, v) =>
      if (reserved key).contains k then none else some (k, v.getStr?.toOption)
  pure
      { name := ← str "name", borsh, reject := (j.getObjValAs? Bool "reject").toOption.getD false,
        canonical, hashes }

/-- Checks one line against a type; `none` means it passed. -/
abbrev Check :=
  Line → Option String

/-- Derived hashes of a value, as `(field, bytes)`. -/
abbrev Hashes (α : Type) :=
  α → List (String × ByteArray)

/-- Decode with both decoders, re-encode with both encoders, compare with the fixture, and check
every derived hash. Rejected lines must be rejected by both decoders. -/
def check (α : Type) [c : Codec α] (hashes : Hashes α := fun _ => []) : Check := fun line =>
  let implDec := Codec.decodeAll (α := α) line.borsh
  let specDec := Codec.decodeAllSpec (α := α) line.borsh.toList
  if line.reject then
    match implDec, specDec with
    | .error _, .error _ => none
    | .ok _, _ => some "Impl accepted an input that nearcore rejects"
    | _, .ok _ => some "Spec accepted an input that nearcore rejects"
  else
    let expected := line.canonical.getD line.borsh
    match implDec, specDec with
    | .error e, _ => some s!"Impl rejected a valid input: {repr e}"
    | _, .error e => some s!"Spec rejected a valid input: {repr e}"
    | .ok v, .ok w =>
      if Codec.encode v != expected then some "Impl encode of the Impl decoding differs"
      else
        if Codec.encodeSpec v != expected.toList then
          some "Spec encode of the Impl decoding differs"
        else
          if Codec.encodeSpec w != expected.toList then
            some "Spec encode of the Spec decoding differs"
          else
            if Codec.encode w != expected then some "Impl encode of the Spec decoding differs"
            else
              let derived := hashes v
              (derived.findSome? fun (k, h) =>
                    match line.hashes.lookup k with
                    | some (some x) =>
                      if x == toHex h then none else some s!"{k} differs: {toHex h} vs {x}"
                    | _ => some s!"fixture has no {k}").orElse
                fun _ =>
                line.hashes.findSome? fun (k, x) =>
                  if x.isSome && !derived.any (·.1 == k) then
                    some s!"fixture has {k}, which the test does not compute"
                  else none

end Near.Node.Conformance
