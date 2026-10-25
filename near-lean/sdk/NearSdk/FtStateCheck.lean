import Lean.Data.Json
import NearSdk.FungibleToken

/-! `ft-state-check <storage.json> [expected-usage]`: decode a contract's raw storage (a JSON
array of `[key-hex, value-hex]` pairs) as a `FungibleToken` and check its invariant. Exits 0
when it holds, 1 when it does not, 2 when the storage does not decode. -/

open Lean NearSdk.FungibleToken

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    return UInt8.ofNat (16 * hi + lo) :: (← unhex rest)
  | [_] => none

private def storageOf (j : Json) : Except String (List (List UInt8 × List UInt8)) := do
  let rows ← j.getArr?
  rows.toList.mapM fun row => do
    let pair ← row.getArr?
    let #[k, v] := pair | throw "a storage row is not a [key, value] pair"
    let some key := unhex (← k.getStr?).toList | throw "key is not hex"
    let some value := unhex (← v.getStr?).toList | throw "value is not hex"
    pure (key, value)

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: ft-state-check <storage.json> [expected-usage]"; return 2
  let expected := args[1]?.bind String.toNat?
  let text ← IO.FS.readFile path
  match Json.parse text >>= storageOf >>= decode with
  | .error e => IO.eprintln s!"does not decode: {e}"; return 2
  | .ok token =>
    let bad := violations token expected
    IO.println s!"{token.balances.length} accounts, total supply {token.totalSupply}, \
      {token.others} other records"
    if bad.isEmpty then IO.println "invariant holds"; return 0
    for v in bad do IO.println s!"violation: {v}"
    return 1
