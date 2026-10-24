import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `bn254.jsonl` (oracle: `near-vm-runner` 0.37.4 `VMLogic::alt_bn128_*`, over
`zeropool-bn` 0.5.11) against the `Spec` and the `Impl` of `NearCrypto.Bn254`. A line is
`{kind, name, input, ok, output | result}`: `ok = false` is a trap of the host function.
-/

namespace CryptoTests.Bn

open Lean NearCrypto Bn254

/-- The reference pairing costs about 0.3 s a pair; it runs on the lines with few pairs. -/
def specPairs : Nat :=
  3

def expectBytes (what : String) (got : Except String ByteArray) (want : Option ByteArray) :
    Option String :=
  match got, want with
  | .ok g, some w => if g == w then none else some s!"{what}: got {toHex g}, want {toHex w}"
  | .error _, none => none
  | .ok g, none => some s!"{what}: got {toHex g}, want a trap"
  | .error e, some w => some s!"{what}: got error ({e}), want {toHex w}"

def expectCheck (what : String) (got : Except String Bool) (want : Option Bool) : Option String :=
  match got, want with
  | .ok g, some w => if g == w then none else some s!"{what}: got {g}, want {w}"
  | .error _, none => none
  | .ok g, none => some s!"{what}: got {g}, want a trap"
  | .error e, some w => some s!"{what}: got error ({e}), want {w}"

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

def check (j : Json) : Except String (Option String) := do
  let kind ← str j "kind"
  let input ← bytes j "input"
  let ok ← bool j "ok"
  match kind with
  | "g1_multiexp" | "g1_sum" =>
    let want ←
      if ok then
        some <$> bytes j "output"
      else
        pure none
    let run (ops : Ops) := if kind == "g1_multiexp" then g1Multiexp ops input else g1Sum ops input
    pure <|
        firstError [expectBytes "Impl" (run Impl.ops) want, expectBytes "Spec" (run Spec.ops) want]
  | "pairing_check" =>
    let want ←
      if ok then
        some <$> bool j "result"
      else
        pure none
    let spec :=
      if input.size / 192 ≤ specPairs then expectCheck "Spec" (pairingCheck Spec.ops input) want
      else none
    pure <| firstError [expectCheck "Impl" (pairingCheck Impl.ops input) want, spec]
  | k =>
    throw s!"unknown kind {k}"

end CryptoTests.Bn
