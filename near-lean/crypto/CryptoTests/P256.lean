import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `p256.jsonl` (oracle: `near-vm-runner` 0.37.4 `VMLogic::p256_verify`, over `p256`
0.13.2 and `ecdsa` 0.16.9) against the `Spec` and the `Impl` of `NearCrypto.P256`. A line is
`{kind, name, sig, msg, pk, ok, result}`: `ok = false` is a trap of the host function, else
`result` is its return value (1 for a valid signature).
-/

namespace CryptoTests.P256

open Lean NearCrypto

def expect (what : String) (got : Except String Bool) (want : Option Nat) : Option String :=
  match got, want with
  | .ok g, some w => if (if g then 1 else 0) == w then none else some s!"{what}: got {g}, want {w}"
  | .error _, none => none
  | .ok g, none => some s!"{what}: got {g}, want a trap"
  | .error e, some w => some s!"{what}: got error ({e}), want {w}"

def check (j : Json) : Except String (Option String) := do
  let sig ← bytes j "sig"
  let msg ← bytes j "msg"
  let pk ← bytes j "pk"
  let ok ← bool j "ok"
  let want ←
    if ok then
      some <$> j.getObjValAs? Nat "result"
    else
      pure none
  pure <|
      [expect "Impl" (P256.Impl.verify sig msg pk) want,
            expect "Spec" (P256.Spec.verify sig msg pk) want].findSome?
        id

end CryptoTests.P256
