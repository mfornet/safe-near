import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `mldsa.jsonl` (oracle: `near-crypto` 0.37.4 `MLDSA65` over `aws-lc-rs` 1.16.2) against
the `Spec` and the `Impl` of ML-DSA-65: key generation from a seed, the acceptance of a raw secret
key, signatures with chosen randomness, and verification verdicts.
-/

namespace CryptoTests.MlDsa

open Lean NearCrypto MlDsa

def expect (what : String) (got want : ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {toHex got}, want {toHex want}"

def expectBool (what : String) (got want : Bool) : Option String :=
  if got == want then none else some s!"{what}: got {got}, want {want}"

def expectOpt (what : String) (got : Option ByteArray) (want : Option ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {got.map toHex}, want {want.map toHex}"

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

/-- The named keys of the `keygen` lines: name, public key, secret key. -/
abbrev Keys :=
  List (String × ByteArray × ByteArray)

def keysOf (lines : Array Json) : Keys :=
  lines.toList.filterMap fun j =>
    match str j "kind", str j "name", bytes j "public", bytes j "secret" with
    | .ok "keygen", .ok n, .ok pk, .ok sk => some (n, pk, sk)
    | _, _, _, _ => none

/-- The key of a `sign` or `verify` line: a named key or literal public key bytes. -/
def keyOf (keys : Keys) (j : Json) : Except String (ByteArray × ByteArray) := do
  match str j "key" with
  | .ok n =>
    match keys.lookup n with
    | some (pk, sk) =>
      pure (pk, sk)
    | none =>
      throw s!"unknown key {n}"
  | .error _ =>
    pure (← bytes j "public", ByteArray.empty)

def check (keys : Keys) (j : Json) : Except String (Option String) := do
  match ← str j "kind" with
  | "keygen" =>
    let seed ← bytes j "seed"
    let pk ← bytes j "public"
    let sk ← bytes j "secret"
    let (spk, ssk) := Spec.keyGen seed
    let (ipk, isk) := Impl.keyGen seed
    pure <|
        firstError
          [expect "Impl public key" ipk pk, expect "Impl secret key" isk sk,
            expect "Spec public key" spk pk, expect "Spec secret key" ssk sk]
  | "secret" =>
    let sk ← bytes j "secret"
    let valid ← bool j "valid"
    let pk ←
      if valid then
        some <$> bytes j "public"
      else
        pure none
    pure <|
        firstError
          [expectOpt "Impl publicKeyOfSecret" (Impl.publicKeyOfSecret sk) pk,
            expectOpt "Spec publicKeyOfSecret" (Spec.publicKeyOfSecret sk) pk]
  | "sign" =>
    let (pk, sk) ← keyOf keys j
    let msg ← message j
    let rnd ← bytes j "rnd"
    let sig ← bytes j "sig"
    pure <|
        firstError
          [expectOpt "Impl sign" (Impl.sign sk msg rnd) (some sig),
            expectBool "Impl verify" (Impl.verify pk msg sig) true,
            expectOpt "Spec sign" (Spec.sign sk msg rnd) (some sig),
            expectBool "Spec verify" (Spec.verify pk msg sig) true]
  | "verify" =>
    let (pk, _) ← keyOf keys j
    let msg ← message j
    let sig ← bytes j "sig"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl verify" (Impl.verify pk msg sig) valid,
            expectBool "Spec verify" (Spec.verify pk msg sig) valid]
  | k =>
    throw s!"unknown kind {k}"

end CryptoTests.MlDsa
