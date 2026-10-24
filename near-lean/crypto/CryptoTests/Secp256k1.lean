import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `secp256k1.jsonl` (oracle: `near-crypto` 0.37.4 over `secp256k1` 0.27.0, the
`libsecp256k1` of `secp256k1-sys` 0.8.2) against the `Spec` and the `Impl`.
-/

namespace CryptoTests.Secp

open Lean NearCrypto Secp256k1

def expect (what : String) (got want : ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {toHex got}, want {toHex want}"

def expectBool (what : String) (got want : Bool) : Option String :=
  if got == want then none else some s!"{what}: got {got}, want {want}"

def expectOpt (what : String) (got : Option ByteArray) (want : Option ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {got.map toHex}, want {want.map toHex}"

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

/-- The 64 bytes `x ‖ y` of a `Spec` point. -/
def specRaw (p : Option (Nat × Nat)) : Option ByteArray :=
  p.map fun (x, y) => Spec.serializeRaw x y

/-- The expected bytes of field `k`, present only on a valid line. -/
def wanted (j : Json) (valid : Bool) (k : String) : Except String (Option ByteArray) :=
  if valid then some <$> bytes j k else pure none

def check (j : Json) : Except String (Option String) := do
  match ← str j "kind" with
  | "secret" =>
    let sk ← bytes j "secret"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl validSecret" (Impl.validSecret sk) valid,
            expectBool "Spec validSecret" (Spec.validSecret sk) valid]
  | "keypair" =>
    let sk ← bytes j "secret"
    let pk ← bytes j "public"
    let compressed ← bytes j "compressed"
    pure <|
        firstError
          [expectOpt "Impl publicKey" (Impl.publicKey sk) (some pk),
            expectOpt "Spec publicKey" (specRaw (Spec.publicKey sk)) (some pk),
            expectOpt "Impl compressed" ((Impl.parsePublicKey (compressed)).map Impl.serializeRaw)
              (some pk),
            expectOpt "Spec compressed" (specRaw (Spec.parsePublicKey compressed)) (some pk)]
  | "sign" =>
    let sk ← bytes j "secret"
    let pk ← bytes j "public"
    let msg ← bytes j "msg"
    let sig ← bytes j "sig"
    pure <|
        firstError
          [expectOpt "Impl sign" (Impl.signRecoverable sk msg) (some sig),
            expectOpt "Spec sign" (Spec.signRecoverable sk msg) (some sig),
            expectBool "Impl verify" (Impl.verify pk msg sig) true,
            expectBool "Spec verify" (Spec.verify pk msg sig) true,
            expectOpt "Impl recover" (Impl.recoverKey msg sig) (some pk),
            expectOpt "Spec recover" (Spec.recoverKey msg sig) (some pk)]
  | "pubkey" =>
    let b ← bytes j "bytes"
    let valid ← bool j "valid"
    let want ← wanted j valid "public"
    let wantCompressed ← wanted j valid "compressed"
    pure <|
        firstError
          [expectOpt "Impl parse" ((Impl.parsePublicKey b).map Impl.serializeRaw) want,
            expectOpt "Spec parse" (specRaw (Spec.parsePublicKey b)) want,
            expectOpt "Impl compressed" ((Impl.parsePublicKey b).map Impl.serializeCompressed)
              wantCompressed,
            expectOpt "Spec compressed"
              ((Spec.parsePublicKey b).map fun (x, y) => Spec.serializeCompressed x y)
              wantCompressed]
  | "recover" =>
    let msg ← bytes j "msg"
    let rs ← bytes j "sig"
    let v ← int j "v"
    let valid ← bool j "valid"
    let want ← wanted j valid "public"
    -- an id outside 0 to 255 cannot be written as the signature's last byte; `from_i32` rejects it
    if v < 0 || v > 255 then
      pure (expectBool "id rejected" false valid)
    else
      let sig := rs.push v.toNat.toUInt8
      pure <|
          firstError
            [expectOpt "Impl recoverKey" (Impl.recoverKey msg sig) want,
              expectOpt "Spec recoverKey" (Spec.recoverKey msg sig) want]
  | "verify" =>
    let pk ← bytes j "public"
    let msg ← bytes j "msg"
    let sig ← bytes j "sig"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl verify" (Impl.verify pk msg sig) valid,
            expectBool "Spec verify" (Spec.verify pk msg sig) valid]
  | "ecrecover" =>
    let hash ← bytes j "hash"
    let sig ← bytes j "sig"
    let v ← j.getObjValAs? Nat "v"
    let flag ← j.getObjValAs? Nat "malleability"
    let valid ← bool j "valid"
    let want ← wanted j valid "public"
    pure <|
        firstError
          [expectOpt "Impl ecrecover" (Impl.ecrecover hash sig v (flag != 0)) want,
            expectOpt "Spec ecrecover" (Spec.ecrecover hash sig v (flag != 0)) want]
  | k =>
    throw s!"unknown kind {k}"

end CryptoTests.Secp
