import NearCrypto
import CryptoTests.Fixtures

/-!
The vectors of `vrf.jsonl` (oracle: `near-crypto` 0.37.4 `vrf` and `key_conversion`,
`curve25519-dalek` 4.1.3) against the `Spec` and the `Impl`.
-/

namespace CryptoTests.Vrf

open Lean NearCrypto Vrf

def expect (what : String) (got want : ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {toHex got}, want {toHex want}"

def expectBool (what : String) (got want : Bool) : Option String :=
  if got == want then none else some s!"{what}: got {got}, want {want}"

def expectOpt (what : String) (got : Option ByteArray) (want : Option ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {got.map toHex}, want {want.map toHex}"

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

/-- The expected bytes of field `k`, present only on a valid line. -/
def wanted (j : Json) (valid : Bool) (k : String) : Except String (Option ByteArray) :=
  if valid then some <$> bytes j k else pure none

/-- The scalar of 32 little-endian bytes. -/
def scalar (b : ByteArray) : Nat :=
  Ed25519.Spec.toNat b

def check (j : Json) : Except String (Option String) := do
  match ← str j "kind" with
  | "ristretto" =>
    let b ← bytes j "bytes"
    let valid ← bool j "valid"
    let double ← wanted j valid "double"
    let impl := Ristretto.Impl.decompress b
    let spec := Ristretto.Spec.decompress b
    pure <|
        firstError
          [expectBool "Impl decompress" impl.isSome valid,
            expectBool "Spec decompress" spec.isSome valid,
            expectOpt "Impl recompress" (impl.map Ristretto.Impl.compress)
              (if valid then some b else none),
            expectOpt "Spec recompress" (spec.map Ristretto.Spec.compress)
              (if valid then some b else none),
            expectOpt "Impl double" (impl.map fun P => Ristretto.Impl.compress (Ed25519.Ext.dbl P))
              double,
            expectOpt "Spec double"
              (spec.map fun P => Ristretto.Spec.compress (Ed25519.Spec.add P P)) double]
  | "basemul" =>
    let s ← bytes j "scalar"
    let point ← bytes j "point"
    pure <|
        firstError
          [expect "Impl basemul" (Impl.basemul (scalar s)) point,
            expect "Spec basemul" (Spec.basemul (scalar s)) point]
  | "vmul2" =>
    let s1 ← bytes j "s1"
    let p1 ← bytes j "p1"
    let s2 ← bytes j "s2"
    let p2 ← bytes j "p2"
    let point ← bytes j "point"
    let impl :=
      match Ristretto.Impl.decompress p1, Ristretto.Impl.decompress p2 with
      | some a, some b =>
        Ristretto.Impl.compress (Ed25519.Ext.doubleMul (scalar s1) a (scalar s2) b)
      | _, _ => ByteArray.empty
    let spec :=
      match Ristretto.Spec.decompress p1, Ristretto.Spec.decompress p2 with
      | some a, some b => Spec.vmul2 (scalar s1) a (scalar s2) b
      | _, _ => ByteArray.empty
    pure (firstError [expect "Impl vmul2" impl point, expect "Spec vmul2" spec point])
  | "key" =>
    let seed ← bytes j "seed"
    let ed ← bytes j "ed25519"
    let secret ← bytes j "secret"
    let pub ← bytes j "public"
    let impl := Impl.SecretKey.ofSeed seed
    pure <|
        firstError
          [expectOpt "Impl ed25519 key" ((Ed25519.Impl.SigningKey.ofSeed seed).map (·.publicKey))
              (some ed),
            expectOpt "Impl secret" (impl.map (·.toBytes)) (some secret),
            expectOpt "Impl public" (impl.map (·.publicKey)) (some pub),
            expect "Spec secret" (Ed25519.Spec.ofNat 32 (Spec.convertSecretKey seed)) secret,
            expect "Spec public" (Spec.publicKey (Spec.convertSecretKey seed)) pub,
            expectOpt "Impl convert" (Impl.convertPublicKey ed) (some pub),
            expectOpt "Spec convert" (Spec.convertPublicKey ed) (some pub)]
  | "convert" =>
    let ed ← bytes j "ed25519"
    let valid ← bool j "valid"
    let want ← wanted j valid "public"
    pure <|
        firstError
          [expectOpt "Impl convert" (Impl.convertPublicKey ed) want,
            expectOpt "Spec convert" (Spec.convertPublicKey ed) want]
  | "compute" =>
    let secret ← bytes j "secret"
    let pub ← bytes j "public"
    let input ← bytes j "input"
    let value ← bytes j "value"
    let proof ← bytes j "proof"
    let key := Impl.SecretKey.ofBytes secret
    let (specValue, specProof) := Spec.computeWithProof (scalar secret) input
    pure <|
        firstError
          [expectOpt "Impl public" (key.map (·.publicKey)) (some pub),
            expectOpt "Impl value" (key.map (·.computeWithProof input |>.1)) (some value),
            expectOpt "Impl proof" (key.map (·.computeWithProof input |>.2)) (some proof),
            expectOpt "Impl compute" (key.map (·.compute input)) (some value),
            expect "Spec public" (Spec.publicKey (scalar secret)) pub,
            expect "Spec value" specValue value, expect "Spec proof" specProof proof,
            expectBool "Impl isValid" (Impl.isValid pub input value proof) true,
            expectBool "Spec isValid" (Spec.isValid pub input value proof) true]
  | "vrf-public" =>
    let b ← bytes j "bytes"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl decode" (Ristretto.Impl.decompress b).isSome valid,
            expectBool "Spec decode" (Ristretto.Spec.decompress b).isSome valid]
  | "vrf-secret" =>
    let b ← bytes j "bytes"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl canonical" (Impl.SecretKey.ofBytes b).isSome valid,
            expectBool "Spec canonical" (Spec.canonical b).isSome valid]
  | "verify" =>
    let pk ← bytes j "public"
    let input ← bytes j "input"
    let value ← bytes j "value"
    let proof ← bytes j "proof"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl isValid" (Impl.isValid pk input value proof) valid,
            expectBool "Spec isValid" (Spec.isValid pk input value proof) valid]
  | "block" =>
    let ed ← bytes j "ed25519"
    let prev ← bytes j "prevRandom"
    let value ← bytes j "value"
    let proof ← bytes j "proof"
    let random ← bytes j "random"
    pure <|
        firstError
          [expectBool "Impl blockVrfValid" (Impl.blockVrfValid ed prev value proof) true,
            expect "randomValue" (Impl.randomValue value) random,
            expectBool "Spec isValid"
              ((Spec.convertPublicKey ed).any fun pk => Spec.isValid pk prev value proof) true]
  | k =>
    throw s!"unknown kind {k}"

end CryptoTests.Vrf
