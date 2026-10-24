import NearCrypto
import CryptoTests.Fixtures

/-!
`crypto-conformance [FIXTURES_DIR]`: every hash vector and Ed25519 vector of the oracle
(`tools/node-conformance`, `crypto-fixtures`) against both the `Spec` and the `Impl` of each
primitive. A failure names the file, line and vector. The exit code is nonzero on any failure.
-/

open Lean NearCrypto CryptoTests

/-- Message of a hash vector: literal bytes, or a unit repeated `count` times. -/
def message (j : Json) : Except String ByteArray := do
  match bytes j "msg" with
  | .ok m =>
    pure m
  | .error _ =>
    let unit ← bytes j "unit"
    let count ← j.getObjValAs? Nat "count"
    pure (ByteArray.mk ((List.replicate count unit.toList).flatten.toArray))

/-- `(Spec, Impl)` of each hash by the oracle's name. -/
def hashes : List (String × ((ByteArray → ByteArray) × (ByteArray → ByteArray))) :=
  [("sha256", (Sha256.Spec.hash, Sha256.Impl.hash)),
    ("sha512", (Sha512.Spec.hash, Sha512.Impl.hash)),
    ("keccak256", (Keccak.Spec.keccak256, Keccak.Impl.keccak256)),
    ("keccak512", (Keccak.Spec.keccak512, Keccak.Impl.keccak512)),
    ("ripemd160", (Ripemd160.Spec.hash, Ripemd160.Impl.hash))]

def expect (what : String) (got want : ByteArray) : Option String :=
  if got == want then none else some s!"{what}: got {toHex got}, want {toHex want}"

def expectBool (what : String) (got want : Bool) : Option String :=
  if got == want then none else some s!"{what}: got {got}, want {want}"

def firstError (rs : List (Option String)) : Option String :=
  rs.findSome? id

def checkHash (j : Json) : Except String (Option String) := do
  let alg ← str j "alg"
  let msg ← message j
  let want ← bytes j "digest"
  match hashes.lookup alg with
  | none =>
    throw s!"unknown algorithm {alg}"
  | some (spec, impl) =>
    pure (firstError [expect s!"{alg} Impl" (impl msg) want, expect s!"{alg} Spec" (spec msg) want])

def checkEd25519 (j : Json) : Except String (Option String) := do
  let kind ← str j "kind"
  match kind with
  | "keypair" =>
    let seed ← bytes j "seed"
    let pk ← bytes j "public"
    let kp ← bytes j "keypair"
    let impl := (Ed25519.Impl.SigningKey.ofSeed seed).map (·.publicKey)
    pure <|
        firstError
          [expect "Impl publicKey" (impl.getD ByteArray.empty) pk,
            expect "Spec publicKey" (Ed25519.Spec.publicKey seed) pk,
            expect "keypair layout" (seed ++ pk) kp]
  | "keypair-check" =>
    let kp ← bytes j "keypair"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl ofKeypair" (Ed25519.Impl.SigningKey.ofKeypair kp).isSome valid,
            expectBool "Spec validKeypair" (Ed25519.Spec.validKeypair kp) valid]
  | "sign" =>
    let seed ← bytes j "seed"
    let pk ← bytes j "public"
    let msg ← bytes j "msg"
    let sig ← bytes j "sig"
    let impl := ((Ed25519.Impl.SigningKey.ofSeed seed).map (·.sign msg)).getD ByteArray.empty
    pure <|
        firstError
          [expect "Impl sign" impl sig, expect "Spec sign" (Ed25519.Spec.sign seed msg) sig,
            expectBool "Impl verify" (Ed25519.Impl.verify pk msg sig) true,
            expectBool "Spec verify" (Ed25519.Spec.verify pk msg sig) true]
  | "verify" =>
    let pk ← bytes j "public"
    let msg ← bytes j "msg"
    let sig ← bytes j "sig"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl verify" (Ed25519.Impl.verify pk msg sig) valid,
            expectBool "Spec verify" (Ed25519.Spec.verify pk msg sig) valid]
  | "pubkey" =>
    let pk ← bytes j "public"
    let valid ← bool j "valid"
    pure <|
        firstError
          [expectBool "Impl decompress" (Ed25519.Impl.validPublicKey pk) valid,
            expectBool "Spec decompress" (Ed25519.Spec.validPublicKey pk) valid]
  | _ =>
    throw s!"unknown kind {kind}"

def runFile (t : Tally) (path : System.FilePath) (check : Json → Except String (Option String)) :
    IO Tally := do
  let lines ← readJsonLines path
  let mut t := t
  let mut n := 0
  for j in lines do
    n := n + 1
    let name := (str j "name").toOption.getD "?"
    let where_ := s!"{path.fileName.getD ""}:{n} {name}"
    match check j with
    | .ok r =>
      t := t.record where_ r
    | .error e =>
      t := t.record where_ (some s!"malformed line: {e}")
  pure t

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "fixtures"
  let mut t : Tally := {}
  t ← runFile t (dir / "hash.jsonl") checkHash
  t ← runFile t (dir / "ed25519.jsonl") checkEd25519
  finish "crypto-conformance" t
