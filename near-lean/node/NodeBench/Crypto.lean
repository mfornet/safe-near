import NearCrypto
import NearRuntime.Sha256
import NodeBench.Harness

/-!
Benchmarks of `NearCrypto`. The names match `tools/node-conformance`'s `crypto-bench`, which times
the same operations with the Rust crates in release mode: SHA-256, SHA-512, Keccak-256/512 and
RIPEMD-160 and BLAKE2b-256/512 over 64 B, 1 KiB and 64 KiB, Ed25519 verification of a 100-byte
message and signing, secp256k1 recovery, verification and signing of a 32-byte message, and the
VRF (`compute_vrf_with_proof` and `is_vrf_valid`) of a 32-byte input, SHAKE256 of 1 KiB, and ML-DSA-65:
key generation from a seed, signing of a 100-byte message with the key decoded and checked for every
signature (`near_crypto::SecretKey::sign`) and with it prepared, and verification. `sha256-old` is the list-based `Near.Sha256` the node used before M2. The first
byte of the message varies with the iteration, so no call is a repeat; verification then fails at
the final comparison, after all the arithmetic of a valid one.
-/

namespace Near.Node.Bench.Crypto

open NearCrypto Near.Node.Bench

private def input (size seed : Nat) : ByteArray :=
  ⟨((List.range size).map fun i => UInt8.ofNat (i * 31 + seed)).toArray⟩

/-- A copy of `m` whose first byte is `i`. -/
private def vary (m : ByteArray) (i : Nat) : ByteArray :=
  m.set! 0 (UInt8.ofNat i)

/-- Label, size and iteration counts of a fast and of a slow hash. -/
private def sizes : List (String × Nat × Nat × Nat) :=
  [("64B", 64, 100000, 20000), ("1KiB", 1024, 20000, 2000), ("64KiB", 65536, 800, 80)]

private def hashBenchmarks (name : String) (f : ByteArray → ByteArray) (slow : Bool := false) :
    List Benchmark :=
  sizes.map fun (label, size, fast, slowIterations) =>
    let data := input size 3
    { name := s!"{name}/{label}", iterations := if slow then slowIterations else fast,
      run := fun i => (f (vary data i)).get! 0 |>.toUInt64 }

private def seed : ByteArray :=
  ⟨(List.range 32).toArray.map fun _ => 7⟩

private def keypair : ByteArray :=
  seed ++ ((Ed25519.Impl.SigningKey.ofSeed seed).map (·.publicKey)).getD ByteArray.empty

private def message : ByteArray :=
  input 100 5

private def signingKey : Ed25519.Impl.SigningKey :=
  (Ed25519.Impl.SigningKey.ofKeypair keypair).getD default

private def signature : ByteArray :=
  signingKey.sign message

private def secpSecret : ByteArray :=
  ⟨(List.range 32).toArray.map fun _ => 7⟩

private def secpMessage : ByteArray :=
  input 32 5

private def secpPublic : ByteArray :=
  (Secp256k1.Impl.publicKey secpSecret).getD ByteArray.empty

private def secpSignature : ByteArray :=
  (Secp256k1.Impl.signRecoverable secpSecret secpMessage).getD ByteArray.empty

private def vrfKey : Vrf.Impl.SecretKey :=
  (Vrf.Impl.SecretKey.ofSeed seed).getD ⟨0, ByteArray.empty⟩

private def vrfInput : ByteArray :=
  input 32 9

private def vrfProof : ByteArray × ByteArray :=
  vrfKey.computeWithProof vrfInput

private def shakeData : ByteArray :=
  input 1024 3

private def mldsaSeed : ByteArray :=
  ⟨(List.range 32).toArray.map fun i => UInt8.ofNat (i * 7 + 1)⟩

private def mldsaKeys : ByteArray × ByteArray :=
  MlDsa.Impl.keyGen mldsaSeed

private def mldsaMessage : ByteArray :=
  input 100 5

private def mldsaRnd : ByteArray :=
  input 32 11

private def mldsaSignature : ByteArray :=
  (MlDsa.Impl.sign mldsaKeys.2 mldsaMessage mldsaRnd).getD ByteArray.empty

/-! ### Pairing-friendly curves and P-256

Inputs of the sizes `crypto-bench curves` uses (two pairs, eight points), built from pseudo-random
scalars; each iteration changes a byte that keeps the input valid (a sign, a scalar, the order of
the pairs, a flag), so none is a repeat. -/

section Curves

open NearCrypto.Pairing

/-- A pseudo-random number below `m`. -/
private def scalar (m i : Nat) : Nat :=
  Pairing.beNat (Sha256.Impl.hash (Pairing.toBe i 8)) 0 32 % m

private def mulPt {α : Type} (F : Fld α) (g : Option (α × α)) (k : Nat) : Option (α × α) :=
  Jac.toAffine F (Jac.mul F (Jac.ofAffine F g) k)

private def negPt {α : Type} (F : Fld α) (g : Option (α × α)) : Option (α × α) :=
  Jac.toAffine F (Jac.neg F (Jac.ofAffine F g))

/-- Swap the two halves of an input of two items of `n` bytes. -/
private def swapItems (m : ByteArray) (n i : Nat) : ByteArray :=
  if i % 2 == 1 then m.extract n m.size ++ m.extract 0 n else m

private def bnG1 (i : Nat) : Bn254.G1 :=
  mulPt Bn254.Spec.f1 Bn254.g1Gen (scalar Bn254.r i)

private def bnPairing : ByteArray :=
  let a := scalar Bn254.r 1
  Bn254.encodeG1 (mulPt Bn254.Spec.f1 Bn254.g1Gen a) ++ Bn254.encodeG2 Bn254.g2Gen ++
    Bn254.encodeG1 (negPt Bn254.Spec.f1 Bn254.g1Gen) ++
    Bn254.encodeG2 (mulPt Bn254.Spec.f2 Bn254.g2Gen a)

private def bnSingle : ByteArray :=
  Bn254.encodeG1 (bnG1 2) ++ Bn254.encodeG2 (mulPt Bn254.Spec.f2 Bn254.g2Gen (scalar Bn254.r 3))

private def bnMultiexp (n : Nat) : ByteArray :=
  (List.range n).foldl
    (fun acc i => acc ++ Bn254.encodeG1 (bnG1 i) ++ Pairing.toLe (scalar Bn254.r (i + 50)) 32)
    ByteArray.empty

private def bnSum : ByteArray :=
  (List.range 8).foldl
    (fun acc i => acc ++ ByteArray.mk #[(i % 2).toUInt8] ++ Bn254.encodeG1 (bnG1 i)) ByteArray.empty

private def blsG1 (i : Nat) : Bls12381.G1 :=
  mulPt Bls12381.f1 Bls12381.g1Gen (scalar Bls12381.r i)

private def blsG2 (i : Nat) : Bls12381.G2 :=
  mulPt Bls12381.f2 Bls12381.g2Gen (scalar Bls12381.r i)

private def blsPairing : ByteArray :=
  let a := scalar Bls12381.r 1
  Bls12381.serializeG1 (mulPt Bls12381.f1 Bls12381.g1Gen a) ++
    Bls12381.serializeG2 Bls12381.g2Gen ++
    Bls12381.serializeG1 (negPt Bls12381.f1 Bls12381.g1Gen) ++
    Bls12381.serializeG2 (mulPt Bls12381.f2 Bls12381.g2Gen a)

private def blsSingle : ByteArray :=
  Bls12381.serializeG1 (blsG1 2) ++ Bls12381.serializeG2 (blsG2 3)

private def blsSum1 : ByteArray :=
  (List.range 8).foldl
    (fun acc i => acc ++ ByteArray.mk #[(i % 2).toUInt8] ++ Bls12381.serializeG1 (blsG1 i))
    ByteArray.empty

private def blsSum2 : ByteArray :=
  (List.range 8).foldl
    (fun acc i => acc ++ ByteArray.mk #[(i % 2).toUInt8] ++ Bls12381.serializeG2 (blsG2 i))
    ByteArray.empty

private def blsMultiexp1 (n : Nat) : ByteArray :=
  (List.range n).foldl
    (fun acc i =>
      acc ++ Bls12381.serializeG1 (blsG1 i) ++ Pairing.toLe (scalar (2 ^ 256) (i + 50)) 32)
    ByteArray.empty

private def blsMultiexp2 (n : Nat) : ByteArray :=
  (List.range n).foldl
    (fun acc i =>
      acc ++ Bls12381.serializeG2 (blsG2 i) ++ Pairing.toLe (scalar (2 ^ 256) (i + 50)) 32)
    ByteArray.empty

private def blsFp : ByteArray :=
  Pairing.toBe (scalar Bls12381.p 5) 48

private def blsFp2 : ByteArray :=
  Pairing.toBe (scalar Bls12381.p 6) 48 ++ Pairing.toBe (scalar Bls12381.p 7) 48

/-- The first byte of a compressed point with the sign flag toggled by `i`. -/
private def flip (m : ByteArray) (i : Nat) : ByteArray :=
  m.set! 0 ((m.get! 0 &&& 0xdf) ||| (UInt8.ofNat (i % 2) <<< (5 : UInt8)))

private def bnResult : Except String ByteArray → UInt64
  | .ok b => b.get! 3 |>.toUInt64
  | .error _ => 2

private def blsResult : Except String (Option ByteArray) → UInt64
  | .ok (some b) => b.get! 5 |>.toUInt64
  | .ok none => 1
  | .error _ => 2

private def p256Secret : Nat :=
  scalar P256.n 9

private def p256Key : ByteArray :=
  match P256.Impl.mulAdd p256Secret (P256.gx, P256.gy) 0 with
  | some (x, y) => ByteArray.mk #[if y % 2 == 1 then 3 else 2] ++ Pairing.toBe x 32
  | none => ByteArray.empty

private def p256Digest : ByteArray :=
  input 32 5

private def p256Signature : ByteArray :=
  let k := scalar P256.n 10
  match P256.Impl.mulAdd k (P256.gx, P256.gy) 0 with
  | some (x, _) =>
    let r := x % P256.n
    let z := Pairing.beNat p256Digest 0 32 % P256.n
    let s := Pairing.invMod P256.n k * ((z + r * p256Secret) % P256.n) % P256.n
    Pairing.toBe r 32 ++ Pairing.toBe s 32
  | none => ByteArray.empty

def curveBenchmarks : List Benchmark :=
  [{ name := "bn254/pairing-1", iterations := 40,
     run := fun i =>
       match Bn254.pairingCheck Bn254.Impl.ops (swapItems bnSingle 192 (i + 2)) with
       | .ok b => if b then 1 else 0
       | .error _ => 2 },
    { name := "bn254/pairing-2", iterations := 40,
      run := fun i =>
        match Bn254.pairingCheck Bn254.Impl.ops (swapItems bnPairing 192 i) with
        | .ok b => if b then 1 else 0
        | .error _ => 2 },
    { name := "bn254/g1-multiexp-1", iterations := 200,
      run := fun i =>
        bnResult (Bn254.g1Multiexp Bn254.Impl.ops ((bnMultiexp 1).set! 64 (UInt8.ofNat (i % 7)))) },
    { name := "bn254/g1-multiexp-8", iterations := 100,
      run := fun i =>
        bnResult (Bn254.g1Multiexp Bn254.Impl.ops ((bnMultiexp 8).set! 64 (UInt8.ofNat (i % 7)))) },
    { name := "bn254/g1-sum-8", iterations := 1000,
      run := fun i => bnResult (Bn254.g1Sum Bn254.Impl.ops (bnSum.set! 0 (UInt8.ofNat (i % 2)))) },
    { name := "bls12381/pairing-1", iterations := 40,
      run := fun i =>
        match Bls12381.pairingCheck Bls12381.Impl.ops (swapItems blsSingle 288 (i + 2)) with
        | .ok c => c.toUInt64
        | .error _ => 9 },
    { name := "bls12381/pairing-2", iterations := 40,
      run := fun i =>
        match Bls12381.pairingCheck Bls12381.Impl.ops (swapItems blsPairing 288 i) with
        | .ok c => c.toUInt64
        | .error _ => 9 },
    { name := "bls12381/p1-sum-8", iterations := 1000,
      run := fun i =>
        blsResult (Bls12381.p1Sum Bls12381.Impl.ops 0 (blsSum1.set! 0 (UInt8.ofNat (i % 2)))) },
    { name := "bls12381/p2-sum-8", iterations := 500,
      run := fun i =>
        blsResult (Bls12381.p2Sum Bls12381.Impl.ops 0 (blsSum2.set! 0 (UInt8.ofNat (i % 2)))) },
    { name := "bls12381/g1-multiexp-1", iterations := 100,
      run := fun i =>
        blsResult
          (Bls12381.g1Multiexp Bls12381.Impl.ops 0
            ((blsMultiexp1 1).set! 96 (UInt8.ofNat (i % 7)))) },
    { name := "bls12381/g1-multiexp-8", iterations := 20,
      run := fun i =>
        blsResult
          (Bls12381.g1Multiexp Bls12381.Impl.ops 0
            ((blsMultiexp1 8).set! 96 (UInt8.ofNat (i % 7)))) },
    { name := "bls12381/g2-multiexp-1", iterations := 40,
      run := fun i =>
        blsResult
          (Bls12381.g2Multiexp Bls12381.Impl.ops 0
            ((blsMultiexp2 1).set! 192 (UInt8.ofNat (i % 7)))) },
    { name := "bls12381/g2-multiexp-8", iterations := 10,
      run := fun i =>
        blsResult
          (Bls12381.g2Multiexp Bls12381.Impl.ops 0
            ((blsMultiexp2 8).set! 192 (UInt8.ofNat (i % 7)))) },
    { name := "bls12381/map-fp-to-g1", iterations := 200,
      run := fun i =>
        blsResult (Bls12381.mapFpToG1 Bls12381.Impl.ops (blsFp.set! 47 (UInt8.ofNat i))) },
    { name := "bls12381/map-fp2-to-g2", iterations := 60,
      run := fun i =>
        blsResult (Bls12381.mapFp2ToG2 Bls12381.Impl.ops (blsFp2.set! 95 (UInt8.ofNat i))) },
    { name := "bls12381/p1-decompress", iterations := 500,
      run := fun i =>
        blsResult
          (Bls12381.p1Decompress Bls12381.Impl.ops 0 (flip (Bls12381.compressG1 (blsG1 4)) i)) },
    { name := "bls12381/p2-decompress", iterations := 200,
      run := fun i =>
        blsResult
          (Bls12381.p2Decompress Bls12381.Impl.ops 0 (flip (Bls12381.compressG2 (blsG2 4)) i)) },
    { name := "p256/verify-32B", iterations := 400,
      run := fun i =>
        match P256.Impl.verify p256Signature (p256Digest.set! 31 (UInt8.ofNat (i % 2))) p256Key with
        | .ok b => if b then 1 else 0
        | .error _ => 2 }]

end Curves

def benchmarks : List Benchmark :=
  curveBenchmarks ++ hashBenchmarks "sha256" sha256 ++ hashBenchmarks "sha512" sha512 ++
    hashBenchmarks "keccak256" keccak256 ++
    hashBenchmarks "keccak512" keccak512 ++
    hashBenchmarks "ripemd160" ripemd160 ++
    hashBenchmarks "blake2b256" blake2b256 ++
    hashBenchmarks "blake2b512" blake2b512 ++
    [{ name := "shake256/1KiB", iterations := 20000,
       run := fun i => (shake256 (vary shakeData i) 32).get! 0 |>.toUInt64 }] ++
    hashBenchmarks "sha256-old" (fun m => ⟨(Near.Sha256.hash m.toList).toArray⟩) true ++
    [{ name := "ed25519/verify", iterations := 1500,
       run := fun i =>
         if ed25519Verify signingKey.publicKey (vary message i) signature then 1 else 0 },
      { name := "ed25519/sign", iterations := 1000,
        run := fun i =>
          -- the key pair is decoded for every signature, as `near_crypto::SecretKey::sign` does;
          -- the extra byte, never present, keeps the decoding from being hoisted out of the loop
          let pair := if i == 1000000000 then keypair.push 0 else keypair
          let key := (Ed25519.Impl.SigningKey.ofKeypair pair).getD default
          (key.sign (vary message i)).get! 0 |>.toUInt64 },
      { name := "ed25519/sign-prepared", iterations := 2000,
        run := fun i => (signingKey.sign (vary message i)).get! 0 |>.toUInt64 },
      { name := "secp256k1/recover", iterations := 1500,
        run := fun i =>
          ((Secp256k1.Impl.recoverKey (vary secpMessage i) secpSignature).getD ByteArray.empty).get!
              5 |>.toUInt64 },
      { name := "secp256k1/verify", iterations := 1500,
        run := fun i =>
          if secp256k1Verify secpPublic (vary secpMessage i) secpSignature then 1 else 0 },
      { name := "secp256k1/sign", iterations := 1500,
        run := fun i =>
          ((Secp256k1.Impl.signRecoverable secpSecret (vary secpMessage i)).getD
                  ByteArray.empty).get!
              5 |>.toUInt64 },
      { name := "mldsa65/keygen", iterations := 300,
        run := fun i => (MlDsa.Impl.keyGen (vary mldsaSeed i)).1.get! 40 |>.toUInt64 },
      { name := "mldsa65/sign", iterations := 300,
        run := fun i =>
          ((MlDsa.Impl.sign mldsaKeys.2 (vary mldsaMessage i) mldsaRnd).getD ByteArray.empty).get!
              100 |>.toUInt64 },
      { name := "mldsa65/sign-prepared", iterations := 300,
        run := fun i =>
          ((MlDsa.Impl.signInternal mldsaKeys.2 (MlDsa.Impl.pure' (vary mldsaMessage i))
                      mldsaRnd).getD
                  ByteArray.empty).get!
              100 |>.toUInt64 },
      { name := "mldsa65/verify", iterations := 500,
        run := fun i =>
          if MlDsa.Impl.verify mldsaKeys.1 (vary mldsaMessage i) mldsaSignature then 1 else 0 },
      { name := "vrf/compute-with-proof", iterations := 400,
        run := fun i => (vrfKey.computeWithProof (vary vrfInput i)).1.get! 3 |>.toUInt64 },
      { name := "vrf/verify", iterations := 400,
        run := fun i =>
          if Vrf.Impl.isValid vrfKey.publicKey (vary vrfInput i) vrfProof.1 vrfProof.2 then 1
          else 0 }]

end Near.Node.Bench.Crypto
