import NearCrypto
import NearRuntime.Sha256
import NodeBench.Harness

/-!
Benchmarks of `NearCrypto`. The names match `tools/node-conformance`'s `crypto-bench`, which times
the same operations with the Rust crates in release mode: SHA-256, SHA-512, Keccak-256/512 and
RIPEMD-160 and BLAKE2b-256/512 over 64 B, 1 KiB and 64 KiB, Ed25519 verification of a 100-byte
message and signing, secp256k1 recovery, verification and signing of a 32-byte message, and the
VRF (`compute_vrf_with_proof` and `is_vrf_valid`) of a 32-byte input. `sha256-old` is the list-based `Near.Sha256` the node used before M2. The first
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

def benchmarks : List Benchmark :=
  hashBenchmarks "sha256" sha256 ++ hashBenchmarks "sha512" sha512 ++
    hashBenchmarks "keccak256" keccak256 ++
    hashBenchmarks "keccak512" keccak512 ++
    hashBenchmarks "ripemd160" ripemd160 ++
    hashBenchmarks "blake2b256" blake2b256 ++
    hashBenchmarks "blake2b512" blake2b512 ++
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
      { name := "vrf/compute-with-proof", iterations := 400,
        run := fun i => (vrfKey.computeWithProof (vary vrfInput i)).1.get! 3 |>.toUInt64 },
      { name := "vrf/verify", iterations := 400,
        run := fun i =>
          if Vrf.Impl.isValid vrfKey.publicKey (vary vrfInput i) vrfProof.1 vrfProof.2 then 1
          else 0 }]

end Near.Node.Bench.Crypto
