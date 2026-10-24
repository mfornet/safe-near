import NearCrypto
import NearRuntime.Sha256
import NodeBench.Harness

/-!
Benchmarks of `NearCrypto`. The names match `tools/node-conformance`'s `crypto-bench`, which times
the same operations with the Rust crates in release mode: SHA-256, SHA-512, Keccak-256/512 and
RIPEMD-160 over 64 B, 1 KiB and 64 KiB, Ed25519 verification of a 100-byte message and
signing. `sha256-old` is the list-based `Near.Sha256` the node used before M2. The first
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

private def sizes : List (String × Nat × Nat) :=
  [("64B", 64, 5000), ("1KiB", 1024, 500), ("64KiB", 65536, 20)]

private def hashBenchmarks (name : String) (f : ByteArray → ByteArray) (scale : Nat := 1) :
    List Benchmark :=
  sizes.map fun (label, size, iterations) =>
    let data := input size 3
    { name := s!"{name}/{label}", iterations := max 2 (iterations / scale),
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

def benchmarks : List Benchmark :=
  hashBenchmarks "sha256" sha256 ++ hashBenchmarks "sha512" sha512 ++
    hashBenchmarks "keccak256" keccak256 ++
    hashBenchmarks "keccak512" keccak512 ++
    hashBenchmarks "ripemd160" ripemd160 ++
    hashBenchmarks "sha256-old" (fun m => ⟨(Near.Sha256.hash m.toList).toArray⟩) 40 ++
    [{ name := "ed25519/verify", iterations := 300,
       run := fun i =>
         if ed25519Verify signingKey.publicKey (vary message i) signature then 1 else 0 },
      { name := "ed25519/sign", iterations := 300,
        run := fun i =>
          -- the key pair is decoded for every signature, as `near_crypto::SecretKey::sign` does;
          -- the extra byte, never present, keeps the decoding from being hoisted out of the loop
          let pair := if i == 1000000000 then keypair.push 0 else keypair
          let key := (Ed25519.Impl.SigningKey.ofKeypair pair).getD default
          (key.sign (vary message i)).get! 0 |>.toUInt64 },
      { name := "ed25519/sign-prepared", iterations := 300,
        run := fun i => (signingKey.sign (vary message i)).get! 0 |>.toUInt64 }]

end Near.Node.Bench.Crypto
