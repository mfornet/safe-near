import NodeBench.Harness
import NearRuntime.Sha256
import NearNode.Primitives

/-!
`node-bench [--filter SUBSTRING] [--out FILE]`: run the node benchmarks and
print (or write) their JSON report. Baselines for M2 start from the existing
`Near.Sha256.hash`; the Borsh benchmarks encode and decode a `SignedTransaction` with eight
actions.
-/

open Near.Node.Bench

def input (size seed : Nat) : List UInt8 :=
  (List.range size).map fun i => UInt8.ofNat (i * 31 + seed)

def sha256 (size iterations : Nat) : Benchmark :=
  { name := s!"sha256/{size}B", iterations,
    run := fun i => ((Near.Sha256.hash (input size i)).foldl (fun a b => a * 31 + b.toUInt64) 0) }

open Near.Node Near.Node.Borsh

def bytesOf (n seed : Nat) : ByteArray :=
  ⟨(input n seed).toArray⟩

def account (s : String) : AccountId :=
  ⟨s⟩

def sampleKey (seed : Nat) : PublicKey :=
  .ed25519 (bytesOf 32 seed)

/-- A transaction of every common shape: calls, transfers, key changes and a contract. -/
def sampleTx (nonce : Nat) : SignedTransaction :=
  .mk
    (.v0
      { signerId := account "alice.near", publicKey := sampleKey 1, nonce := nonce.toUInt64,
        receiverId := account "bob.near", blockHash := ⟨bytesOf 32 2⟩,
        actions :=
          #[.base (.functionCall ⟨"ft_transfer", bytesOf 128 3, 30000000000000, ⟨1⟩⟩),
            .base (.transfer ⟨⟨10 ^ 24⟩⟩),
            .base
              (.addKey
                ⟨sampleKey 4,
                  ⟨0, .functionCall ⟨some ⟨10 ^ 25⟩, "app.near", #["get", "set", "remove"]⟩⟩⟩),
            .base (.stake ⟨⟨10 ^ 27⟩, sampleKey 5⟩), .base (.deleteKey ⟨sampleKey 6⟩),
            .base (.deployContract ⟨bytesOf 2048 7⟩),
            .base (.functionCall ⟨"on_callback", bytesOf 512 8, 5000000000000, ⟨0⟩⟩),
            .base (.deleteAccount ⟨account "carol.near"⟩)] })
    (.ed25519 (bytesOf 64 9 |>.set! 63 0))

@[never_extract, noinline]
def decodeTx (d : ByteArray) : Except Error SignedTransaction :=
  Codec.decodeAll d

def sampleBytes : ByteArray :=
  Codec.encode (sampleTx 7)

def nonceOf : Except Error SignedTransaction → UInt64
  | .ok ⟨.v0 t, _⟩ => t.nonce
  | _ => 0

def benchmarks : List Benchmark :=
  [sha256 64 2000, sha256 1024 200, sha256 65536 4,
    { name := s!"borsh/encode SignedTransaction ({sampleBytes.size}B)", iterations := 20000,
      run := fun i => (Codec.encode (sampleTx i)).size.toUInt64 },
    { name := "borsh/decode SignedTransaction", iterations := 20000,
      run := fun _ => nonceOf (decodeTx sampleBytes) },
    { name := "borsh/spec encode SignedTransaction", iterations := 2000,
      run := fun i => (Codec.encodeSpec (sampleTx i)).length.toUInt64 },
    { name := "borsh/spec decode SignedTransaction", iterations := 2000,
      run := fun _ => nonceOf (Codec.decodeAllSpec sampleBytes.toList) }]

structure Options where
  filter : String := ""
  out : Option System.FilePath := none

def parse : Options → List String → Except String Options
  | o, [] => .ok o
  | o, "--filter" :: f :: rest => parse { o with filter := f } rest
  | o, "--out" :: f :: rest => parse { o with out := some f } rest
  | _, arg :: _ => .error s!"unknown argument: {arg}"

def main (args : List String) : IO UInt32 := do
  match parse {} args with
  | .error e =>
    IO.eprintln s!"{e}\nusage: node-bench [--filter SUBSTRING] [--out FILE]"
    return 2
  | .ok o =>
    let selected :=
      benchmarks.filter fun b => (b.name.splitOn o.filter).length > 1 || o.filter.isEmpty
    let mut results := #[]
    for b in selected do
      let r ← measure b
      IO.eprintln s!"{r.name}: {r.nanosPerIteration} ns/iter"
      results := results.push r
    let json := (report results).pretty
    match o.out with
    | some path =>
      IO.FS.writeFile path (json ++ "\n")
    | none =>
      IO.println json
    return 0
