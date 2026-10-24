import NodeBench.Harness
import NearRuntime.Sha256
import NearNode.Primitives

/-!
`node-bench [--filter SUBSTRING] [--out FILE]`: run the node benchmarks and
print (or write) their JSON report. Baselines for M2 start from the existing
`Near.Sha256.hash`; the Borsh benchmarks encode and decode a `SignedTransaction` with eight
actions; the block benchmarks a four-chunk block with 80 approvals; the epoch benchmarks a chunk
state witness of about 400 KB and the sampling of producers and chunk validators.
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

def txBenchmarks : List Benchmark :=
  [sha256 64 2000, sha256 1024 200, sha256 65536 4,
    { name := s!"borsh/encode SignedTransaction ({sampleBytes.size}B)", iterations := 20000,
      run := fun i => (Codec.encode (sampleTx i)).size.toUInt64 },
    { name := "borsh/decode SignedTransaction", iterations := 20000,
      run := fun _ => nonceOf (decodeTx sampleBytes) },
    { name := "borsh/spec encode SignedTransaction", iterations := 2000,
      run := fun i => (Codec.encodeSpec (sampleTx i)).length.toUInt64 },
    { name := "borsh/spec decode SignedTransaction", iterations := 2000,
      run := fun _ => nonceOf (Codec.decodeAllSpec sampleBytes.toList) }]

def sampleHash (seed : Nat) : CryptoHash :=
  ⟨bytesOf 32 seed⟩

def sampleSig (seed : Nat) : Signature :=
  .ed25519 (bytesOf 64 seed |>.set! 63 0)

def sampleChunk (shard : Nat) : ShardChunkHeader :=
  .v3
    {
      inner :=
        .v4
          { prevBlockHash := sampleHash 1, prevStateRoot := sampleHash 2,
            prevOutcomeRoot := sampleHash 3, encodedMerkleRoot := sampleHash 4,
            encodedLength := 90000, heightCreated := 1000, shardId := shard.toUInt64,
            prevGasUsed := 100000000000000, gasLimit := 1000000000000000,
            prevBalanceBurnt := ⟨10 ^ 22⟩, prevOutgoingReceiptsRoot := sampleHash 5,
            txRoot := sampleHash 6,
            prevValidatorProposals := #[⟨account "v.near", sampleKey 7, ⟨10 ^ 26⟩⟩],
            congestionInfo := .v1 ⟨⟨5⟩, ⟨6⟩, 7, 8⟩,
            bandwidthRequests := .v1 ⟨#[⟨1, ⟨bytesOf 5 3⟩⟩, ⟨2, ⟨bytesOf 5 4⟩⟩]⟩ },
      heightIncluded := 1001, signature := sampleSig 8 }

/-- A block of four chunks and 80 approvals, as a mainnet block of the current protocol. -/
def sampleBlock : Block :=
  let chunks := (List.range 4).toArray.map sampleChunk
  .v4 {
      header :=
        .v6 {
            prevHash := sampleHash 9
            innerLite :=
              { height := 1001, epochId := ⟨sampleHash 10⟩, nextEpochId := ⟨sampleHash 11⟩,
                prevStateRoot := sampleHash 12, prevOutcomeRoot := sampleHash 13,
                timestamp := 1700000000000000000, nextBpHash := sampleHash 14,
                blockMerkleRoot := sampleHash 15 }
            innerRest :=
              { blockBodyHash := sampleHash 16, prevChunkOutgoingReceiptsRoot := sampleHash 17,
                chunkHeadersRoot := sampleHash 18, chunkTxRoot := sampleHash 19,
                randomValue := sampleHash 20, prevValidatorProposals := #[],
                chunkMask := #[true, true, true, false], nextGasPrice := ⟨10 ^ 8⟩,
                totalSupply := ⟨10 ^ 33⟩, lastFinalBlock := sampleHash 21,
                lastDsFinalBlock := sampleHash 22, blockOrdinal := 5000, prevHeight := 1000,
                epochSyncDataHash := none,
                approvals := (List.range 80).toArray.map fun i => some (sampleSig i),
                latestProtocolVersion := 86,
                chunkEndorsements := ⟨(List.range 4).toArray.map fun i => bytesOf 8 i⟩,
                shardSplit := none }
            signature := sampleSig 23 }
      body :=
        .v2
          { chunks, challenges := #[], vrfValue := ⟨bytesOf 32 24⟩, vrfProof := ⟨bytesOf 64 25⟩,
            chunkEndorsements :=
              (List.range 4).toArray.map fun _ =>
                (List.range 40).toArray.map fun i => some (sampleSig i) } }

def blockBytes : ByteArray :=
  Codec.encode sampleBlock

@[never_extract, noinline]
def decodeBlock (d : ByteArray) : Except Error Block :=
  Codec.decodeAll d

def blockHeight : Except Error Block → UInt64
  | .ok b => b.header.height
  | _ => 0

/-- The sample header with a timestamp that depends on the iteration, so nothing is shared. -/
@[never_extract, noinline]
def headerAt (i : Nat) : BlockHeader :=
  match sampleBlock.header with
  | .v6 h => .v6 { h with innerLite := { h.innerLite with timestamp := i.toUInt64 } }
  | h => h

@[never_extract, noinline]
def blockAt (i : Nat) : Block :=
  match sampleBlock with
  | .v4 b => .v4 { b with header := headerAt i }
  | b => b

def chainBenchmarks : List Benchmark :=
  [{ name := s!"borsh/encode Block ({blockBytes.size}B)", iterations := 2000,
     run := fun i => (Codec.encode (if i % 2 == 0 then sampleBlock else default)).size.toUInt64 },
    { name := "borsh/decode Block", iterations := 2000,
      run := fun _ => blockHeight (decodeBlock blockBytes) },
    { name := "block/hash (BlockHeader.hash)", iterations := 2000,
      run := fun i => (headerAt i).hash.bytes[0]!.toUInt64 },
    { name := "block/chunk roots and validity", iterations := 500,
      run := fun i => (BlockValidityError.code (blockAt i).checkValidity).toUInt64 }]

/-- A trie value of 200 bytes. -/
def trieValue (i : Nat) : ByteArray :=
  bytesOf 200 i

/-- A state transition over `n` trie values. -/
def sampleTransition (n : Nat) : ChunkStateTransition :=
  { blockHash := sampleHash 30, baseState := .trieValues ((List.range n).toArray.map trieValue),
    postStateRoot := sampleHash 31 }

/-- A chunk state witness of about 400 KB: a main transition of 1500 trie values, two implicit
transitions, receipt proofs from four shards and eight transactions. -/
def sampleWitness : ChunkStateWitness :=
  .v2
    { epochId := ⟨sampleHash 32⟩, chunkHeader := sampleChunk 1,
      mainStateTransition := sampleTransition 1500,
      sourceReceiptProofs :=
        ⟨(List.range 4).toArray.map fun i =>
            (⟨sampleHash (40 + i)⟩,
              ⟨#[], ⟨i.toUInt64, 1, #[⟨sampleHash 50, .left⟩, ⟨sampleHash 51, .right⟩]⟩⟩)⟩,
      appliedReceiptsHash := sampleHash 33, transactions := (List.range 8).toArray.map sampleTx,
      implicitTransitions := #[sampleTransition 40, sampleTransition 40], newTransactions := #[] }

def witnessBytes : ByteArray :=
  Codec.encode sampleWitness

@[never_extract, noinline]
def decodeWitness (d : ByteArray) : Except Error ChunkStateWitness :=
  Codec.decodeAll d

def witnessTxs : Except Error ChunkStateWitness → UInt64
  | .ok (.v2 w) => w.transactions.size.toUInt64
  | _ => 0

/-- An epoch of 100 validators with stakes between 10^24 and 10^26, 100 block producer seats and
four shards of 60 chunk producers, with 400 mandates per shard. -/
def sampleEpoch : EpochInfo :=
  let validators : Array ValidatorStake :=
    (Array.range 100).map fun i =>
      .v1 ⟨account s!"validator{i}.near", sampleKey i, ⟨10 ^ 24 * (1 + i * i % 97)⟩⟩
  let stakeOf (ids : Array UInt64) : Array Balance :=
    ids.map fun id =>
      match validators[id.toNat]! with
      | .v1 v => v.stake
  let bps := (Array.range 100).map Nat.toUInt64
  let cps : Array (Array UInt64) :=
    (Array.range 4).map fun s => (Array.range 60).map fun i => ((s * 17 + i) % 100).toUInt64
  let index (ids : Array UInt64) : StakeWeightedIndex :=
    (StakeWeightedIndex.new (stakeOf ids)).getD default
  let mandates := (ValidatorMandates.new ⟨400, 4⟩ validators).getD default
  .v5
    { epochHeight := 7, validators, validatorToIndex := ⟨#[]⟩, blockProducersSettlement := bps,
      chunkProducersSettlement := cps, stakeChange := ⟨#[]⟩, validatorReward := ⟨#[]⟩,
      validatorKickout := ⟨#[]⟩, mintedAmount := 0, seatPrice := 1, protocolVersion := 86,
      shardLayout := .v0 ⟨4, 0⟩, lastResharding := none, rngSeed := ⟨bytesOf 32 99⟩,
      blockProducersSampler := index bps, chunkProducersSampler := cps.map index,
      validatorMandates := mandates }

def epochBenchmarks : List Benchmark :=
  [{ name := s!"borsh/encode ChunkStateWitness ({witnessBytes.size}B)", iterations := 50,
     run := fun i => (Codec.encode (if i % 2 == 0 then sampleWitness else default)).size.toUInt64 },
    { name := "borsh/decode ChunkStateWitness", iterations := 200,
      run := fun _ => witnessTxs (decodeWitness witnessBytes) },
    { name := "epoch/sample_block_producer (100 seats)", iterations := 20000,
      run := fun i => (sampleEpoch.sampleBlockProducer i.toUInt64).getD 0 },
    { name := "epoch/sample_chunk_producer (60 per shard)", iterations := 20000,
      run := fun i =>
        (sampleEpoch.sampleChunkProducer (.v0 ⟨4, 0⟩) (i % 4).toUInt64 i.toUInt64).getD 0 },
    { name := "epoch/sample_chunk_validators (4 x 400 mandates)", iterations := 20,
      run := fun i =>
        ((sampleEpoch.sampleChunkValidators i.toUInt64).map (·.size.toUInt64)).getD 0 }]

def benchmarks : List Benchmark :=
  txBenchmarks ++ chainBenchmarks ++ epochBenchmarks

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
