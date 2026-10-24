import NodeConformance.Runner
import NearNode.Primitives

/-!
The M1c part of the registry of `node-conformance-types` for epochs: shard layouts, `EpochInfo`
with its samplers and mandates, block info and epoch sync proofs. The producers are sampled at the
heights of `sampleHeights`; where nearcore panics the oracle records no value, and so does the
`Option` of the Lean function.
-/

open Near.Node Near.Node.Conformance Near.Node.Borsh

/-- The heights at which producers are sampled. -/
def sampleHeights : Array UInt64 :=
  (Array.range 16).map Nat.toUInt64 ++
    #[100, 255, 256, 1000, 65535, 65536, 12345678, 4294967295, 4294967296, 1099511627783,
      9223372036854775807, 9223372036854775808, 18446744073709551614, 18446744073709551615] ++
    (Array.range 16).map fun i => (37 * (i + 16) * (i + 16) + (i + 16)).toUInt64

/-- The heights at which chunk validators are sampled. -/
def validatorHeights : Array UInt64 :=
  (Array.range sampleHeights.size).filterMap fun i => if i % 7 == 0 then sampleHeights[i]? else none

private def account (s : String) : AccountId :=
  ⟨s⟩

private def probeAccounts : Array AccountId :=
  #["a.near", "alice.near", "test1", "test2", "zzzzzzzz.near", "00"].map account

private def layoutFields (l : ShardLayout) : List (String × ByteArray) :=
  let ids : Array (Option UInt64) := (Array.range 8).map fun i => l.getShardId i
  let indexes : Array (Option UInt64) :=
    ((Array.range 8).map Nat.toUInt64 ++ #[1000, 2000, 18446744073709551615]).map fun s =>
      (l.getShardIndex s).map Nat.toUInt64
  let boundaries : Array AccountId :=
    match l with
    | .v0 _ => #[]
    | .v1 l => l.boundaryAccounts
    | .v2 l => l.boundaryAccounts
    | .v3 l => l.boundaryAccounts
  let shards : Array (Option UInt64) := (probeAccounts ++ boundaries).map l.accountIdToShardId
  [("version", Codec.encode l.version), ("numShards", Codec.encode l.numShards),
    ("shardIndexes", Codec.encode indexes), ("shardIds", Codec.encode ids),
    ("accountShards", Codec.encode shards)]

/-- `StakeWeightedIndex::new`, or nothing where nearcore overflows. -/
private def builtIndex (stakes : Array Balance) : ByteArray :=
  match StakeWeightedIndex.new stakes with
  | some i => Codec.encode i
  | none => ByteArray.empty

private def samplerSamples (s : StakeWeightedIndex) : ByteArray :=
  let seeds := (Array.range 40).map fun i => (CryptoHash.hash (Codec.encode i.toUInt32)).bytes
  match seeds.mapM s.sample with
  | some xs => xs.foldl (fun b x => b ++ Codec.encode x.toUInt64) ByteArray.empty
  | none => ByteArray.empty

/-- `ValidatorMandates::new` over a config and validators. Decoding rejects the configs that the
oracle's type rejects: no shards, more than 64 shards, a target above 1000. -/
structure MandatesInput where
  target : UInt64
  numShards : UInt64
  validators : Array ValidatorStake

instance : Codec MandatesInput :=
  .tryIso (UInt64 × UInt64 × Array ValidatorStake)
    (fun (t, n, v) =>
      if n == 0 || n > 64 || t > 1000 then .error (.invalid "mandates config") else .ok ⟨t, n, v⟩)
    fun x => (x.target, x.numShards, x.validators)

/-- A seed and a count between 1 and 4096. -/
structure RngCase where
  seed : RngSeed
  n : UInt32

instance : Codec RngCase :=
  .tryIso (RngSeed × UInt32)
    (fun (s, n) => if n == 0 || n > 4096 then .error (.invalid "count") else .ok ⟨s, n⟩) fun x =>
    (x.seed, x.n)

private def enc [Codec α] (xs : Array α) : ByteArray :=
  xs.foldl (fun b x => b ++ Codec.encode x) ByteArray.empty

/-- The first `n` draws of `f` from the generator seeded by `seed`. -/
private def draw (seed : ByteArray) (f : ChaCha20Rng → α × ChaCha20Rng) (n : Nat) :
    Array α × ChaCha20Rng :=
  (List.range n).foldl
    (fun (acc, r) _ =>
      let (x, r) := f r
      (acc.push x, r))
    (#[], ChaCha20Rng.fromSeed seed)

private def rngFields (c : RngCase) : List (String × ByteArray) :=
  let seed := c.seed.bytes
  let u32s := (draw seed ChaCha20Rng.nextU32 200).1
  let u64s := (draw seed ChaCha20Rng.nextU64 100).1
  let ranges := (draw seed (·.genRange c.n) 60).1
  let (items, r) := (ChaCha20Rng.fromSeed seed).shuffle ((Array.range c.n.toNat).map Nat.toUInt32)
  let after := (r.nextU64).1
  [("u32s", enc u32s), ("u64s", enc u64s), ("range", enc ranges),
    ("shuffle", enc items ++ Codec.encode after)]

private def epochFields (e : EpochInfo) : List (String × ByteArray) :=
  let accounts : Array AccountId :=
    (Array.range e.validatorsLen).filterMap fun i => e.validatorAccountId i.toUInt64
  let ids : Array (Option UInt64) :=
    (accounts ++ #[account "nobody.near", account "a.near"]).map e.getValidatorId
  let bp : Array (Option UInt64) := sampleHeights.map e.sampleBlockProducer
  let settlement := e.chunkProducersSettlement
  let layout := e.shardLayout.getD (.v0 ⟨settlement.size.toUInt64, 0⟩)
  let shards : Array ShardId :=
    (if layout.numShards > 1000 then #[] else layout.shardIds) ++
      #[settlement.size.toUInt64, 1000, 18446744073709551615]
  let cp : Array (Option UInt64) :=
    shards.flatMap fun s => sampleHeights.map fun h => e.sampleChunkProducer layout s h
  let guarded :=
    match e.validatorMandates with
    | some m => m.config.numShards > 4096 || m.mandates.size > 1000000
    | none => false
  let cv :=
    if guarded then ByteArray.empty
    else
      match validatorHeights.mapM e.sampleChunkValidators with
      | some xs => Codec.encode xs
      | none => ByteArray.empty
  [("validatorAccounts", Codec.encode accounts), ("validatorIds", Codec.encode ids),
    ("bp", Codec.encode bp), ("cp", Codec.encode cp), ("cv", cv)]

private def blockInfoFields (b : BlockInfo) : List (String × ByteArray) :=
  [("hash", b.hash.bytes), ("height", Codec.encode b.height), ("prevHash", b.prevHash.bytes),
    ("epochId", b.epochId.hash.bytes), ("isGenesis", ⟨#[if b.isGenesis then 1 else 0]⟩)]

/-- Every epoch fixture type with its check. -/
def epochRegistry : List (String × Check) :=
  [("ShardUId", check ShardUId), ("ShardLayout", check ShardLayout layoutFields),
    ("ValidatorKickoutReason", check ValidatorKickoutReason),
    ("ValidatorStats", check ValidatorStats), ("ChunkStats", check ChunkStats),
    ("BlockChunkValidatorStats", check BlockChunkValidatorStats), ("SlashState", check SlashState),
    ("ValidatorWeight", check ValidatorWeight),
    ("StakeWeights", check (Array Balance) fun s => [("hash", builtIndex s)]),
    ("StakeWeightedIndex", check StakeWeightedIndex fun s => [("samples", samplerSamples s)]),
    ("ValidatorMandatesConfig", check ValidatorMandatesConfig),
    ("ValidatorMandates", check ValidatorMandates),
    ("MandatesInput",
      check MandatesInput fun i =>
        [("hash",
            match ValidatorMandates.new ⟨i.target, i.numShards⟩ i.validators with
            | some m => Codec.encode m
            | none => ByteArray.empty)]),
    ("RngCase", check RngCase rngFields), ("EpochInfo", check EpochInfo epochFields),
    ("BlockInfo", check BlockInfo blockInfoFields), ("EpochSummary", check EpochSummary),
    ("EpochSyncProofEpochData", check EpochSyncProofEpochData),
    ("EpochSyncProofLastEpochData",
      check EpochSyncProofLastEpochData fun d => [("hash", d.computeEpochSyncDataHash.bytes)]),
    ("EpochSyncProofCurrentEpochData", check EpochSyncProofCurrentEpochData),
    ("EpochSyncProof", check EpochSyncProof),
    ("CompressedEpochSyncProof", check CompressedEpochSyncProof)]
