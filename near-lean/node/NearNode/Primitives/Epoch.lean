import NearNode.Primitives.ShardLayout
import NearNode.Primitives.Rand
import NearNode.Primitives.Validator

/-!
# Epoch info

`near-primitives::epoch_info`, `rand`, `validator_mandates` and the epoch types of `types` at
`=0.37.4`: the five `EpochInfo` versions with the stake-weighted samplers and validator mandates
that V3 to V5 store, and the pure functions that pick block producers, chunk producers and chunk
validators from them. A `HashMap` field is a `SortedMap`. Where nearcore panics (an index out of
range, a division by zero, an overflow) the functions return `none`.
-/

namespace Near.Node

open Borsh

/-- `ValidatorId`: an index into the validators of an epoch. -/
abbrev ValidatorId :=
  UInt64

/-- `EpochHeight`. -/
abbrev EpochHeight :=
  UInt64

/-- `NumBlocks`. -/
abbrev NumBlocks :=
  UInt64

/-- `RngSeed`: `[u8; 32]`. -/
structure RngSeed where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec RngSeed :=
  .isoOf (.fixed 32) .mk RngSeed.bytes

/-- `StakeWeightedIndex`: the alias method tables for sampling an index with probability
proportional to its stake. -/
structure StakeWeightedIndex where
  stakeSum : Balance
  aliases : Array UInt64
  noAliasOdds : Array Balance
  deriving BEq, Inhabited

instance : Codec StakeWeightedIndex :=
  .iso (Balance × Array UInt64 × Array Balance) (fun (s, a, o) => ⟨s, a, o⟩) fun x =>
    (x.stakeSum, x.aliases, x.noAliasOdds)

namespace StakeWeightedIndex

/-- `StakeWeightedIndex::new`: Vose's alias method on the stakes scaled by their count. `none`
where nearcore overflows. -/
def new (stakes : Array Balance) : Option StakeWeightedIndex :=
  Id.run do
    let n := stakes.size
    let bound := 2 ^ 128
    let mut sum := 0
    for w in stakes do
      sum := sum + w.val
    if sum ≥ bound || stakes.any (·.val * n ≥ bound) then
      return none
    let mut odds := stakes.map (·.val * n)
    let mut aliases := Array.replicate n 0
    let mut smalls : Array Nat := #[]
    let mut bigs : Array Nat := #[]
    for i in [0:n] do
      if odds[i]! < sum then
        smalls := smalls.push i
      else
        bigs := bigs.push i
    for _ in [0:n + 1] do
      match smalls.back?, bigs.back? with
      | some s, some b =>
        smalls := smalls.pop
        bigs := bigs.pop
        aliases := aliases.set! s b
        odds := odds.set! b (odds[b]! - sum + odds[s]!)
        if odds[b]! < sum then
          smalls := smalls.push b
        else
          bigs := bigs.push b
      | _, _ =>
        break
    for s in smalls do
      odds := odds.set! s sum
    for b in bigs do
      odds := odds.set! b sum
    return some ⟨⟨sum⟩, aliases.map Nat.toUInt64, odds.map (⟨·⟩)⟩

/-- `StakeWeightedIndex::sample`: the index for a 32-byte seed. -/
def sample (s : StakeWeightedIndex) (seed : ByteArray) : Option Nat :=
  let le (from' count : Nat) : Nat :=
    (List.range count).foldr (fun i acc => acc * 256 + (seed.get! (from' + i)).toNat) 0
  if s.aliases.isEmpty || s.stakeSum.val == 0 then none
  else
    let index := le 0 8 % s.aliases.size
    let stake := le 8 16 % s.stakeSum.val
    match s.noAliasOdds[index]? with
    | none => none
    | some odds => if stake < odds.val then some index else (s.aliases[index]?).map (·.toNat)

end StakeWeightedIndex

/-- `ValidatorMandatesConfig`. -/
structure ValidatorMandatesConfig where
  targetMandatesPerShard : UInt64
  numShards : UInt64
  deriving BEq, Inhabited

instance : Codec ValidatorMandatesConfig :=
  .iso (UInt64 × UInt64) (fun (t, n) => ⟨t, n⟩) fun x => (x.targetMandatesPerShard, x.numShards)

/-- `ValidatorMandates`: whole mandates (a validator id per mandate) and the partial mandates. -/
structure ValidatorMandates where
  config : ValidatorMandatesConfig
  stakePerMandate : Balance
  mandates : Array ValidatorId
  partials : Array (ValidatorId × Balance)
  deriving BEq, Inhabited

instance : Codec ValidatorMandates :=
  .iso (ValidatorMandatesConfig × Balance × Array ValidatorId × Array (ValidatorId × Balance))
    (fun (c, s, m, p) => ⟨c, s, m, p⟩) fun x =>
    (x.config, x.stakePerMandate, x.mandates, x.partials)

namespace ValidatorMandates

private def u128Max : Nat :=
  2 ^ 128 - 1

/-- `binary_search` of `compute_mandate_price`, over the number of whole mandates `f`, which does
not increase with the price. -/
private def search (f : Nat → Nat) (lo hi target : Nat) : Option Nat :=
  Id.run do
    let highestExact (lo hi : Nat) : Option Nat :=
      Id.run do
        if hi < lo then
          return none
        let mut lo := lo
        let mut hi := hi
        for _ in [0:300] do
          if hi - lo > 1 then
            let mid := lo + (hi - lo) / 2
            let v := f mid
            if v == target then
              lo := mid
            else if v < target then
              hi := mid
            else
              return none
        return some lo
    if hi < lo then
      return none
    if f lo == target then
      return highestExact lo hi
    else if f hi == target then
      return some hi
    let mut lo := lo
    let mut hi := hi
    for _ in [0:300] do
      if hi - lo > 1 then
        let mid := lo + (hi - lo) / 2
        let v := f mid
        if v == target then
          return highestExact mid hi
        else if v < target then
          hi := mid
        else
          lo := mid
    return some lo

/-- `compute_mandate_price`: the largest price at which the number of whole mandates is the target
(or the best price above it). -/
def computePrice (c : ValidatorMandatesConfig) (stakes : Array Balance) : Option Nat :=
  let total := stakes.foldl (fun s w => min u128Max (s + w.val)) 0
  let perShard := min (2 ^ 64 - 1) (c.numShards.toNat * c.targetMandatesPerShard.toNat)
  let target := min perShard total
  search (fun price => stakes.foldl (fun s w => min u128Max (s + w.val / price)) 0) 1 total target

/-- `ValidatorMandates::new`; `none` where nearcore panics. -/
def new (c : ValidatorMandatesConfig) (validators : Array ValidatorStake) :
    Option ValidatorMandates := do
  if c.numShards == 0 then
    none
  let stakes :=
    validators.map fun
      | .v1 v => v.stake
  let price ← computePrice c stakes
  if price == 0 then
    none
  let mut mandates : Array ValidatorId := #[]
  let mut partials : Array (ValidatorId × Balance) := #[]
  for i in [0:stakes.size] do
    let count := stakes[i]!.val / price
    if count ≥ 2 ^ 16 then
      none
    mandates := mandates ++ Array.replicate count i.toUInt64
    let rest := stakes[i]!.val % price
    if rest > 0 then
      partials := partials.push (i.toUInt64, ⟨rest⟩)
  pure ⟨c, ⟨price⟩, mandates, partials⟩

/-- Add `amount` to the entry of `id`, keeping the entries ascending by id. -/
private def addTo (m : Array (ValidatorId × Nat)) (id : ValidatorId) (amount : Nat) :
    Array (ValidatorId × Nat) :=
  match m.findIdx? (·.1 == id) with
  | some i => m.modify i fun (k, v) => (k, v + amount)
  | none => m.push (id, amount)

/-- `ValidatorMandates::sample`: shuffle the shards, the mandates and the partials, deal them out
to the shards round robin, and shuffle the validators of each shard. `none` where a stake sum
overflows. -/
def sample (m : ValidatorMandates) (rng : ChaCha20Rng) :
    Option (Array (Array (ValidatorId × Balance)) × ChaCha20Rng) :=
  Id.run do
    let numShards := m.config.numShards.toNat
    let mut rng := rng
    let (shardsForMandates, r) := rng.shuffle (Array.range numShards)
    let (shardsForPartials, r) := r.shuffle (Array.range numShards)
    let (mandates, r) := r.shuffle m.mandates
    let (partials, r) := r.shuffle m.partials
    rng := r
    let mut assignment : Array (Array (ValidatorId × Nat)) := Array.replicate numShards #[]
    for shard in [0:numShards] do
      let mut idx := shard
      while idx < mandates.size do
        assignment :=
          assignment.modify shardsForMandates[shard]! fun a =>
            addTo a mandates[idx]! m.stakePerMandate.val
        idx := idx + numShards
      idx := shard
      while idx < partials.size do
        let (id, weight) := partials[idx]!
        assignment := assignment.modify shardsForPartials[shard]! fun a => addTo a id weight.val
        idx := idx + numShards
    let mut out : Array (Array (ValidatorId × Balance)) := #[]
    for shard in [0:numShards] do
      let entries := assignment[shard]!
      let ids := (entries.map (·.1)).qsort (· < ·)
      let (ordered, r) := rng.shuffle ids
      rng := r
      out :=
        out.push (ordered.map fun id => (id, ⟨(entries.find? (·.1 == id)).map (·.2) |>.getD 0⟩))
    if assignment.any (·.any (·.2 ≥ 2 ^ 128)) then
      return none
    return some (out, rng)

end ValidatorMandates

/-- `ValidatorKickoutReason`. -/
inductive ValidatorKickoutReason where
  | unusedSlashed
  | notEnoughBlocks (produced expected : NumBlocks)
  | notEnoughChunks (produced expected : NumBlocks)
  | unstaked
  | notEnoughStake (stake threshold : Balance)
  | didNotGetASeat
  | notEnoughChunkEndorsements (produced expected : NumBlocks)
  | protocolVersionTooOld (version networkVersion : ProtocolVersion)
  deriving BEq, Inhabited

instance : Codec ValidatorKickoutReason :=
  .enum "ValidatorKickoutReason"
    [.const 0 .unusedSlashed,
      .variant 1 (NumBlocks × NumBlocks) (fun (p, e) => .notEnoughBlocks p e) fun
        | .notEnoughBlocks p e => some (p, e)
        | _ => none,
      .variant 2 (NumBlocks × NumBlocks) (fun (p, e) => .notEnoughChunks p e) fun
        | .notEnoughChunks p e => some (p, e)
        | _ => none,
      .const 3 .unstaked,
      .variant 4 (Balance × Balance) (fun (s, t) => .notEnoughStake s t) fun
        | .notEnoughStake s t => some (s, t)
        | _ => none,
      .const 5 .didNotGetASeat,
      .variant 6 (NumBlocks × NumBlocks) (fun (p, e) => .notEnoughChunkEndorsements p e) fun
        | .notEnoughChunkEndorsements p e => some (p, e)
        | _ => none,
      .variant 7 (ProtocolVersion × ProtocolVersion) (fun (v, n) => .protocolVersionTooOld v n) fun
        | .protocolVersionTooOld v n => some (v, n)
        | _ => none]

/-- `ValidatorStats`. -/
structure ValidatorStats where
  produced : NumBlocks
  expected : NumBlocks
  deriving BEq, Inhabited

instance : Codec ValidatorStats :=
  .iso (NumBlocks × NumBlocks) (fun (p, e) => ⟨p, e⟩) fun x => (x.produced, x.expected)

/-- `ChunkStats`. -/
structure ChunkStats where
  production : ValidatorStats
  endorsement : ValidatorStats
  deriving BEq, Inhabited

instance : Codec ChunkStats :=
  .iso (ValidatorStats × ValidatorStats) (fun (p, e) => ⟨p, e⟩) fun x =>
    (x.production, x.endorsement)

/-- `BlockChunkValidatorStats`. -/
structure BlockChunkValidatorStats where
  blockStats : ValidatorStats
  chunkStats : ChunkStats
  deriving BEq, Inhabited

instance : Codec BlockChunkValidatorStats :=
  .iso (ValidatorStats × ChunkStats) (fun (b, c) => ⟨b, c⟩) fun x => (x.blockStats, x.chunkStats)

/-- `ValidatorWeight`: a hidden validator and its weight. -/
structure ValidatorWeight where
  validatorId : ValidatorId
  weight : UInt64
  deriving BEq, Inhabited

instance : Codec ValidatorWeight :=
  .iso (ValidatorId × UInt64) (fun (v, w) => ⟨v, w⟩) fun x => (x.validatorId, x.weight)

/-- `EpochInfoV1`. -/
structure EpochInfoV1 where
  epochHeight : EpochHeight
  validators : Array ValidatorStakeV1
  validatorToIndex : SortedMap AccountId ValidatorId
  blockProducersSettlement : Array ValidatorId
  chunkProducersSettlement : Array (Array ValidatorId)
  hiddenValidatorsSettlement : Array ValidatorWeight
  fishermen : Array ValidatorStakeV1
  fishermenToIndex : SortedMap AccountId ValidatorId
  stakeChange : SortedMap AccountId Balance
  validatorReward : SortedMap AccountId Balance
  validatorKickout : SortedMap AccountId ValidatorKickoutReason
  mintedAmount : Balance
  seatPrice : Balance
  protocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec EpochInfoV1 :=
  .iso
    (EpochHeight ×
      Array ValidatorStakeV1 ×
      SortedMap AccountId ValidatorId ×
      Array ValidatorId ×
      Array (Array ValidatorId) ×
      Array ValidatorWeight ×
      Array ValidatorStakeV1 ×
      SortedMap AccountId ValidatorId ×
      SortedMap AccountId Balance ×
      SortedMap AccountId Balance ×
      SortedMap AccountId ValidatorKickoutReason × Balance × Balance × ProtocolVersion)
    (fun (eh, v, vi, bp, cp, h, f, fi, sc, vr, vk, ma, sp, pv) =>
      ⟨eh, v, vi, bp, cp, h, f, fi, sc, vr, vk, ma, sp, pv⟩)
    fun x =>
    (x.epochHeight, x.validators, x.validatorToIndex, x.blockProducersSettlement,
      x.chunkProducersSettlement, x.hiddenValidatorsSettlement, x.fishermen, x.fishermenToIndex,
      x.stakeChange, x.validatorReward, x.validatorKickout, x.mintedAmount, x.seatPrice,
      x.protocolVersion)

/-- `EpochInfoV2`: validators are versioned. -/
structure EpochInfoV2 where
  epochHeight : EpochHeight
  validators : Array ValidatorStake
  validatorToIndex : SortedMap AccountId ValidatorId
  blockProducersSettlement : Array ValidatorId
  chunkProducersSettlement : Array (Array ValidatorId)
  hiddenValidatorsSettlement : Array ValidatorWeight
  fishermen : Array ValidatorStake
  fishermenToIndex : SortedMap AccountId ValidatorId
  stakeChange : SortedMap AccountId Balance
  validatorReward : SortedMap AccountId Balance
  validatorKickout : SortedMap AccountId ValidatorKickoutReason
  mintedAmount : Balance
  seatPrice : Balance
  protocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec EpochInfoV2 :=
  .iso
    (EpochHeight ×
      Array ValidatorStake ×
      SortedMap AccountId ValidatorId ×
      Array ValidatorId ×
      Array (Array ValidatorId) ×
      Array ValidatorWeight ×
      Array ValidatorStake ×
      SortedMap AccountId ValidatorId ×
      SortedMap AccountId Balance ×
      SortedMap AccountId Balance ×
      SortedMap AccountId ValidatorKickoutReason × Balance × Balance × ProtocolVersion)
    (fun (eh, v, vi, bp, cp, h, f, fi, sc, vr, vk, ma, sp, pv) =>
      ⟨eh, v, vi, bp, cp, h, f, fi, sc, vr, vk, ma, sp, pv⟩)
    fun x =>
    (x.epochHeight, x.validators, x.validatorToIndex, x.blockProducersSettlement,
      x.chunkProducersSettlement, x.hiddenValidatorsSettlement, x.fishermen, x.fishermenToIndex,
      x.stakeChange, x.validatorReward, x.validatorKickout, x.mintedAmount, x.seatPrice,
      x.protocolVersion)

/-- `EpochInfoV3`: adds the seed and the samplers that pick producers at each height. -/
structure EpochInfoV3 where
  base : EpochInfoV2
  rngSeed : RngSeed
  blockProducersSampler : StakeWeightedIndex
  chunkProducersSampler : Array StakeWeightedIndex
  deriving BEq, Inhabited

instance : Codec EpochInfoV3 :=
  .iso (EpochInfoV2 × RngSeed × StakeWeightedIndex × Array StakeWeightedIndex)
    (fun (b, r, s, c) => ⟨b, r, s, c⟩) fun x =>
    (x.base, x.rngSeed, x.blockProducersSampler, x.chunkProducersSampler)

/-- `EpochInfoV4`: adds the validator mandates; the hidden validators and fishermen are unused. -/
structure EpochInfoV4 where
  epochHeight : EpochHeight
  validators : Array ValidatorStake
  validatorToIndex : SortedMap AccountId ValidatorId
  blockProducersSettlement : Array ValidatorId
  chunkProducersSettlement : Array (Array ValidatorId)
  hiddenValidatorsSettlement : Array ValidatorWeight
  fishermen : Array ValidatorStake
  fishermenToIndex : SortedMap AccountId ValidatorId
  stakeChange : SortedMap AccountId Balance
  validatorReward : SortedMap AccountId Balance
  validatorKickout : SortedMap AccountId ValidatorKickoutReason
  mintedAmount : Balance
  seatPrice : Balance
  protocolVersion : ProtocolVersion
  rngSeed : RngSeed
  blockProducersSampler : StakeWeightedIndex
  chunkProducersSampler : Array StakeWeightedIndex
  validatorMandates : ValidatorMandates
  deriving BEq, Inhabited

instance : Codec EpochInfoV4 :=
  .iso (EpochInfoV2 × RngSeed × StakeWeightedIndex × Array StakeWeightedIndex × ValidatorMandates)
    (fun (b, r, s, c, m) =>
      ⟨b.epochHeight, b.validators, b.validatorToIndex, b.blockProducersSettlement,
        b.chunkProducersSettlement, b.hiddenValidatorsSettlement, b.fishermen, b.fishermenToIndex,
        b.stakeChange, b.validatorReward, b.validatorKickout, b.mintedAmount, b.seatPrice,
        b.protocolVersion, r, s, c, m⟩)
    fun x =>
    (⟨x.epochHeight, x.validators, x.validatorToIndex, x.blockProducersSettlement,
        x.chunkProducersSettlement, x.hiddenValidatorsSettlement, x.fishermen, x.fishermenToIndex,
        x.stakeChange, x.validatorReward, x.validatorKickout, x.mintedAmount, x.seatPrice,
        x.protocolVersion⟩,
      x.rngSeed, x.blockProducersSampler, x.chunkProducersSampler, x.validatorMandates)

/-- `EpochInfoV5`: adds the shard layout and the last resharding; no hidden validators or
fishermen. -/
structure EpochInfoV5 where
  epochHeight : EpochHeight
  validators : Array ValidatorStake
  validatorToIndex : SortedMap AccountId ValidatorId
  blockProducersSettlement : Array ValidatorId
  chunkProducersSettlement : Array (Array ValidatorId)
  stakeChange : SortedMap AccountId Balance
  validatorReward : SortedMap AccountId Balance
  validatorKickout : SortedMap AccountId ValidatorKickoutReason
  mintedAmount : Balance
  seatPrice : Balance
  protocolVersion : ProtocolVersion
  shardLayout : ShardLayout
  lastResharding : Option EpochHeight
  rngSeed : RngSeed
  blockProducersSampler : StakeWeightedIndex
  chunkProducersSampler : Array StakeWeightedIndex
  validatorMandates : ValidatorMandates
  deriving BEq, Inhabited

instance : Codec EpochInfoV5 :=
  .iso
    (EpochHeight ×
      Array ValidatorStake ×
      SortedMap AccountId ValidatorId ×
      Array ValidatorId ×
      Array (Array ValidatorId) ×
      SortedMap AccountId Balance ×
      SortedMap AccountId Balance ×
      SortedMap AccountId ValidatorKickoutReason ×
      Balance ×
      Balance ×
      ProtocolVersion ×
      ShardLayout ×
      Option EpochHeight ×
      RngSeed × StakeWeightedIndex × Array StakeWeightedIndex × ValidatorMandates)
    (fun (eh, v, vi, bp, cp, sc, vr, vk, ma, sp, pv, sl, lr, rs, bs, cs, vm) =>
      ⟨eh, v, vi, bp, cp, sc, vr, vk, ma, sp, pv, sl, lr, rs, bs, cs, vm⟩)
    fun x =>
    (x.epochHeight, x.validators, x.validatorToIndex, x.blockProducersSettlement,
      x.chunkProducersSettlement, x.stakeChange, x.validatorReward, x.validatorKickout,
      x.mintedAmount, x.seatPrice, x.protocolVersion, x.shardLayout, x.lastResharding, x.rngSeed,
      x.blockProducersSampler, x.chunkProducersSampler, x.validatorMandates)

/-- `EpochInfo`. -/
inductive EpochInfo where
  | v1 (e : EpochInfoV1)
  | v2 (e : EpochInfoV2)
  | v3 (e : EpochInfoV3)
  | v4 (e : EpochInfoV4)
  | v5 (e : EpochInfoV5)
  deriving BEq, Inhabited

instance : Codec EpochInfo :=
  .enum "EpochInfo"
    [.variant 0 EpochInfoV1 .v1 fun
        | .v1 e => some e
        | _ => none,
      .variant 1 EpochInfoV2 .v2 fun
        | .v2 e => some e
        | _ => none,
      .variant 2 EpochInfoV3 .v3 fun
        | .v3 e => some e
        | _ => none,
      .variant 3 EpochInfoV4 .v4 fun
        | .v4 e => some e
        | _ => none,
      .variant 4 EpochInfoV5 .v5 fun
        | .v5 e => some e
        | _ => none]

namespace EpochInfo

/-- `EpochInfo::epoch_height`. -/
def epochHeight : EpochInfo → EpochHeight
  | .v1 e => e.epochHeight
  | .v2 e => e.epochHeight
  | .v3 e => e.base.epochHeight
  | .v4 e => e.epochHeight
  | .v5 e => e.epochHeight

/-- `EpochInfo::protocol_version`. -/
def protocolVersion : EpochInfo → ProtocolVersion
  | .v1 e => e.protocolVersion
  | .v2 e => e.protocolVersion
  | .v3 e => e.base.protocolVersion
  | .v4 e => e.protocolVersion
  | .v5 e => e.protocolVersion

/-- `EpochInfo::block_producers_settlement`. -/
def blockProducersSettlement : EpochInfo → Array ValidatorId
  | .v1 e => e.blockProducersSettlement
  | .v2 e => e.blockProducersSettlement
  | .v3 e => e.base.blockProducersSettlement
  | .v4 e => e.blockProducersSettlement
  | .v5 e => e.blockProducersSettlement

/-- `EpochInfo::chunk_producers_settlement`. -/
def chunkProducersSettlement : EpochInfo → Array (Array ValidatorId)
  | .v1 e => e.chunkProducersSettlement
  | .v2 e => e.chunkProducersSettlement
  | .v3 e => e.base.chunkProducersSettlement
  | .v4 e => e.chunkProducersSettlement
  | .v5 e => e.chunkProducersSettlement

/-- `EpochInfo::validators_len`. -/
def validatorsLen : EpochInfo → Nat
  | .v1 e => e.validators.size
  | .v2 e => e.validators.size
  | .v3 e => e.base.validators.size
  | .v4 e => e.validators.size
  | .v5 e => e.validators.size

/-- `EpochInfo::validator_account_id`. -/
def validatorAccountId (e : EpochInfo) (id : ValidatorId) : Option AccountId :=
  match e with
  | .v1 e => e.validators[id.toNat]?.map (·.accountId)
  | .v2 e =>
    e.validators[id.toNat]?.map fun
      | .v1 v => v.accountId
  | .v3 e =>
    e.base.validators[id.toNat]?.map fun
      | .v1 v => v.accountId
  | .v4 e =>
    e.validators[id.toNat]?.map fun
      | .v1 v => v.accountId
  | .v5 e =>
    e.validators[id.toNat]?.map fun
      | .v1 v => v.accountId

/-- `EpochInfo::get_validator_id`. -/
def getValidatorId (e : EpochInfo) (account : AccountId) : Option ValidatorId :=
  match e with
  | .v1 e => e.validatorToIndex.find? account
  | .v2 e => e.validatorToIndex.find? account
  | .v3 e => e.base.validatorToIndex.find? account
  | .v4 e => e.validatorToIndex.find? account
  | .v5 e => e.validatorToIndex.find? account

/-- `EpochInfo::rng_seed`: zero before V3. -/
def rngSeed : EpochInfo → RngSeed
  | .v1 _ | .v2 _ => ⟨ByteArray.mk (Array.replicate 32 0)⟩
  | .v3 e => e.rngSeed
  | .v4 e => e.rngSeed
  | .v5 e => e.rngSeed

/-- `EpochInfo::shard_layout`: only V5 stores one. -/
def shardLayout : EpochInfo → Option ShardLayout
  | .v5 e => some e.shardLayout
  | _ => none

/-- `EpochInfo::validator_mandates`: empty before V4. -/
def validatorMandates : EpochInfo → Option ValidatorMandates
  | .v4 e => some e.validatorMandates
  | .v5 e => some e.validatorMandates
  | _ => none

/-- `block_produce_seed`: the hash of the epoch seed and the height. -/
def blockProduceSeed (height : BlockHeight) (seed : RngSeed) : ByteArray :=
  (CryptoHash.hash (seed.bytes ++ Codec.encode height)).bytes

/-- `chunk_produce_seed`: the hash of the epoch seed, the height and the shard. -/
def chunkProduceSeed (seed : RngSeed) (height : BlockHeight) (shard : ShardId) : ByteArray :=
  (CryptoHash.hash (seed.bytes ++ Codec.encode height ++ Codec.encode shard)).bytes

/-- `EpochInfo::sample_block_producer`. -/
def sampleBlockProducer (e : EpochInfo) (height : BlockHeight) : Option ValidatorId :=
  let settlement := e.blockProducersSettlement
  let byHeight := settlement[(height.toNat % settlement.size : Nat)]?
  let sampled (sampler : StakeWeightedIndex) : Option ValidatorId :=
    (sampler.sample (blockProduceSeed height e.rngSeed)).bind (settlement[·]?)
  match e with
  | .v1 _ | .v2 _ => if settlement.isEmpty then none else byHeight
  | .v3 e => sampled e.blockProducersSampler
  | .v4 e => sampled e.blockProducersSampler
  | .v5 e => sampled e.blockProducersSampler

/-- `EpochInfo::sample_chunk_producer` under `layout`. -/
def sampleChunkProducer (e : EpochInfo) (layout : ShardLayout) (shard : ShardId)
    (height : BlockHeight) : Option ValidatorId := do
  let index ← layout.getShardIndex shard
  let producers ← e.chunkProducersSettlement[index]?
  let sampled (samplers : Array StakeWeightedIndex) : Option ValidatorId := do
    let sample ← (← samplers[index]?).sample (chunkProduceSeed e.rngSeed height shard)
    producers[sample]?
  match e with
  | .v1 _ | .v2 _ =>
    if producers.isEmpty then
      none
    else
      producers[(height.toNat % producers.size : Nat)]?
  | .v3 e =>
    sampled e.chunkProducersSampler
  | .v4 e =>
    sampled e.chunkProducersSampler
  | .v5 e =>
    sampled e.chunkProducersSampler

/-- `chunk_validate_rng`: a ChaCha20 generator seeded by the hash of the epoch seed and height. -/
def chunkValidateRng (seed : RngSeed) (height : BlockHeight) : ChaCha20Rng :=
  .fromSeed (CryptoHash.hash (seed.bytes ++ Codec.encode height)).bytes

/-- `EpochInfo::sample_chunk_validators`: the validators and stakes assigned to each shard; empty
before V4. -/
def sampleChunkValidators (e : EpochInfo) (height : BlockHeight) :
    Option (Array (Array (ValidatorId × Balance))) :=
  match e with
  | .v4 e => (e.validatorMandates.sample (chunkValidateRng e.rngSeed height)).map (·.1)
  | .v5 e => (e.validatorMandates.sample (chunkValidateRng e.rngSeed height)).map (·.1)
  | _ => some #[]

end EpochInfo

end Near.Node
