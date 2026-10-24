import NearNode.Primitives.Epoch
import NearNode.Primitives.Block

/-!
# Block info and epoch sync

`near-primitives::epoch_block_info`, `epoch_manager::EpochSummary` and `epoch_sync` at `=0.37.4`:
the per-block record of the epoch manager (five versions), the summary of an epoch, and the proof
that lets a node join at an epoch boundary. `CompressedEpochSyncProof` is a zstd frame that stays
opaque here.
-/

namespace Near.Node

open Borsh

/-- `SlashState`. -/
inductive SlashState where
  | doubleSign
  | alreadySlashed
  | other
  deriving BEq, Inhabited

instance : Codec SlashState :=
  .enum "SlashState" [.const 0 .doubleSign, .const 1 .alreadySlashed, .const 2 .other]

/-- `BlockInfoV1`. -/
structure BlockInfoV1 where
  hash : CryptoHash
  height : BlockHeight
  lastFinalizedHeight : BlockHeight
  lastFinalBlockHash : CryptoHash
  prevHash : CryptoHash
  epochFirstBlock : CryptoHash
  epochId : EpochId
  proposals : Array ValidatorStakeV1
  chunkMask : Array Bool
  latestProtocolVersion : ProtocolVersion
  slashed : SortedMap AccountId SlashState
  totalSupply : Balance
  timestampNanosec : UInt64
  deriving BEq, Inhabited

instance : Codec BlockInfoV1 :=
  .iso
    (CryptoHash ×
      BlockHeight ×
      BlockHeight ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      EpochId ×
      Array ValidatorStakeV1 ×
      Array Bool × ProtocolVersion × SortedMap AccountId SlashState × Balance × UInt64)
    (fun (h, ht, lf, lb, p, ef, ei, pr, cm, lv, sl, ts, tn) =>
      ⟨h, ht, lf, lb, p, ef, ei, pr, cm, lv, sl, ts, tn⟩)
    fun x =>
    (x.hash, x.height, x.lastFinalizedHeight, x.lastFinalBlockHash, x.prevHash, x.epochFirstBlock,
      x.epochId, x.proposals, x.chunkMask, x.latestProtocolVersion, x.slashed, x.totalSupply,
      x.timestampNanosec)

/-- `BlockInfoV2`: versioned proposals. -/
structure BlockInfoV2 where
  hash : CryptoHash
  height : BlockHeight
  lastFinalizedHeight : BlockHeight
  lastFinalBlockHash : CryptoHash
  prevHash : CryptoHash
  epochFirstBlock : CryptoHash
  epochId : EpochId
  proposals : Array ValidatorStake
  chunkMask : Array Bool
  latestProtocolVersion : ProtocolVersion
  slashed : SortedMap AccountId SlashState
  totalSupply : Balance
  timestampNanosec : UInt64
  deriving BEq, Inhabited

instance : Codec BlockInfoV2 :=
  .iso
    (CryptoHash ×
      BlockHeight ×
      BlockHeight ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      EpochId ×
      Array ValidatorStake ×
      Array Bool × ProtocolVersion × SortedMap AccountId SlashState × Balance × UInt64)
    (fun (h, ht, lf, lb, p, ef, ei, pr, cm, lv, sl, ts, tn) =>
      ⟨h, ht, lf, lb, p, ef, ei, pr, cm, lv, sl, ts, tn⟩)
    fun x =>
    (x.hash, x.height, x.lastFinalizedHeight, x.lastFinalBlockHash, x.prevHash, x.epochFirstBlock,
      x.epochId, x.proposals, x.chunkMask, x.latestProtocolVersion, x.slashed, x.totalSupply,
      x.timestampNanosec)

/-- `BlockInfoV3`: adds the chunk endorsements. -/
structure BlockInfoV3 where
  base : BlockInfoV2
  chunkEndorsements : ChunkEndorsementsBitmap
  deriving BEq, Inhabited

instance : Codec BlockInfoV3 :=
  .iso (BlockInfoV2 × ChunkEndorsementsBitmap) (fun (b, c) => ⟨b, c⟩) fun x =>
    (x.base, x.chunkEndorsements)

/-- `BlockInfoV4`: no slashing, adds the shard split. -/
structure BlockInfoV4 where
  hash : CryptoHash
  height : BlockHeight
  lastFinalizedHeight : BlockHeight
  lastFinalBlockHash : CryptoHash
  prevHash : CryptoHash
  epochFirstBlock : CryptoHash
  epochId : EpochId
  proposals : Array ValidatorStake
  chunkMask : Array Bool
  latestProtocolVersion : ProtocolVersion
  totalSupply : Balance
  timestampNanosec : UInt64
  chunkEndorsements : ChunkEndorsementsBitmap
  shardSplit : Option (ShardId × AccountId)
  deriving BEq, Inhabited

instance : Codec BlockInfoV4 :=
  .iso
    (CryptoHash ×
      BlockHeight ×
      BlockHeight ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      EpochId ×
      Array ValidatorStake ×
      Array Bool ×
      ProtocolVersion × Balance × UInt64 × ChunkEndorsementsBitmap × Option (ShardId × AccountId))
    (fun (h, ht, lf, lb, p, ef, ei, pr, cm, lv, ts, tn, ce, ss) =>
      ⟨h, ht, lf, lb, p, ef, ei, pr, cm, lv, ts, tn, ce, ss⟩)
    fun x =>
    (x.hash, x.height, x.lastFinalizedHeight, x.lastFinalBlockHash, x.prevHash, x.epochFirstBlock,
      x.epochId, x.proposals, x.chunkMask, x.latestProtocolVersion, x.totalSupply,
      x.timestampNanosec, x.chunkEndorsements, x.shardSplit)

/-- `BlockInfoV5`: adds the last certified block epoch and the SPICE endorsement stats. -/
structure BlockInfoV5 where
  base : BlockInfoV4
  lastCertifiedBlockEpoch : EpochId
  spiceChunkEndorsementStats : Array SpiceChunkEndorsementStats
  deriving BEq, Inhabited

instance : Codec BlockInfoV5 :=
  .iso (BlockInfoV4 × EpochId × Array SpiceChunkEndorsementStats) (fun (b, l, s) => ⟨b, l, s⟩)
    fun x => (x.base, x.lastCertifiedBlockEpoch, x.spiceChunkEndorsementStats)

/-- `BlockInfo`. -/
inductive BlockInfo where
  | v1 (b : BlockInfoV1)
  | v2 (b : BlockInfoV2)
  | v3 (b : BlockInfoV3)
  | v4 (b : BlockInfoV4)
  | v5 (b : BlockInfoV5)
  deriving BEq, Inhabited

instance : Codec BlockInfo :=
  .enum "BlockInfo"
    [.variant 0 BlockInfoV1 .v1 fun
        | .v1 b => some b
        | _ => none,
      .variant 1 BlockInfoV2 .v2 fun
        | .v2 b => some b
        | _ => none,
      .variant 2 BlockInfoV3 .v3 fun
        | .v3 b => some b
        | _ => none,
      .variant 3 BlockInfoV4 .v4 fun
        | .v4 b => some b
        | _ => none,
      .variant 4 BlockInfoV5 .v5 fun
        | .v5 b => some b
        | _ => none]

namespace BlockInfo

/-- `BlockInfo::hash`. -/
def hash : BlockInfo → CryptoHash
  | .v1 b => b.hash
  | .v2 b => b.hash
  | .v3 b => b.base.hash
  | .v4 b => b.hash
  | .v5 b => b.base.hash

/-- `BlockInfo::height`. -/
def height : BlockInfo → BlockHeight
  | .v1 b => b.height
  | .v2 b => b.height
  | .v3 b => b.base.height
  | .v4 b => b.height
  | .v5 b => b.base.height

/-- `BlockInfo::prev_hash`. -/
def prevHash : BlockInfo → CryptoHash
  | .v1 b => b.prevHash
  | .v2 b => b.prevHash
  | .v3 b => b.base.prevHash
  | .v4 b => b.prevHash
  | .v5 b => b.base.prevHash

/-- `BlockInfo::epoch_id`. -/
def epochId : BlockInfo → EpochId
  | .v1 b => b.epochId
  | .v2 b => b.epochId
  | .v3 b => b.base.epochId
  | .v4 b => b.epochId
  | .v5 b => b.base.epochId

/-- `BlockInfo::is_genesis`. -/
def isGenesis (b : BlockInfo) : Bool :=
  b.prevHash == CryptoHash.zero

end BlockInfo

/-- `EpochSummary`: the epoch manager's summary of one epoch. -/
structure EpochSummary where
  prevEpochLastBlockHash : CryptoHash
  allProposals : Array ValidatorStake
  validatorKickout : SortedMap AccountId ValidatorKickoutReason
  validatorBlockChunkStats : SortedMap AccountId BlockChunkValidatorStats
  nextNextEpochVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec EpochSummary :=
  .iso
    (CryptoHash ×
      Array ValidatorStake ×
      SortedMap AccountId ValidatorKickoutReason ×
      SortedMap AccountId BlockChunkValidatorStats × ProtocolVersion)
    (fun (p, a, k, s, v) => ⟨p, a, k, s, v⟩) fun x =>
    (x.prevEpochLastBlockHash, x.allProposals, x.validatorKickout, x.validatorBlockChunkStats,
      x.nextNextEpochVersion)

/-- `EpochSyncProofEpochData`. -/
structure EpochSyncProofEpochData where
  blockProducers : Array ValidatorStake
  useVersionedBpHashFormat : Bool
  lastFinalBlockHeader : BlockHeader
  thisEpochEndorsementsForLastFinalBlock : Array (Option Signature)
  deriving BEq, Inhabited

instance : Codec EpochSyncProofEpochData :=
  .iso (Array ValidatorStake × Bool × BlockHeader × Array (Option Signature))
    (fun (b, u, h, e) => ⟨b, u, h, e⟩) fun x =>
    (x.blockProducers, x.useVersionedBpHashFormat, x.lastFinalBlockHeader,
      x.thisEpochEndorsementsForLastFinalBlock)

/-- `EpochSyncProofLastEpochData`. -/
structure EpochSyncProofLastEpochData where
  epochInfo : EpochInfo
  nextEpochInfo : EpochInfo
  nextNextEpochInfo : EpochInfo
  firstBlockInEpoch : BlockInfo
  lastBlockInEpoch : BlockInfo
  secondLastBlockInEpoch : BlockInfo
  deriving BEq, Inhabited

instance : Codec EpochSyncProofLastEpochData :=
  .iso (EpochInfo × EpochInfo × EpochInfo × BlockInfo × BlockInfo × BlockInfo)
    (fun (e, n, nn, f, l, s) => ⟨e, n, nn, f, l, s⟩) fun x =>
    (x.epochInfo, x.nextEpochInfo, x.nextNextEpochInfo, x.firstBlockInEpoch, x.lastBlockInEpoch,
      x.secondLastBlockInEpoch)

/-- `EpochSyncProofLastEpochData::compute_epoch_sync_data_hash`. -/
def EpochSyncProofLastEpochData.computeEpochSyncDataHash (d : EpochSyncProofLastEpochData) :
    CryptoHash :=
  CryptoHash.hashBorsh
    (d.firstBlockInEpoch, d.secondLastBlockInEpoch, d.lastBlockInEpoch, d.epochInfo,
      d.nextEpochInfo, d.nextNextEpochInfo)

/-- `EpochSyncProofCurrentEpochData`. -/
structure EpochSyncProofCurrentEpochData where
  firstBlockHeaderInEpoch : BlockHeader
  lastBlockHeaderInPrevEpoch : BlockHeader
  secondLastBlockHeaderInPrevEpoch : BlockHeader
  merkleProofForFirstBlock : Array MerklePathItem
  partialMerkleTreeForFirstBlock : PartialMerkleTree
  deriving BEq, Inhabited

instance : Codec EpochSyncProofCurrentEpochData :=
  .iso (BlockHeader × BlockHeader × BlockHeader × Array MerklePathItem × PartialMerkleTree)
    (fun (f, l, s, m, p) => ⟨f, l, s, m, p⟩) fun x =>
    (x.firstBlockHeaderInEpoch, x.lastBlockHeaderInPrevEpoch, x.secondLastBlockHeaderInPrevEpoch,
      x.merkleProofForFirstBlock, x.partialMerkleTreeForFirstBlock)

/-- `EpochSyncProofV1`. -/
structure EpochSyncProofV1 where
  allEpochs : Array EpochSyncProofEpochData
  lastEpoch : EpochSyncProofLastEpochData
  currentEpoch : EpochSyncProofCurrentEpochData
  deriving BEq, Inhabited

instance : Codec EpochSyncProofV1 :=
  .iso
    (Array EpochSyncProofEpochData × EpochSyncProofLastEpochData × EpochSyncProofCurrentEpochData)
    (fun (a, l, c) => ⟨a, l, c⟩) fun x => (x.allEpochs, x.lastEpoch, x.currentEpoch)

/-- `EpochSyncProof`. -/
inductive EpochSyncProof where
  | v1 (p : EpochSyncProofV1)
  deriving BEq, Inhabited

instance : Codec EpochSyncProof :=
  .enum "EpochSyncProof"
    [.variant 0 EpochSyncProofV1 .v1 fun
        | .v1 p => some p]

/-- `CompressedEpochSyncProof`: the zstd-compressed Borsh `EpochSyncProof`. -/
structure CompressedEpochSyncProof where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec CompressedEpochSyncProof :=
  .iso ByteArray .mk CompressedEpochSyncProof.bytes

/-- `should_use_versioned_bp_hash_format`. -/
def shouldUseVersionedBpHashFormat (v : ProtocolVersion) : Bool :=
  v ≥ 49

end Near.Node
