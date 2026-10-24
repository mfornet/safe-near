import NearNode.Primitives.Validator
import NearNode.Primitives.Merkle

/-!
# Block headers

`near-primitives::block_header` at `=0.37.4`: `BlockHeaderInnerLite`, `BlockHeaderInnerRest` V1
to V7, `BlockHeader` V1 to V7 and the block hash. The cached `hash` of a header is not on the wire;
it is `combine_hash(combine_hash(sha256(inner_lite), sha256(inner_rest)), prev_hash)` computed from
the Borsh encodings, for every version. The block producer signs this hash.
-/

namespace Near.Node

open Borsh

/-- `ChunkEndorsementsBitmap`: one bitmap (little-endian bit order within each byte) per shard. -/
structure ChunkEndorsementsBitmap where
  inner : Array ByteArray
  deriving BEq, Inhabited

instance : Codec ChunkEndorsementsBitmap :=
  .iso (Array ByteArray) .mk ChunkEndorsementsBitmap.inner

/-- `BlockHeaderInnerLite`: the part of a header that light clients receive. -/
structure BlockHeaderInnerLite where
  height : BlockHeight
  epochId : EpochId
  nextEpochId : EpochId
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  timestamp : UInt64
  nextBpHash : CryptoHash
  blockMerkleRoot : CryptoHash
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerLite :=
  .iso
    (BlockHeight × EpochId × EpochId × CryptoHash × CryptoHash × UInt64 × CryptoHash × CryptoHash)
    (fun (h, e, n, s, o, t, b, m) => ⟨h, e, n, s, o, t, b, m⟩) fun x =>
    (x.height, x.epochId, x.nextEpochId, x.prevStateRoot, x.prevOutcomeRoot, x.timestamp,
      x.nextBpHash, x.blockMerkleRoot)

/-- `BlockHeaderInnerRest` (V1). `challengesRoot` and `challengesResult` are deprecated but still
encoded. -/
structure BlockHeaderInnerRestV1 where
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  chunksIncluded : UInt64
  challengesRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStakeV1
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  challengesResult : Array SlashedValidator
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV1 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStakeV1 ×
      Array Bool ×
      Balance ×
      Balance ×
      Array SlashedValidator × CryptoHash × CryptoHash × Array (Option Signature) × ProtocolVersion)
    (fun (r, h, t, i, c, v, p, m, g, s, cr, f, d, a, l) =>
      ⟨r, h, t, i, c, v, p, m, g, s, cr, f, d, a, l⟩)
    fun x =>
    (x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot, x.chunksIncluded,
      x.challengesRoot, x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice,
      x.totalSupply, x.challengesResult, x.lastFinalBlock, x.lastDsFinalBlock, x.approvals,
      x.latestProtocolVersion)

/-- `BlockHeaderInnerRestV2`: V1 without `chunks_included`. -/
structure BlockHeaderInnerRestV2 where
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  challengesRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStakeV1
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  challengesResult : Array SlashedValidator
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV2 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStakeV1 ×
      Array Bool ×
      Balance ×
      Balance ×
      Array SlashedValidator × CryptoHash × CryptoHash × Array (Option Signature) × ProtocolVersion)
    (fun (r, h, t, c, v, p, m, g, s, cr, f, d, a, l) => ⟨r, h, t, c, v, p, m, g, s, cr, f, d, a, l⟩)
    fun x =>
    (x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot, x.challengesRoot,
      x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice, x.totalSupply,
      x.challengesResult, x.lastFinalBlock, x.lastDsFinalBlock, x.approvals,
      x.latestProtocolVersion)

/-- `BlockHeaderInnerRestV3`: versioned `ValidatorStake`, block ordinal, previous height and the
epoch sync data hash. -/
structure BlockHeaderInnerRestV3 where
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  challengesRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  challengesResult : Array SlashedValidator
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV3 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Array Bool ×
      Balance ×
      Balance ×
      Array SlashedValidator ×
      CryptoHash ×
      CryptoHash ×
      UInt64 × BlockHeight × Option CryptoHash × Array (Option Signature) × ProtocolVersion)
    (fun (r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l) =>
      ⟨r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l⟩)
    fun x =>
    (x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot, x.challengesRoot,
      x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice, x.totalSupply,
      x.challengesResult, x.lastFinalBlock, x.lastDsFinalBlock, x.blockOrdinal, x.prevHeight,
      x.epochSyncDataHash, x.approvals, x.latestProtocolVersion)

/-- `BlockHeaderInnerRestV4`: V3 with the block body hash first. -/
structure BlockHeaderInnerRestV4 where
  blockBodyHash : CryptoHash
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  challengesRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  challengesResult : Array SlashedValidator
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV4 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Array Bool ×
      Balance ×
      Balance ×
      Array SlashedValidator ×
      CryptoHash ×
      CryptoHash ×
      UInt64 × BlockHeight × Option CryptoHash × Array (Option Signature) × ProtocolVersion)
    (fun (bb, r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l) =>
      ⟨bb, r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l⟩)
    fun x =>
    (x.blockBodyHash, x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot,
      x.challengesRoot, x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice,
      x.totalSupply, x.challengesResult, x.lastFinalBlock, x.lastDsFinalBlock, x.blockOrdinal,
      x.prevHeight, x.epochSyncDataHash, x.approvals, x.latestProtocolVersion)

/-- `BlockHeaderInnerRestV5`: V4 with the chunk endorsements bitmap last. -/
structure BlockHeaderInnerRestV5 where
  blockBodyHash : CryptoHash
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  challengesRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  challengesResult : Array SlashedValidator
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  chunkEndorsements : ChunkEndorsementsBitmap
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV5 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Array Bool ×
      Balance ×
      Balance ×
      Array SlashedValidator ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      Option CryptoHash × Array (Option Signature) × ProtocolVersion × ChunkEndorsementsBitmap)
    (fun (bb, r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l, ce) =>
      ⟨bb, r, h, t, c, v, p, m, g, s, cr, f, d, o, ph, es, a, l, ce⟩)
    fun x =>
    (x.blockBodyHash, x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot,
      x.challengesRoot, x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice,
      x.totalSupply, x.challengesResult, x.lastFinalBlock, x.lastDsFinalBlock, x.blockOrdinal,
      x.prevHeight, x.epochSyncDataHash, x.approvals, x.latestProtocolVersion, x.chunkEndorsements)

/-- `BlockHeaderInnerRestV6`: V5 without challenges, with the shard split. -/
structure BlockHeaderInnerRestV6 where
  blockBodyHash : CryptoHash
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  chunkEndorsements : ChunkEndorsementsBitmap
  shardSplit : Option (ShardId × AccountId)
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV6 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Array Bool ×
      Balance ×
      Balance ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      Option CryptoHash ×
      Array (Option Signature) ×
      ProtocolVersion × ChunkEndorsementsBitmap × Option (ShardId × AccountId))
    (fun (bb, r, h, t, v, p, m, g, s, f, d, o, ph, es, a, l, ce, sp) =>
      ⟨bb, r, h, t, v, p, m, g, s, f, d, o, ph, es, a, l, ce, sp⟩)
    fun x =>
    (x.blockBodyHash, x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot,
      x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice, x.totalSupply,
      x.lastFinalBlock, x.lastDsFinalBlock, x.blockOrdinal, x.prevHeight, x.epochSyncDataHash,
      x.approvals, x.latestProtocolVersion, x.chunkEndorsements, x.shardSplit)

/-- `BlockHeaderInnerRestV7`: V6 with the spice fields. -/
structure BlockHeaderInnerRestV7 where
  blockBodyHash : CryptoHash
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  chunkEndorsements : ChunkEndorsementsBitmap
  shardSplit : Option (ShardId × AccountId)
  prevLastCertifiedBlockEpochId : EpochId
  spiceChunkEndorsementStats : Array SpiceChunkEndorsementStats
  deriving BEq, Inhabited

instance : Codec BlockHeaderInnerRestV7 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Array Bool ×
      Balance ×
      Balance ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      Option CryptoHash ×
      Array (Option Signature) ×
      ProtocolVersion ×
      ChunkEndorsementsBitmap ×
      Option (ShardId × AccountId) × EpochId × Array SpiceChunkEndorsementStats)
    (fun (bb, r, h, t, v, p, m, g, s, f, d, o, ph, es, a, l, ce, sp, pe, st) =>
      ⟨bb, r, h, t, v, p, m, g, s, f, d, o, ph, es, a, l, ce, sp, pe, st⟩)
    fun x =>
    (x.blockBodyHash, x.prevChunkOutgoingReceiptsRoot, x.chunkHeadersRoot, x.chunkTxRoot,
      x.randomValue, x.prevValidatorProposals, x.chunkMask, x.nextGasPrice, x.totalSupply,
      x.lastFinalBlock, x.lastDsFinalBlock, x.blockOrdinal, x.prevHeight, x.epochSyncDataHash,
      x.approvals, x.latestProtocolVersion, x.chunkEndorsements, x.shardSplit,
      x.prevLastCertifiedBlockEpochId, x.spiceChunkEndorsementStats)

/-- `BlockHeader::compute_inner_hash`: combine the hashes of the two inner encodings. -/
def computeInnerHash [Codec ρ] (lite : BlockHeaderInnerLite) (rest : ρ) : CryptoHash :=
  combineHash (CryptoHash.hashBorsh lite) (CryptoHash.hashBorsh rest)

/-- `BlockHeader::compute_hash`: the block hash. -/
def computeBlockHash [Codec ρ] (prevHash : CryptoHash) (lite : BlockHeaderInnerLite) (rest : ρ) :
    CryptoHash :=
  combineHash (computeInnerHash lite rest) prevHash

/-- `BlockHeaderV1`. -/
structure BlockHeaderV1 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV1
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV1 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV1 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV2`. -/
structure BlockHeaderV2 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV2
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV2 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV2 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV3`. -/
structure BlockHeaderV3 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV3
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV3 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV3 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV4`. -/
structure BlockHeaderV4 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV4
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV4 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV4 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV5`. -/
structure BlockHeaderV5 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV5
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV5 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV5 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV6`. -/
structure BlockHeaderV6 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV6
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV6 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV6 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeaderV7`. -/
structure BlockHeaderV7 where
  prevHash : CryptoHash
  innerLite : BlockHeaderInnerLite
  innerRest : BlockHeaderInnerRestV7
  signature : Signature
  deriving BEq, Inhabited

instance : Codec BlockHeaderV7 :=
  .iso (CryptoHash × BlockHeaderInnerLite × BlockHeaderInnerRestV7 × Signature)
    (fun (p, l, r, s) => ⟨p, l, r, s⟩) fun x => (x.prevHash, x.innerLite, x.innerRest, x.signature)

/-- `BlockHeader`. -/
inductive BlockHeader where
  | v1 (h : BlockHeaderV1)
  | v2 (h : BlockHeaderV2)
  | v3 (h : BlockHeaderV3)
  | v4 (h : BlockHeaderV4)
  | v5 (h : BlockHeaderV5)
  | v6 (h : BlockHeaderV6)
  | v7 (h : BlockHeaderV7)
  deriving BEq, Inhabited

instance : Codec BlockHeader :=
  .enum "BlockHeader"
    [.variant 0 BlockHeaderV1 .v1 fun
        | .v1 h => some h
        | _ => none,
      .variant 1 BlockHeaderV2 .v2 fun
        | .v2 h => some h
        | _ => none,
      .variant 2 BlockHeaderV3 .v3 fun
        | .v3 h => some h
        | _ => none,
      .variant 3 BlockHeaderV4 .v4 fun
        | .v4 h => some h
        | _ => none,
      .variant 4 BlockHeaderV5 .v5 fun
        | .v5 h => some h
        | _ => none,
      .variant 5 BlockHeaderV6 .v6 fun
        | .v6 h => some h
        | _ => none,
      .variant 6 BlockHeaderV7 .v7 fun
        | .v7 h => some h
        | _ => none]

namespace BlockHeader

/-- The hash of the previous block. -/
def prevHash : BlockHeader → CryptoHash
  | .v1 h => h.prevHash
  | .v2 h => h.prevHash
  | .v3 h => h.prevHash
  | .v4 h => h.prevHash
  | .v5 h => h.prevHash
  | .v6 h => h.prevHash
  | .v7 h => h.prevHash

/-- The lite inner part. -/
def innerLite : BlockHeader → BlockHeaderInnerLite
  | .v1 h => h.innerLite
  | .v2 h => h.innerLite
  | .v3 h => h.innerLite
  | .v4 h => h.innerLite
  | .v5 h => h.innerLite
  | .v6 h => h.innerLite
  | .v7 h => h.innerLite

/-- The block producer's signature of the block hash. -/
def signature : BlockHeader → Signature
  | .v1 h => h.signature
  | .v2 h => h.signature
  | .v3 h => h.signature
  | .v4 h => h.signature
  | .v5 h => h.signature
  | .v6 h => h.signature
  | .v7 h => h.signature

/-- `BlockHeader::compute_inner_hash`. -/
def innerHash : BlockHeader → CryptoHash
  | .v1 h => computeInnerHash h.innerLite h.innerRest
  | .v2 h => computeInnerHash h.innerLite h.innerRest
  | .v3 h => computeInnerHash h.innerLite h.innerRest
  | .v4 h => computeInnerHash h.innerLite h.innerRest
  | .v5 h => computeInnerHash h.innerLite h.innerRest
  | .v6 h => computeInnerHash h.innerLite h.innerRest
  | .v7 h => computeInnerHash h.innerLite h.innerRest

/-- The block hash (`BlockHeader::hash`): computed from the header, since it is not on the wire. -/
def hash (h : BlockHeader) : CryptoHash :=
  combineHash h.innerHash h.prevHash

/-- The height of the block. -/
def height (h : BlockHeader) : BlockHeight :=
  h.innerLite.height

/-- The root of the previous chunks' outgoing receipts. -/
def prevChunkOutgoingReceiptsRoot : BlockHeader → CryptoHash
  | .v1 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v2 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v3 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v4 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v5 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v6 h => h.innerRest.prevChunkOutgoingReceiptsRoot
  | .v7 h => h.innerRest.prevChunkOutgoingReceiptsRoot

/-- The root of the chunk headers tree. -/
def chunkHeadersRoot : BlockHeader → CryptoHash
  | .v1 h => h.innerRest.chunkHeadersRoot
  | .v2 h => h.innerRest.chunkHeadersRoot
  | .v3 h => h.innerRest.chunkHeadersRoot
  | .v4 h => h.innerRest.chunkHeadersRoot
  | .v5 h => h.innerRest.chunkHeadersRoot
  | .v6 h => h.innerRest.chunkHeadersRoot
  | .v7 h => h.innerRest.chunkHeadersRoot

/-- The root of the chunk transaction roots. -/
def chunkTxRoot : BlockHeader → CryptoHash
  | .v1 h => h.innerRest.chunkTxRoot
  | .v2 h => h.innerRest.chunkTxRoot
  | .v3 h => h.innerRest.chunkTxRoot
  | .v4 h => h.innerRest.chunkTxRoot
  | .v5 h => h.innerRest.chunkTxRoot
  | .v6 h => h.innerRest.chunkTxRoot
  | .v7 h => h.innerRest.chunkTxRoot

/-- Which chunks are new in this block. -/
def chunkMask : BlockHeader → Array Bool
  | .v1 h => h.innerRest.chunkMask
  | .v2 h => h.innerRest.chunkMask
  | .v3 h => h.innerRest.chunkMask
  | .v4 h => h.innerRest.chunkMask
  | .v5 h => h.innerRest.chunkMask
  | .v6 h => h.innerRest.chunkMask
  | .v7 h => h.innerRest.chunkMask

/-- The approvals the block includes. -/
def approvals : BlockHeader → Array (Option Signature)
  | .v1 h => h.innerRest.approvals
  | .v2 h => h.innerRest.approvals
  | .v3 h => h.innerRest.approvals
  | .v4 h => h.innerRest.approvals
  | .v5 h => h.innerRest.approvals
  | .v6 h => h.innerRest.approvals
  | .v7 h => h.innerRest.approvals

/-- `BlockHeader::block_body_hash`: V4 and later. -/
def blockBodyHash : BlockHeader → Option CryptoHash
  | .v1 _ | .v2 _ | .v3 _ => none
  | .v4 h => some h.innerRest.blockBodyHash
  | .v5 h => some h.innerRest.blockBodyHash
  | .v6 h => some h.innerRest.blockBodyHash
  | .v7 h => some h.innerRest.blockBodyHash

end BlockHeader

end Near.Node
