import NearNode.Primitives.Receipt
import NearNode.Primitives.Merkle
import NearNode.Primitives.ChunkExtra

/-!
# Chunks

`near-primitives::sharding` at `=0.37.4`: chunk headers (three header versions over six inner
versions) with their hashes, shard chunks, encoded chunks and their body, partial encoded chunks
with receipt proofs, and the state sync info.
-/

namespace Near.Node

open Borsh

/-- `ChunkHash`. -/
structure ChunkHash where
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec ChunkHash :=
  .iso CryptoHash .mk ChunkHash.hash

/-- `ChunkHashHeight`: the leaf of the block's chunk headers tree. -/
structure ChunkHashHeight where
  chunkHash : ChunkHash
  height : BlockHeight
  deriving BEq, Inhabited

instance : Codec ChunkHashHeight :=
  .iso (ChunkHash × BlockHeight) (fun (c, h) => ⟨c, h⟩) fun x => (x.chunkHash, x.height)

/-- `ShardChunkHeaderInnerV1`. -/
structure ShardChunkHeaderInnerV1 where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  prevValidatorProposals : Array ValidatorStakeV1
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV1 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      ShardId × Gas × Gas × Balance × CryptoHash × CryptoHash × Array ValidatorStakeV1)
    (fun (pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp) =>
      ⟨pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp⟩)
    fun x =>
    (x.prevBlockHash, x.prevStateRoot, x.prevOutcomeRoot, x.encodedMerkleRoot, x.encodedLength,
      x.heightCreated, x.shardId, x.prevGasUsed, x.gasLimit, x.prevBalanceBurnt,
      x.prevOutgoingReceiptsRoot, x.txRoot, x.prevValidatorProposals)

/-- `ShardChunkHeaderInnerV2`: versioned `ValidatorStake` proposals. -/
structure ShardChunkHeaderInnerV2 where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV2 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight × ShardId × Gas × Gas × Balance × CryptoHash × CryptoHash × Array ValidatorStake)
    (fun (pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp) =>
      ⟨pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp⟩)
    fun x =>
    (x.prevBlockHash, x.prevStateRoot, x.prevOutcomeRoot, x.encodedMerkleRoot, x.encodedLength,
      x.heightCreated, x.shardId, x.prevGasUsed, x.gasLimit, x.prevBalanceBurnt,
      x.prevOutgoingReceiptsRoot, x.txRoot, x.prevValidatorProposals)

/-- `ShardChunkHeaderInnerV3`: adds congestion info. -/
structure ShardChunkHeaderInnerV3 where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  congestionInfo : CongestionInfo
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV3 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      ShardId ×
      Gas × Gas × Balance × CryptoHash × CryptoHash × Array ValidatorStake × CongestionInfo)
    (fun (pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci) =>
      ⟨pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci⟩)
    fun x =>
    (x.prevBlockHash, x.prevStateRoot, x.prevOutcomeRoot, x.encodedMerkleRoot, x.encodedLength,
      x.heightCreated, x.shardId, x.prevGasUsed, x.gasLimit, x.prevBalanceBurnt,
      x.prevOutgoingReceiptsRoot, x.txRoot, x.prevValidatorProposals, x.congestionInfo)

/-- `ShardChunkHeaderInnerV4`: adds bandwidth requests. -/
structure ShardChunkHeaderInnerV4 where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  congestionInfo : CongestionInfo
  bandwidthRequests : BandwidthRequests
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV4 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      ShardId ×
      Gas ×
      Gas ×
      Balance × CryptoHash × CryptoHash × Array ValidatorStake × CongestionInfo × BandwidthRequests)
    (fun (pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci, br) =>
      ⟨pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci, br⟩)
    fun x =>
    (x.prevBlockHash, x.prevStateRoot, x.prevOutcomeRoot, x.encodedMerkleRoot, x.encodedLength,
      x.heightCreated, x.shardId, x.prevGasUsed, x.gasLimit, x.prevBalanceBurnt,
      x.prevOutgoingReceiptsRoot, x.txRoot, x.prevValidatorProposals, x.congestionInfo,
      x.bandwidthRequests)

/-- `ShardChunkHeaderInnerV5`: adds the proposed split. -/
structure ShardChunkHeaderInnerV5 where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  congestionInfo : CongestionInfo
  bandwidthRequests : BandwidthRequests
  proposedSplit : Option TrieSplit
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV5 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      CryptoHash ×
      UInt64 ×
      BlockHeight ×
      ShardId ×
      Gas ×
      Gas ×
      Balance ×
      CryptoHash ×
      CryptoHash × Array ValidatorStake × CongestionInfo × BandwidthRequests × Option TrieSplit)
    (fun (pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci, br, sp) =>
      ⟨pb, ps, po, em, el, hc, s, pg, gl, bb, or, tx, vp, ci, br, sp⟩)
    fun x =>
    (x.prevBlockHash, x.prevStateRoot, x.prevOutcomeRoot, x.encodedMerkleRoot, x.encodedLength,
      x.heightCreated, x.shardId, x.prevGasUsed, x.gasLimit, x.prevBalanceBurnt,
      x.prevOutgoingReceiptsRoot, x.txRoot, x.prevValidatorProposals, x.congestionInfo,
      x.bandwidthRequests, x.proposedSplit)

/-- `ShardChunkHeaderInnerV6SpiceTxOnly`: a spice chunk carries transactions only. -/
structure ShardChunkHeaderInnerV6 where
  prevBlockHash : CryptoHash
  encodedMerkleRoot : CryptoHash
  encodedLength : UInt64
  heightCreated : BlockHeight
  shardId : ShardId
  prevOutgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInnerV6 :=
  .iso (CryptoHash × CryptoHash × UInt64 × BlockHeight × ShardId × CryptoHash × CryptoHash)
    (fun (pb, em, el, hc, s, or, tx) => ⟨pb, em, el, hc, s, or, tx⟩) fun x =>
    (x.prevBlockHash, x.encodedMerkleRoot, x.encodedLength, x.heightCreated, x.shardId,
      x.prevOutgoingReceiptsRoot, x.txRoot)

/-- `ShardChunkHeaderInner`. -/
inductive ShardChunkHeaderInner where
  | v1 (i : ShardChunkHeaderInnerV1)
  | v2 (i : ShardChunkHeaderInnerV2)
  | v3 (i : ShardChunkHeaderInnerV3)
  | v4 (i : ShardChunkHeaderInnerV4)
  | v5 (i : ShardChunkHeaderInnerV5)
  | v6 (i : ShardChunkHeaderInnerV6)
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderInner :=
  .enum "ShardChunkHeaderInner"
    [.variant 0 ShardChunkHeaderInnerV1 .v1 fun
        | .v1 i => some i
        | _ => none,
      .variant 1 ShardChunkHeaderInnerV2 .v2 fun
        | .v2 i => some i
        | _ => none,
      .variant 2 ShardChunkHeaderInnerV3 .v3 fun
        | .v3 i => some i
        | _ => none,
      .variant 3 ShardChunkHeaderInnerV4 .v4 fun
        | .v4 i => some i
        | _ => none,
      .variant 4 ShardChunkHeaderInnerV5 .v5 fun
        | .v5 i => some i
        | _ => none,
      .variant 5 ShardChunkHeaderInnerV6 .v6 fun
        | .v6 i => some i
        | _ => none]

namespace ShardChunkHeaderInner

/-- The previous block hash. -/
def prevBlockHash : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.prevBlockHash
  | .v2 i => i.prevBlockHash
  | .v3 i => i.prevBlockHash
  | .v4 i => i.prevBlockHash
  | .v5 i => i.prevBlockHash
  | .v6 i => i.prevBlockHash

/-- The state root before the chunk; the zero hash for a transaction-only chunk (nearcore returns
a default hash there). -/
def prevStateRoot : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.prevStateRoot
  | .v2 i => i.prevStateRoot
  | .v3 i => i.prevStateRoot
  | .v4 i => i.prevStateRoot
  | .v5 i => i.prevStateRoot
  | .v6 _ => CryptoHash.zero

/-- The outcome root of the previous chunk; the zero hash for a transaction-only chunk. -/
def prevOutcomeRoot : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.prevOutcomeRoot
  | .v2 i => i.prevOutcomeRoot
  | .v3 i => i.prevOutcomeRoot
  | .v4 i => i.prevOutcomeRoot
  | .v5 i => i.prevOutcomeRoot
  | .v6 _ => CryptoHash.zero

/-- The merkle root of the encoded chunk parts. -/
def encodedMerkleRoot : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.encodedMerkleRoot
  | .v2 i => i.encodedMerkleRoot
  | .v3 i => i.encodedMerkleRoot
  | .v4 i => i.encodedMerkleRoot
  | .v5 i => i.encodedMerkleRoot
  | .v6 i => i.encodedMerkleRoot

/-- The root of the outgoing receipts of the previous chunk. -/
def prevOutgoingReceiptsRoot : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.prevOutgoingReceiptsRoot
  | .v2 i => i.prevOutgoingReceiptsRoot
  | .v3 i => i.prevOutgoingReceiptsRoot
  | .v4 i => i.prevOutgoingReceiptsRoot
  | .v5 i => i.prevOutgoingReceiptsRoot
  | .v6 i => i.prevOutgoingReceiptsRoot

/-- The transaction root. -/
def txRoot : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.txRoot
  | .v2 i => i.txRoot
  | .v3 i => i.txRoot
  | .v4 i => i.txRoot
  | .v5 i => i.txRoot
  | .v6 i => i.txRoot

/-- The height at which the chunk was created. -/
def heightCreated : ShardChunkHeaderInner → BlockHeight
  | .v1 i => i.heightCreated
  | .v2 i => i.heightCreated
  | .v3 i => i.heightCreated
  | .v4 i => i.heightCreated
  | .v5 i => i.heightCreated
  | .v6 i => i.heightCreated

/-- The shard. -/
def shardId : ShardChunkHeaderInner → ShardId
  | .v1 i => i.shardId
  | .v2 i => i.shardId
  | .v3 i => i.shardId
  | .v4 i => i.shardId
  | .v5 i => i.shardId
  | .v6 i => i.shardId

end ShardChunkHeaderInner

/-- `ShardChunkHeaderV1`: the chunk hash is the hash of the inner part only. -/
structure ShardChunkHeaderV1 where
  inner : ShardChunkHeaderInnerV1
  heightIncluded : BlockHeight
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderV1 :=
  .iso (ShardChunkHeaderInnerV1 × BlockHeight × Signature) (fun (i, h, s) => ⟨i, h, s⟩) fun x =>
    (x.inner, x.heightIncluded, x.signature)

/-- `ShardChunkHeaderV2`: the layout of V1, hashed with the encoded merkle root. -/
structure ShardChunkHeaderV2 where
  inner : ShardChunkHeaderInnerV1
  heightIncluded : BlockHeight
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderV2 :=
  .iso (ShardChunkHeaderInnerV1 × BlockHeight × Signature) (fun (i, h, s) => ⟨i, h, s⟩) fun x =>
    (x.inner, x.heightIncluded, x.signature)

/-- `ShardChunkHeaderV3`: a versioned inner part. -/
structure ShardChunkHeaderV3 where
  inner : ShardChunkHeaderInner
  heightIncluded : BlockHeight
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ShardChunkHeaderV3 :=
  .iso (ShardChunkHeaderInner × BlockHeight × Signature) (fun (i, h, s) => ⟨i, h, s⟩) fun x =>
    (x.inner, x.heightIncluded, x.signature)

/-- `ShardChunkHeaderV1::compute_hash`: the hash of the Borsh inner part. -/
def ShardChunkHeaderV1.chunkHash (h : ShardChunkHeaderV1) : ChunkHash :=
  ⟨CryptoHash.hashBorsh h.inner⟩

/-- `ShardChunkHeaderV2::compute_hash`: the inner hash combined with the encoded merkle root. -/
def ShardChunkHeaderV2.chunkHash (h : ShardChunkHeaderV2) : ChunkHash :=
  ⟨combineHash (CryptoHash.hashBorsh h.inner) h.inner.encodedMerkleRoot⟩

/-- `ShardChunkHeaderV3::compute_hash`: the hash of the tagged inner part combined with the
encoded merkle root. -/
def ShardChunkHeaderV3.chunkHash (h : ShardChunkHeaderV3) : ChunkHash :=
  ⟨combineHash (CryptoHash.hashBorsh h.inner) h.inner.encodedMerkleRoot⟩

/-- `ShardChunkHeader`. -/
inductive ShardChunkHeader where
  | v1 (h : ShardChunkHeaderV1)
  | v2 (h : ShardChunkHeaderV2)
  | v3 (h : ShardChunkHeaderV3)
  deriving BEq, Inhabited

instance : Codec ShardChunkHeader :=
  .enum "ShardChunkHeader"
    [.variant 0 ShardChunkHeaderV1 .v1 fun
        | .v1 h => some h
        | _ => none,
      .variant 1 ShardChunkHeaderV2 .v2 fun
        | .v2 h => some h
        | _ => none,
      .variant 2 ShardChunkHeaderV3 .v3 fun
        | .v3 h => some h
        | _ => none]

namespace ShardChunkHeader

/-- `ShardChunkHeader::compute_hash`: the chunk hash, which the chunk producer signs. -/
def chunkHash : ShardChunkHeader → ChunkHash
  | .v1 h => h.chunkHash
  | .v2 h => h.chunkHash
  | .v3 h => h.chunkHash

/-- `ShardChunkHeader::inner_header_hash`: the hash of the Borsh inner part. -/
def innerHeaderHash : ShardChunkHeader → CryptoHash
  | .v1 h => CryptoHash.hashBorsh h.inner
  | .v2 h => CryptoHash.hashBorsh h.inner
  | .v3 h => CryptoHash.hashBorsh h.inner

/-- The height of the block that included the chunk. -/
def heightIncluded : ShardChunkHeader → BlockHeight
  | .v1 h => h.heightIncluded
  | .v2 h => h.heightIncluded
  | .v3 h => h.heightIncluded

/-- The height at which the chunk was created. -/
def heightCreated : ShardChunkHeader → BlockHeight
  | .v1 h => h.inner.heightCreated
  | .v2 h => h.inner.heightCreated
  | .v3 h => h.inner.heightCreated

/-- The shard. -/
def shardId : ShardChunkHeader → ShardId
  | .v1 h => h.inner.shardId
  | .v2 h => h.inner.shardId
  | .v3 h => h.inner.shardId

/-- The chunk producer's signature. -/
def signature : ShardChunkHeader → Signature
  | .v1 h => h.signature
  | .v2 h => h.signature
  | .v3 h => h.signature

/-- The state root before the chunk. -/
def prevStateRoot : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.prevStateRoot
  | .v2 h => h.inner.prevStateRoot
  | .v3 h => h.inner.prevStateRoot

/-- The root of the outgoing receipts of the previous chunk. -/
def prevOutgoingReceiptsRoot : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.prevOutgoingReceiptsRoot
  | .v2 h => h.inner.prevOutgoingReceiptsRoot
  | .v3 h => h.inner.prevOutgoingReceiptsRoot

/-- The outcome root of the previous chunk. -/
def prevOutcomeRoot : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.prevOutcomeRoot
  | .v2 h => h.inner.prevOutcomeRoot
  | .v3 h => h.inner.prevOutcomeRoot

/-- The transaction root. -/
def txRoot : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.txRoot
  | .v2 h => h.inner.txRoot
  | .v3 h => h.inner.txRoot

/-- The merkle root of the encoded chunk parts. -/
def encodedMerkleRoot : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.encodedMerkleRoot
  | .v2 h => h.inner.encodedMerkleRoot
  | .v3 h => h.inner.encodedMerkleRoot

/-- `ShardChunkHeader::is_new_chunk`: whether the block at `height` included this chunk. -/
def isNewChunk (h : ShardChunkHeader) (height : BlockHeight) : Bool :=
  h.heightIncluded == height

/-- The leaf of the chunk headers tree. -/
def hashHeight (h : ShardChunkHeader) : ChunkHashHeight :=
  ⟨h.chunkHash, h.heightIncluded⟩

end ShardChunkHeader

/-- `ShardProof`. -/
structure ShardProof where
  fromShardId : ShardId
  toShardId : ShardId
  proof : Array MerklePathItem
  deriving BEq, Inhabited

instance : Codec ShardProof :=
  .iso (ShardId × ShardId × Array MerklePathItem) (fun (f, t, p) => ⟨f, t, p⟩) fun x =>
    (x.fromShardId, x.toShardId, x.proof)

/-- `ReceiptProof`: the receipts of one shard pair and the proof that they are in the receipts
root. -/
structure ReceiptProof where
  receipts : Array Receipt
  proof : ShardProof
  deriving BEq, Inhabited

instance : Codec ReceiptProof :=
  .iso (Array Receipt × ShardProof) (fun (r, p) => ⟨r, p⟩) fun x => (x.receipts, x.proof)

/-- The hash of the Borsh `ReceiptList` (the target shard, then the receipts). The proof is
checked against the hash of this hash (`verify_path` hashes its item). -/
def ReceiptProof.leafHash (p : ReceiptProof) : CryptoHash :=
  CryptoHash.hashBorsh (p.proof.toShardId, p.receipts)

/-- `ReceiptProof::verify_against_receipt_root`. -/
def ReceiptProof.verifyAgainstReceiptRoot (p : ReceiptProof) (root : CryptoHash) : Bool :=
  verifyPath root p.proof.proof p.leafHash

/-- `PartialEncodedChunkPart`. -/
structure PartialEncodedChunkPart where
  partOrd : UInt64
  part : ByteArray
  merkleProof : Array MerklePathItem
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkPart :=
  .iso (UInt64 × ByteArray × Array MerklePathItem) (fun (o, p, m) => ⟨o, p, m⟩) fun x =>
    (x.partOrd, x.part, x.merkleProof)

/-- `PartialEncodedChunkV1`. -/
structure PartialEncodedChunkV1 where
  header : ShardChunkHeaderV1
  parts : Array PartialEncodedChunkPart
  prevOutgoingReceipts : Array ReceiptProof
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkV1 :=
  .iso (ShardChunkHeaderV1 × Array PartialEncodedChunkPart × Array ReceiptProof)
    (fun (h, p, r) => ⟨h, p, r⟩) fun x => (x.header, x.parts, x.prevOutgoingReceipts)

/-- `PartialEncodedChunkV2`. -/
structure PartialEncodedChunkV2 where
  header : ShardChunkHeader
  parts : Array PartialEncodedChunkPart
  prevOutgoingReceipts : Array ReceiptProof
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkV2 :=
  .iso (ShardChunkHeader × Array PartialEncodedChunkPart × Array ReceiptProof)
    (fun (h, p, r) => ⟨h, p, r⟩) fun x => (x.header, x.parts, x.prevOutgoingReceipts)

/-- `PartialEncodedChunk`. -/
inductive PartialEncodedChunk where
  | v1 (c : PartialEncodedChunkV1)
  | v2 (c : PartialEncodedChunkV2)
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunk :=
  .enum "PartialEncodedChunk"
    [.variant 0 PartialEncodedChunkV1 .v1 fun
        | .v1 c => some c
        | _ => none,
      .variant 1 PartialEncodedChunkV2 .v2 fun
        | .v2 c => some c
        | _ => none]

/-- `PartialEncodedChunk::chunk_hash`. -/
def PartialEncodedChunk.chunkHash : PartialEncodedChunk → ChunkHash
  | .v1 c => c.header.chunkHash
  | .v2 c => c.header.chunkHash

/-- `ShardChunkV1`: the chunk hash is stored beside the header. -/
structure ShardChunkV1 where
  chunkHash : ChunkHash
  header : ShardChunkHeaderV1
  transactions : Array SignedTransaction
  prevOutgoingReceipts : Array Receipt
  deriving BEq, Inhabited

instance : Codec ShardChunkV1 :=
  .iso (ChunkHash × ShardChunkHeaderV1 × Array SignedTransaction × Array Receipt)
    (fun (c, h, t, r) => ⟨c, h, t, r⟩) fun x =>
    (x.chunkHash, x.header, x.transactions, x.prevOutgoingReceipts)

/-- `ShardChunkV2`. -/
structure ShardChunkV2 where
  chunkHash : ChunkHash
  header : ShardChunkHeader
  transactions : Array SignedTransaction
  prevOutgoingReceipts : Array Receipt
  deriving BEq, Inhabited

instance : Codec ShardChunkV2 :=
  .iso (ChunkHash × ShardChunkHeader × Array SignedTransaction × Array Receipt)
    (fun (c, h, t, r) => ⟨c, h, t, r⟩) fun x =>
    (x.chunkHash, x.header, x.transactions, x.prevOutgoingReceipts)

/-- `ShardChunk`. -/
inductive ShardChunk where
  | v1 (c : ShardChunkV1)
  | v2 (c : ShardChunkV2)
  deriving BEq, Inhabited

instance : Codec ShardChunk :=
  .enum "ShardChunk"
    [.variant 0 ShardChunkV1 .v1 fun
        | .v1 c => some c
        | _ => none,
      .variant 1 ShardChunkV2 .v2 fun
        | .v2 c => some c
        | _ => none]

/-- `ShardChunk::compute_header_hash`: the hash recomputed from the header (the stored
`chunk_hash` is not checked by the codec). -/
def ShardChunk.computeHeaderHash : ShardChunk → ChunkHash
  | .v1 c => c.header.chunkHash
  | .v2 c => c.header.chunkHash

/-- `EncodedShardChunkBody`: the Reed-Solomon parts, some of which may be missing. -/
structure EncodedShardChunkBody where
  parts : Array (Option ByteArray)
  deriving BEq, Inhabited

instance : Codec EncodedShardChunkBody :=
  .iso (Array (Option ByteArray)) .mk EncodedShardChunkBody.parts

/-- `EncodedShardChunkBody::get_merkle_hash_and_paths`: the merkle root and proofs of the parts;
nearcore panics unless every part is present, so it is `none` here. -/
def EncodedShardChunkBody.merkleHashAndPaths (b : EncodedShardChunkBody) :
    Option (CryptoHash × Array (Array MerklePathItem)) :=
  (b.parts.mapM id).map merklize

/-- `EncodedShardChunkV1`. -/
structure EncodedShardChunkV1 where
  header : ShardChunkHeaderV1
  content : EncodedShardChunkBody
  deriving BEq, Inhabited

instance : Codec EncodedShardChunkV1 :=
  .iso (ShardChunkHeaderV1 × EncodedShardChunkBody) (fun (h, c) => ⟨h, c⟩) fun x =>
    (x.header, x.content)

/-- `EncodedShardChunkV2`. -/
structure EncodedShardChunkV2 where
  header : ShardChunkHeader
  content : EncodedShardChunkBody
  deriving BEq, Inhabited

instance : Codec EncodedShardChunkV2 :=
  .iso (ShardChunkHeader × EncodedShardChunkBody) (fun (h, c) => ⟨h, c⟩) fun x =>
    (x.header, x.content)

/-- `EncodedShardChunk`. -/
inductive EncodedShardChunk where
  | v1 (c : EncodedShardChunkV1)
  | v2 (c : EncodedShardChunkV2)
  deriving BEq, Inhabited

instance : Codec EncodedShardChunk :=
  .enum "EncodedShardChunk"
    [.variant 0 EncodedShardChunkV1 .v1 fun
        | .v1 c => some c
        | _ => none,
      .variant 1 EncodedShardChunkV2 .v2 fun
        | .v2 c => some c
        | _ => none]

/-- `EncodedShardChunk::chunk_hash`. -/
def EncodedShardChunk.chunkHash : EncodedShardChunk → ChunkHash
  | .v1 c => c.header.chunkHash
  | .v2 c => c.header.chunkHash

/-- `EncodedShardChunk::content`. -/
def EncodedShardChunk.content : EncodedShardChunk → EncodedShardChunkBody
  | .v1 c => c.content
  | .v2 c => c.content

/-- `TransactionReceipt`: the payload that the encoded chunk parts carry. -/
structure TransactionReceipt where
  transactions : Array SignedTransaction
  receipts : Array Receipt
  deriving BEq, Inhabited

instance : Codec TransactionReceipt :=
  .iso (Array SignedTransaction × Array Receipt) (fun (t, r) => ⟨t, r⟩) fun x =>
    (x.transactions, x.receipts)

/-- `StateSyncInfoV0`. -/
structure StateSyncInfoV0 where
  syncHash : CryptoHash
  shards : Array ShardId
  deriving BEq, Inhabited

instance : Codec StateSyncInfoV0 :=
  .iso (CryptoHash × Array ShardId) (fun (h, s) => ⟨h, s⟩) fun x => (x.syncHash, x.shards)

/-- `StateSyncInfoV1`. -/
structure StateSyncInfoV1 where
  epochFirstBlock : CryptoHash
  syncHash : Option CryptoHash
  shards : Array ShardId
  deriving BEq, Inhabited

instance : Codec StateSyncInfoV1 :=
  .iso (CryptoHash × Option CryptoHash × Array ShardId) (fun (e, h, s) => ⟨e, h, s⟩) fun x =>
    (x.epochFirstBlock, x.syncHash, x.shards)

/-- `StateSyncInfo`. -/
inductive StateSyncInfo where
  | v0 (i : StateSyncInfoV0)
  | v1 (i : StateSyncInfoV1)
  deriving BEq, Inhabited

instance : Codec StateSyncInfo :=
  .enum "StateSyncInfo"
    [.variant 0 StateSyncInfoV0 .v0 fun
        | .v0 i => some i
        | _ => none,
      .variant 1 StateSyncInfoV1 .v1 fun
        | .v1 i => some i
        | _ => none]

/-- `PartialState`: the trie nodes that prove a state change. -/
inductive PartialState where
  | trieValues (values : Array ByteArray)
  deriving BEq, Inhabited

instance : Codec PartialState :=
  .enum "PartialState"
    [.variant 0 (Array ByteArray) .trieValues fun
        | .trieValues v => some v]

end Near.Node
