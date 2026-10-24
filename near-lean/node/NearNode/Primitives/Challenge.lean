import NearNode.Primitives.Sharding

/-!
# Challenges

`near-primitives::challenge` at `=0.37.4`. Challenges are deprecated, but old block bodies and
blocks still carry them, so the wire format stays. `Challenge::hash` is the hash of the body.
-/

namespace Near.Node

open Borsh

/-- `BlockDoubleSign`: two encoded block headers. -/
structure BlockDoubleSign where
  leftBlockHeader : ByteArray
  rightBlockHeader : ByteArray
  deriving BEq, Inhabited

instance : Codec BlockDoubleSign :=
  .iso (ByteArray × ByteArray) (fun (l, r) => ⟨l, r⟩) fun x =>
    (x.leftBlockHeader, x.rightBlockHeader)

/-- `MaybeEncodedShardChunk`. -/
inductive MaybeEncodedShardChunk where
  | encoded (c : EncodedShardChunk)
  | decoded (c : ShardChunk)
  deriving BEq, Inhabited

instance : Codec MaybeEncodedShardChunk :=
  .enum "MaybeEncodedShardChunk"
    [.variant 0 EncodedShardChunk .encoded fun
        | .encoded c => some c
        | _ => none,
      .variant 1 ShardChunk .decoded fun
        | .decoded c => some c
        | _ => none]

/-- `ChunkProofs`. -/
structure ChunkProofs where
  blockHeader : ByteArray
  merkleProof : Array MerklePathItem
  chunk : MaybeEncodedShardChunk
  deriving BEq, Inhabited

instance : Codec ChunkProofs :=
  .iso (ByteArray × Array MerklePathItem × MaybeEncodedShardChunk) (fun (b, m, c) => ⟨b, m, c⟩)
    fun x => (x.blockHeader, x.merkleProof, x.chunk)

/-- `ChunkState`. -/
structure ChunkState where
  prevBlockHeader : ByteArray
  blockHeight : BlockHeight
  prevMerkleProof : Array MerklePathItem
  prevChunk : ShardChunk
  merkleProof : Array MerklePathItem
  chunkHeader : ShardChunkHeader
  partialState : PartialState
  deriving BEq, Inhabited

instance : Codec ChunkState :=
  .iso
    (ByteArray ×
      BlockHeight ×
      Array MerklePathItem × ShardChunk × Array MerklePathItem × ShardChunkHeader × PartialState)
    (fun (b, h, p, c, m, ch, s) => ⟨b, h, p, c, m, ch, s⟩) fun x =>
    (x.prevBlockHeader, x.blockHeight, x.prevMerkleProof, x.prevChunk, x.merkleProof, x.chunkHeader,
      x.partialState)

/-- `ChallengeBody`. -/
inductive ChallengeBody where
  | blockDoubleSign (b : BlockDoubleSign)
  | chunkProofs (c : ChunkProofs)
  | chunkState (c : ChunkState)
  deriving BEq, Inhabited

instance : Codec ChallengeBody :=
  .enum "ChallengeBody"
    [.variant 0 BlockDoubleSign .blockDoubleSign fun
        | .blockDoubleSign b => some b
        | _ => none,
      .variant 1 ChunkProofs .chunkProofs fun
        | .chunkProofs c => some c
        | _ => none,
      .variant 2 ChunkState .chunkState fun
        | .chunkState c => some c
        | _ => none]

/-- `Challenge`. -/
structure Challenge where
  body : ChallengeBody
  accountId : AccountId
  signature : Signature
  deriving BEq, Inhabited

instance : Codec Challenge :=
  .iso (ChallengeBody × AccountId × Signature) (fun (b, a, s) => ⟨b, a, s⟩) fun x =>
    (x.body, x.accountId, x.signature)

/-- `Challenge::init`: the hash of the body. -/
def Challenge.hash (c : Challenge) : CryptoHash :=
  CryptoHash.hashBorsh c.body

end Near.Node
