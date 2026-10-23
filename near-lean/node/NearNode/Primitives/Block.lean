import NearNode.Primitives.BlockHeader
import NearNode.Primitives.Challenge
import NearNode.Primitives.Spice

/-!
# Blocks

`near-primitives::block`, `block_body` and `optimistic_block` at `=0.37.4`: the four block versions,
the three block body versions, the roots a header commits to (computed from the chunk headers with
`merklize`), `check_validity`, `Tip` and the optimistic block.
-/

namespace Near.Node

open Borsh

/-- `near_crypto::vrf::Value`: 32 bytes. -/
structure VrfValue where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec VrfValue :=
  .isoOf (.fixed 32) .mk VrfValue.bytes

/-- `near_crypto::vrf::Proof`: 64 bytes. -/
structure VrfProof where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec VrfProof :=
  .isoOf (.fixed 64) .mk VrfProof.bytes

/-- `BlockBodyV1`. -/
structure BlockBodyV1 where
  chunks : Array ShardChunkHeader
  challenges : Array Challenge
  vrfValue : VrfValue
  vrfProof : VrfProof
  deriving BEq, Inhabited

instance : Codec BlockBodyV1 :=
  .iso (Array ShardChunkHeader × Array Challenge × VrfValue × VrfProof)
    (fun (c, h, v, p) => ⟨c, h, v, p⟩) fun x => (x.chunks, x.challenges, x.vrfValue, x.vrfProof)

/-- `BlockBodyV2`: adds the chunk endorsement signatures of every shard. -/
structure BlockBodyV2 where
  chunks : Array ShardChunkHeader
  challenges : Array Challenge
  vrfValue : VrfValue
  vrfProof : VrfProof
  chunkEndorsements : Array (Array (Option Signature))
  deriving BEq, Inhabited

instance : Codec BlockBodyV2 :=
  .iso
    (Array ShardChunkHeader ×
      Array Challenge × VrfValue × VrfProof × Array (Array (Option Signature)))
    (fun (c, h, v, p, e) => ⟨c, h, v, p, e⟩) fun x =>
    (x.chunks, x.challenges, x.vrfValue, x.vrfProof, x.chunkEndorsements)

/-- `SpiceBlockBodyV3`: core statements replace endorsements and challenges. -/
structure SpiceBlockBodyV3 where
  chunks : Array ShardChunkHeader
  vrfValue : VrfValue
  vrfProof : VrfProof
  coreStatements : SpiceCoreStatements
  deriving BEq, Inhabited

instance : Codec SpiceBlockBodyV3 :=
  .iso (Array ShardChunkHeader × VrfValue × VrfProof × SpiceCoreStatements)
    (fun (c, v, p, s) => ⟨c, v, p, s⟩) fun x => (x.chunks, x.vrfValue, x.vrfProof, x.coreStatements)

/-- `BlockBody`. -/
inductive BlockBody where
  | v1 (b : BlockBodyV1)
  | v2 (b : BlockBodyV2)
  | v3 (b : SpiceBlockBodyV3)
  deriving BEq, Inhabited

instance : Codec BlockBody :=
  .enum "BlockBody"
    [.variant 0 BlockBodyV1 .v1 fun
        | .v1 b => some b
        | _ => none,
      .variant 1 BlockBodyV2 .v2 fun
        | .v2 b => some b
        | _ => none,
      .variant 2 SpiceBlockBodyV3 .v3 fun
        | .v3 b => some b
        | _ => none]

namespace BlockBody

/-- The chunk headers. -/
def chunks : BlockBody → Array ShardChunkHeader
  | .v1 b => b.chunks
  | .v2 b => b.chunks
  | .v3 b => b.chunks

/-- `BlockBody::compute_hash`: V1 hashes the bare struct, later versions the tagged enum. -/
def computeHash : BlockBody → CryptoHash
  | .v1 b => CryptoHash.hashBorsh b
  | b@(.v2 _) => CryptoHash.hashBorsh b
  | b@(.v3 _) => CryptoHash.hashBorsh b

end BlockBody

/-- `BlockV1`: chunk headers of the first version, in the block itself. -/
structure BlockV1 where
  header : BlockHeader
  chunks : Array ShardChunkHeaderV1
  challenges : Array Challenge
  vrfValue : VrfValue
  vrfProof : VrfProof
  deriving BEq, Inhabited

instance : Codec BlockV1 :=
  .iso (BlockHeader × Array ShardChunkHeaderV1 × Array Challenge × VrfValue × VrfProof)
    (fun (h, c, ch, v, p) => ⟨h, c, ch, v, p⟩) fun x =>
    (x.header, x.chunks, x.challenges, x.vrfValue, x.vrfProof)

/-- `BlockV2`: versioned chunk headers. -/
structure BlockV2 where
  header : BlockHeader
  chunks : Array ShardChunkHeader
  challenges : Array Challenge
  vrfValue : VrfValue
  vrfProof : VrfProof
  deriving BEq, Inhabited

instance : Codec BlockV2 :=
  .iso (BlockHeader × Array ShardChunkHeader × Array Challenge × VrfValue × VrfProof)
    (fun (h, c, ch, v, p) => ⟨h, c, ch, v, p⟩) fun x =>
    (x.header, x.chunks, x.challenges, x.vrfValue, x.vrfProof)

/-- `BlockV3`: a header and a `BlockBodyV1`. -/
structure BlockV3 where
  header : BlockHeader
  body : BlockBodyV1
  deriving BEq, Inhabited

instance : Codec BlockV3 :=
  .iso (BlockHeader × BlockBodyV1) (fun (h, b) => ⟨h, b⟩) fun x => (x.header, x.body)

/-- `BlockV4`: a header and a versioned body. -/
structure BlockV4 where
  header : BlockHeader
  body : BlockBody
  deriving BEq, Inhabited

instance : Codec BlockV4 :=
  .iso (BlockHeader × BlockBody) (fun (h, b) => ⟨h, b⟩) fun x => (x.header, x.body)

/-- `Block`. -/
inductive Block where
  | v1 (b : BlockV1)
  | v2 (b : BlockV2)
  | v3 (b : BlockV3)
  | v4 (b : BlockV4)
  deriving BEq, Inhabited

instance : Codec Block :=
  .enum "Block"
    [.variant 0 BlockV1 .v1 fun
        | .v1 b => some b
        | _ => none,
      .variant 1 BlockV2 .v2 fun
        | .v2 b => some b
        | _ => none,
      .variant 2 BlockV3 .v3 fun
        | .v3 b => some b
        | _ => none,
      .variant 3 BlockV4 .v4 fun
        | .v4 b => some b
        | _ => none]

/-- `BlockValidityError`. -/
inductive BlockValidityError where
  | invalidStateRoot
  | invalidReceiptRoot
  | invalidChunkHeaderRoot
  | invalidTransactionRoot
  | invalidChunkMask
  deriving BEq, Inhabited

/-- A number for each outcome of `check_validity`: 0 for a valid block, then the variants in order. -/
def BlockValidityError.code : Option BlockValidityError → UInt8
  | none => 0
  | some .invalidStateRoot => 1
  | some .invalidReceiptRoot => 2
  | some .invalidChunkHeaderRoot => 3
  | some .invalidTransactionRoot => 4
  | some .invalidChunkMask => 5

namespace Block

/-- The block header. -/
def header : Block → BlockHeader
  | .v1 b => b.header
  | .v2 b => b.header
  | .v3 b => b.header
  | .v4 b => b.header

/-- The block hash. -/
def hash (b : Block) : CryptoHash :=
  b.header.hash

/-- `Block::chunks`: the chunk headers, V1 headers lifted. -/
def chunks : Block → Array ShardChunkHeader
  | .v1 b => b.chunks.map .v1
  | .v2 b => b.chunks
  | .v3 b => b.body.chunks
  | .v4 b => b.body.chunks

/-- `Block::is_spice_block`. -/
def isSpiceBlock : Block → Bool
  | .v4 ⟨_, .v3 _⟩ => true
  | _ => false

/-- `Block::compute_block_body_hash`: none before V3. -/
def computeBlockBodyHash : Block → Option CryptoHash
  | .v1 _ | .v2 _ => none
  | .v3 b => some (BlockBody.v1 b.body).computeHash
  | .v4 b => some b.body.computeHash

/-- `Chunks::compute_state_root`. -/
def computeStateRoot (b : Block) : CryptoHash :=
  (merklize (b.chunks.map ShardChunkHeader.prevStateRoot)).1

/-- `Chunks::compute_chunk_prev_outgoing_receipts_root`. -/
def computeChunkPrevOutgoingReceiptsRoot (b : Block) : CryptoHash :=
  (merklize (b.chunks.map ShardChunkHeader.prevOutgoingReceiptsRoot)).1

/-- `Chunks::compute_chunk_headers_root`: the root and the proof of every chunk. -/
def computeChunkHeadersRoot (b : Block) : CryptoHash × Array (Array MerklePathItem) :=
  merklize (b.chunks.map ShardChunkHeader.hashHeight)

/-- `Chunks::compute_chunk_tx_root`. -/
def computeChunkTxRoot (b : Block) : CryptoHash :=
  (merklize (b.chunks.map ShardChunkHeader.txRoot)).1

/-- `Chunks::compute_outcome_root`. -/
def computeOutcomeRoot (b : Block) : CryptoHash :=
  (merklize (b.chunks.map ShardChunkHeader.prevOutcomeRoot)).1

/-- `Block::check_validity`: the header's roots and chunk mask against the chunk headers. The
outcome root reports `InvalidTransactionRoot`, as in nearcore. -/
def checkValidity (b : Block) : Option BlockValidityError :=
  let h := b.header
  if !b.isSpiceBlock && h.innerLite.prevStateRoot != b.computeStateRoot then some .invalidStateRoot
  else
    if h.prevChunkOutgoingReceiptsRoot != b.computeChunkPrevOutgoingReceiptsRoot then
      some .invalidReceiptRoot
    else
      if h.chunkHeadersRoot != b.computeChunkHeadersRoot.1 then some .invalidChunkHeaderRoot
      else
        if h.chunkTxRoot != b.computeChunkTxRoot then some .invalidTransactionRoot
        else
          if h.innerLite.prevOutcomeRoot != b.computeOutcomeRoot then some .invalidTransactionRoot
          else
            if h.chunkMask != b.chunks.map (·.isNewChunk h.height) then some .invalidChunkMask
            else none

end Block

/-- `Tip`. -/
structure Tip where
  height : BlockHeight
  lastBlockHash : CryptoHash
  prevBlockHash : CryptoHash
  epochId : EpochId
  nextEpochId : EpochId
  deriving BEq, Inhabited

instance : Codec Tip :=
  .iso (BlockHeight × CryptoHash × CryptoHash × EpochId × EpochId)
    (fun (h, l, p, e, n) => ⟨h, l, p, e, n⟩) fun x =>
    (x.height, x.lastBlockHash, x.prevBlockHash, x.epochId, x.nextEpochId)

/-- `OptimisticBlockInner`. -/
structure OptimisticBlockInner where
  prevBlockHash : CryptoHash
  blockHeight : BlockHeight
  blockTimestamp : UInt64
  randomValue : CryptoHash
  vrfValue : VrfValue
  vrfProof : VrfProof
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec OptimisticBlockInner :=
  .iso (CryptoHash × BlockHeight × UInt64 × CryptoHash × VrfValue × VrfProof × String)
    (fun (p, h, t, r, v, f, s) => ⟨p, h, t, r, v, f, s⟩) fun x =>
    (x.prevBlockHash, x.blockHeight, x.blockTimestamp, x.randomValue, x.vrfValue, x.vrfProof,
      x.signatureDifferentiator)

/-- `OptimisticBlock`. -/
structure OptimisticBlock where
  inner : OptimisticBlockInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec OptimisticBlock :=
  .iso (OptimisticBlockInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x => (x.inner, x.signature)

/-- `OptimisticBlock::init`: the hash of the inner part, which the producer signs. -/
def OptimisticBlock.hash (b : OptimisticBlock) : CryptoHash :=
  CryptoHash.hashBorsh b.inner

end Near.Node
