import NearNode.Primitives
import NearNode.Chain.Apply
import NearNode.Validator.ReedSolomon
import NearNode.Validator.Signer

/-!
# Producing a chunk

`ShardChunkWithEncoding::new` and the helpers around it (`core/primitives/src/sharding.rs`,
`chain/chain/src/chain.rs`):

* the body is the Borsh `TransactionReceipt(transactions, outgoing receipts)`, Reed-Solomon encoded
  into the parts (`reed_solomon_encode`), whose merkle root and paths are `get_merkle_hash_and_paths`
  (the parts hashed as Borsh byte strings);
* the header is `ShardChunkHeaderV3` over the inner part of the protocol (`V5` from protocol 85,
  `DynamicResharding`; `V4` before), signed by the producer's validator key over the chunk hash,
  with `height_included` 0;
* `create_receipts_proofs_from_outgoing_receipts` groups the outgoing receipts by receiving shard and
  proves each group against `prev_outgoing_receipts_root`;
* `create_partial_encoded_chunk` selects parts by ordinal with their merkle paths.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Borsh Near.Node.ReedSolomon

/-- The facts a chunk header carries about the state before the chunk (a `ChunkExtra`) and the
chunk's contents. -/
structure ChunkInputs where
  prevBlockHash : CryptoHash
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  height : BlockHeight
  shardId : ShardId
  prevGasUsed : Gas
  gasLimit : Gas
  prevBalanceBurnt : Balance
  prevValidatorProposals : Array ValidatorStake
  transactions : Array SignedTransaction
  outgoingReceipts : Array Receipt
  outgoingReceiptsRoot : CryptoHash
  txRoot : CryptoHash
  congestionInfo : CongestionInfo
  bandwidthRequests : BandwidthRequests
  proposedSplit : Option TrieSplit := none
  deriving Inhabited

/-- `ShardChunkHeaderV3::new`: the inner part of the protocol, its hash and the signature. -/
def newChunkHeader (signer : Signer) (protocolVersion : Nat) (i : ChunkInputs)
    (encodedMerkleRoot : CryptoHash) (encodedLength : UInt64) : ShardChunkHeader :=
  let inner : ShardChunkHeaderInner :=
    if protocolVersion ≥ 85 then
      .v5
        { prevBlockHash := i.prevBlockHash, prevStateRoot := i.prevStateRoot,
          prevOutcomeRoot := i.prevOutcomeRoot, encodedMerkleRoot, encodedLength,
          heightCreated := i.height, shardId := i.shardId, prevGasUsed := i.prevGasUsed,
          gasLimit := i.gasLimit, prevBalanceBurnt := i.prevBalanceBurnt,
          prevOutgoingReceiptsRoot := i.outgoingReceiptsRoot, txRoot := i.txRoot,
          prevValidatorProposals := i.prevValidatorProposals, congestionInfo := i.congestionInfo,
          bandwidthRequests := i.bandwidthRequests, proposedSplit := i.proposedSplit }
    else
      .v4
        { prevBlockHash := i.prevBlockHash, prevStateRoot := i.prevStateRoot,
          prevOutcomeRoot := i.prevOutcomeRoot, encodedMerkleRoot, encodedLength,
          heightCreated := i.height, shardId := i.shardId, prevGasUsed := i.prevGasUsed,
          gasLimit := i.gasLimit, prevBalanceBurnt := i.prevBalanceBurnt,
          prevOutgoingReceiptsRoot := i.outgoingReceiptsRoot, txRoot := i.txRoot,
          prevValidatorProposals := i.prevValidatorProposals, congestionInfo := i.congestionInfo,
          bandwidthRequests := i.bandwidthRequests }
  let hash := combineHash (CryptoHash.hashBorsh inner) inner.encodedMerkleRoot
  .v3 { inner, heightIncluded := 0, signature := signer.sign hash.bytes }

/-- A produced chunk: the decoded chunk, its encoding and the merkle path of every part. -/
structure Produced where
  chunk : ShardChunk
  encoded : EncodedShardChunk
  paths : Array (Array MerklePathItem)

/-- `ShardChunkWithEncoding::new`. -/
def produceChunk (signer : Signer) (protocolVersion : Nat) (rs : Code) (i : ChunkInputs) :
    Except String Produced := do
  let body := Codec.encode (TransactionReceipt.mk i.transactions i.outgoingReceipts)
  let encoded ← encodeBytes rs body
  let parts := encoded.1
  let encodedLength := encoded.2
  let content : EncodedShardChunkBody := ⟨parts.map some⟩
  let some (root, paths) := content.merkleHashAndPaths | throw "a part is missing"
  let header := newChunkHeader signer protocolVersion i root encodedLength.toUInt64
  let hash := header.chunkHash
  pure
      {
        chunk :=
          .v2
            { chunkHash := hash, header, transactions := i.transactions,
              prevOutgoingReceipts := i.outgoingReceipts },
        encoded := .v2 ⟨header, content⟩, paths }

/-- `Chain::build_receipts_hashes` over typed receipts. -/
def receiptsHashes (layout : ShardLayout) (receipts : Array Receipt) :
    Except String (Array CryptoHash) := do
  let groups ← Apply.groupByShard layout (receipts.map Codec.encode)
  Apply.receiptHashes layout groups

/-- `Chain::create_receipts_proofs_from_outgoing_receipts`: the root over the per-shard hashes and one
proof for every shard of the layout, in index order. -/
def receiptProofs (layout : ShardLayout) (shardId : ShardId) (receipts : Array Receipt) :
    Except String (CryptoHash × Array ReceiptProof) := do
  let hashes ← receiptsHashes layout receipts
  let (root, paths) := merklize hashes
  let groups ← Apply.groupByShard layout (receipts.map Codec.encode)
  let mut proofs := #[]
  for i in [0:paths.size] do
    let some toShard := layout.getShardId i | throw "shard index out of range"
    let rs ←
      (groups[i]!).mapM fun r =>
          match Codec.decodeAll (α := Receipt) r with
          | .ok r => pure r
          | .error _ => throw "receipt does not decode"
    proofs := proofs.push ⟨rs, ⟨shardId, toShard, paths[i]!⟩⟩
  pure (root, proofs)

/-- `EncodedShardChunk::create_partial_encoded_chunk`: the parts of the given ordinals, each with its
merkle path, and the receipt proofs. -/
def partialEncodedChunk (c : EncodedShardChunk) (partOrds : Array UInt64)
    (prevOutgoingReceipts : Array ReceiptProof) (paths : Array (Array MerklePathItem)) :
    Except String PartialEncodedChunk := do
  let parts := c.content.parts
  let mut out := #[]
  for o in partOrds do
    let some (some part) := parts[o.toNat]? | throw s!"no part {o}"
    let some path := paths[o.toNat]? | throw s!"no path {o}"
    out := out.push ⟨o, part, path⟩
  match c with
  | .v1 c =>
    pure (.v1 ⟨c.header, out, prevOutgoingReceipts⟩)
  | .v2 c =>
    pure (.v2 ⟨c.header, out, prevOutgoingReceipts⟩)

end Near.Node.Validator
