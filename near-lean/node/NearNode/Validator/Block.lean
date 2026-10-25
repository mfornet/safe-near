import NearNode.Chain.Validate
import NearNode.Validator.Signer

/-!
# Producing a block

`Client::produce_block_on` gathers the inputs; `Block::produce` (`core/primitives/src/block.rs`) and
`BlockHeader::new` (`block_header.rs`) build the block. At protocol 86 (`DynamicResharding`, from 85)
the header is V6 and the body V2:

* the chunks included at `height` (`height_included == height`) add their gas used and limit, balance
  burnt and validator proposals to the block, in shard order; the others are the previous block's
  chunk headers and set no bit of the chunk mask;
* the next gas price is `compute_next_gas_price_checked` of the previous price and those sums, the
  total supply the previous one plus the minted amount (an epoch start) minus the balance burnt;
* the time is `max(now, prev + 1)`, the VRF is the validator's over the previous block's
  `random_value`, and the block's `random_value` is the SHA-256 of the VRF value (`get_block_metadata`);
* `last_ds_final_block` is the previous block when the new one is its child, else the previous
  `last_ds_final_block`; `last_final_block` is `last_final_block_for_height`;
* the roots are the merkle roots over the chunk headers (`Chunks::compute_*`), the endorsement bitmap
  has one bit per chunk validator (least significant bit first), the body hash is the body's, and
  the producer signs the block hash.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Borsh

/-- `ChunkEndorsementsBitmap::from_endorsements`: bit `i` of a shard's row is set when validator
`i` endorsed. -/
def endorsementsBitmap (rows : Array (Array Bool)) : ChunkEndorsementsBitmap :=
  ⟨rows.map fun row =>
      Id.run do
        let mut bytes := ByteArray.mk (Array.replicate ((row.size + 7) / 8) 0)
        for i in [0:row.size] do
          if row[i]! then
            bytes := bytes.set! (i / 8) (bytes.get! (i / 8) ||| (1 <<< (i % 8)).toUInt8)
        return bytes⟩

/-- `get_block_metadata`: the timestamp, the VRF value and proof, and the random value. -/
def blockMetadata (s : Signer) (prev : HeaderView) (now : UInt64) :
    Except String (UInt64 × VrfValue × VrfProof × CryptoHash) := do
  let time := if now <= prev.timestamp then prev.timestamp + 1 else now
  let some key := s.vrfKey | throw "the validator key has no VRF form"
  let (value, proof) := key.computeWithProof prev.randomValue.bytes
  pure (time, ⟨value⟩, ⟨proof⟩, CryptoHash.hash value)

/-- What `Client::produce_block_on` hands to `Block::produce`. -/
structure BlockInputs where
  /-- The protocol version of the epoch and the one the node votes for. -/
  protocolVersion : ProtocolVersion
  latestProtocolVersion : ProtocolVersion
  prev : BlockHeader
  height : BlockHeight
  blockOrdinal : UInt64
  /-- One header per shard; those with `height_included == height` are new. -/
  chunks : Array ShardChunkHeader
  /-- One row per shard of the endorsement signatures of its chunk validators, in assignment order. -/
  chunkEndorsements : Array (Array (Option Signature))
  epochId : EpochId
  nextEpochId : EpochId
  epochSyncDataHash : Option CryptoHash
  /-- The signatures of the approvers, in the order of the epoch's approvers. -/
  approvals : Array (Option Signature)
  economics : Config
  mintedAmount : Option Balance
  nextBpHash : CryptoHash
  blockMerkleRoot : CryptoHash
  now : UInt64
  shardSplit : Option (ShardId × AccountId) := none
  deriving Inhabited

/-- `Block::produce` for a protocol that uses header V6 (from 85). -/
def produceBlock (s : Signer) (i : BlockInputs) : Except String Block := do
  if i.protocolVersion < 85 || i.protocolVersion ≥ 180 then
    throw "only the V6 header (protocol 85 to 179) is produced"
  let some prev := i.prev.view? | throw "the previous header is not one this node knows"
  let prevHash := i.prev.hash
  -- the chunks included in this block
  let isNew := fun (c : ShardChunkHeader) => c.heightIncluded == i.height
  let mut proposals : Array ValidatorStake := #[]
  let mut gasUsed : Nat := 0
  let mut gasLimit : Nat := 0
  let mut burnt : Nat := 0
  let mut mask : Array Bool := #[]
  for c in i.chunks do
    if isNew c then
      gasUsed := gasUsed + c.prevGasUsed.toNat
      proposals := proposals ++ c.prevValidatorProposals
      gasLimit := gasLimit + c.gasLimit.toNat
      burnt := burnt + c.prevBalanceBurnt.val
      mask := mask.push true
    else
      mask := mask.push false
  let some nextPrice := computeNextGasPrice prev.nextGasPrice.val gasUsed gasLimit i.economics
    | throw "the gas price overflows"
  let supply := prev.totalSupply.val + (i.mintedAmount.map (·.val)).getD 0
  if supply < burnt then
    throw "more burnt than in supply"
  let (time, vrfValue, vrfProof, random) ← blockMetadata s prev i.now
  let lastDsFinal := if i.height == prev.height + 1 then prevHash else prev.lastDsFinalBlock
  let lastFinal :=
    if i.height == prev.height + 1 && prev.lastDsFinalBlock == prev.prevHash then prev.prevHash
    else prev.lastFinalBlock
  let bitmap := endorsementsBitmap (i.chunkEndorsements.map (·.map (·.isSome)))
  let body : BlockBody := .v2 ⟨i.chunks, #[], vrfValue, vrfProof, i.chunkEndorsements⟩
  let stateRoot := (merklize (i.chunks.map ShardChunkHeader.prevStateRoot)).1
  let receiptsRoot := (merklize (i.chunks.map ShardChunkHeader.prevOutgoingReceiptsRoot)).1
  let headersRoot := (merklize (i.chunks.map ShardChunkHeader.hashHeight)).1
  let txRoot := (merklize (i.chunks.map ShardChunkHeader.txRoot)).1
  let outcomeRoot := (merklize (i.chunks.map ShardChunkHeader.prevOutcomeRoot)).1
  let lite : BlockHeaderInnerLite :=
    { height := i.height, epochId := i.epochId, nextEpochId := i.nextEpochId,
      prevStateRoot := stateRoot, prevOutcomeRoot := outcomeRoot, timestamp := time,
      nextBpHash := i.nextBpHash, blockMerkleRoot := i.blockMerkleRoot }
  let rest : BlockHeaderInnerRestV6 :=
    { blockBodyHash := body.computeHash, prevChunkOutgoingReceiptsRoot := receiptsRoot,
      chunkHeadersRoot := headersRoot, chunkTxRoot := txRoot, randomValue := random,
      prevValidatorProposals := proposals, chunkMask := mask, nextGasPrice := ⟨nextPrice⟩,
      totalSupply := ⟨supply - burnt⟩, lastFinalBlock := lastFinal, lastDsFinalBlock := lastDsFinal,
      blockOrdinal := i.blockOrdinal, prevHeight := prev.height,
      epochSyncDataHash := i.epochSyncDataHash, approvals := i.approvals,
      latestProtocolVersion := i.latestProtocolVersion, chunkEndorsements := bitmap,
      shardSplit := i.shardSplit }
  let hash := computeBlockHash prevHash lite rest
  pure (.v4 ⟨.v6 ⟨prevHash, lite, rest, s.sign hash.bytes⟩, body⟩)

end Near.Node.Validator
