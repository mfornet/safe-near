import NearNode.Chain.Validate
import NearNode.Validator.Block
import NearNode.Validator.Inclusion
import NearNode.Protocol

/-!
# Producing a block on the chain state

`Client::produce_block_on` (`chain/client/src/client.rs`) over the node's `ChainState`: the approvals
in the order of `get_epoch_block_approvers_ordered`, the new chunks (the ones with enough
endorsements) in place of the previous block's headers with `height_included` set, the block merkle
tree extended by the parent, the minted amount at an epoch start, the `next_bp_hash`, and the epoch
sync data hash, then `Block::produce`.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Borsh

/-- `ShardChunkHeader::height_included_mut`. -/
def _root_.Near.Node.ShardChunkHeader.withHeightIncluded (h : ShardChunkHeader)
    (height : BlockHeight) : ShardChunkHeader :=
  match h with
  | .v1 x => .v1 { x with heightIncluded := height }
  | .v2 x => .v2 { x with heightIncluded := height }
  | .v3 x => .v3 { x with heightIncluded := height }

/-- A new chunk and the endorsement signatures of its validators. -/
structure NewChunk where
  header : ShardChunkHeader
  endorsements : Array (Option Signature)
  deriving Inhabited

/-- The result of `Result` as a string. -/
def asString (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

/-- `Client::produce_block_on`. `approvals` are the signatures collected for `(prev, height)`;
`newChunks` the chunks to include, by shard. -/
def produceBlockOn (st : ChainState) (signer : Signer) (prevHash : CryptoHash)
    (height : BlockHeight) (approvals : Array (AccountId × Signature))
    (newChunks : Array (ShardId × NewChunk)) (now : UInt64) : Except String Block := do
  let prev ← asString (st.block prevHash)
  let epochId ← asString (st.epochIdFromPrevBlock prevHash)
  let nextEpochId ← asString (st.nextEpochIdFromPrevBlock prevHash)
  let epoch ← asString (st.epoch epochId)
  -- the approvals in the order of the approvers
  let approvers ← asString (st.blockApprovers prevHash epochId nextEpochId)
  let sigs : Array (Option Signature) :=
    approvers.map fun a => (approvals.find? (·.1 == a.accountId)).map (·.2)
  -- the next block producer's bp hash
  let nextBpHash ←
    if prev.view.epochId != epochId then
      asString (st.bpHashOf nextEpochId)
    else
      pure prev.view.nextBpHash
  let tree := prev.tree.insert prev.hash
  let minted ←
    if ← asString (st.isNextBlockEpochStart prevHash) then
      pure (some (← asString (st.epoch nextEpochId)).info.mintedAmount)
    else
      pure none
  let syncHash ←
    if epoch.info.protocolVersion ≥ 85 then
      asString (validateHeader.computeEpochSyncDataHash st prevHash)
    else
      pure none
  -- the chunk headers: the previous block's, the new ones replacing them
  let mut chunks := prev.chunks
  let mut endorsements : Array (Array (Option Signature)) := Array.replicate chunks.size #[]
  for (shard, c) in newChunks do
    let some i := epoch.layout.getShardIndex shard | throw s!"shard {shard} is not in the layout"
    if i ≥ chunks.size then
      throw "shard index out of range"
    chunks := chunks.set! i (c.header.withHeightIncluded height)
    endorsements := endorsements.set! i c.endorsements
  produceBlock signer
      { protocolVersion := epoch.info.protocolVersion,
        latestProtocolVersion := Near.Node.protocolVersion.toUInt32, prev := prev.header, height,
        blockOrdinal := tree.size + 1, chunks, chunkEndorsements := endorsements, epochId,
        nextEpochId, epochSyncDataHash := syncHash, approvals := sigs, economics := st.config,
        mintedAmount := minted, nextBpHash, blockMerkleRoot := tree.root, now }

end Near.Node.Validator
