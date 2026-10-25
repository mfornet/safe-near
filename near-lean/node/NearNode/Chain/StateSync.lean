import NearNode.Chain.Apply
import NearNode.Chain.Header

/-!
# Checking a state sync header

What nearcore does with the `ShardStateSyncResponseHeader` of a peer before it asks for parts
(`ChainStateSyncAdapter::set_state_header`, `chain/chain/src/state_sync/adapter.rs`, with
`validate_chunk_proofs` in `chain/chain/src/validate.rs` and `validate_state_root_node` in the
runtime):

1. the chunk is the one its header names (hash, transaction root, receipts root);
2. the chunk is in the block before the sync block, and the chunk before it in the block before the
   block that included the chunk (merkle paths against `chunk_headers_root`);
3. the incoming receipts of the shard, block by block from the sync block back to the previous chunk,
   are the ones the blocks commit to (a merkle path to the receipts root of the chunk of the sending
   shard, and one from there to the block's `prev_chunk_outgoing_receipts_root`), from every shard
   that had a chunk in the block, once each;
4. the state root node hashes to the state root and carries the memory usage it claims.

Headers are the ones of the chain the node accepted, so a header that proves a block that is not on
it fails by itself. `ShardStart` is what the node keeps of a valid header: where the shard's chunks
start being applied and the receipts delivered up to there.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh Near.Node.Chain

private def fail' {α : Type} (msg : String) : Except String α :=
  .error s!"state sync header: {msg}"

/-- `Trie::get_memory_usage_from_serialized`. -/
def rootNodeMemoryUsage (data : ByteArray) : Option UInt64 :=
  match Codec.decodeAll (α := RawTrieNodeWithSize) data with
  | .ok n => some n.memoryUsage
  | .error _ => none

/-- `validate_state_root_node`. -/
def validateRootNode (node : StateRootNode) (root : CryptoHash) : Bool :=
  if root == CryptoHash.zero then node.data.size == 0 && node.memoryUsage == 0
  else CryptoHash.hash node.data == root && rootNodeMemoryUsage node.data == some node.memoryUsage

/-- `validate_chunk_proofs` for a chunk of version 2. -/
def validateChunkProofs (st : Near.Node.Chain.ChainState) (c : ShardChunkV2) : Except String Unit :=
  do
  let correct := c.header.chunkHash
  unless c.chunkHash == correct do
    throw "the chunk hash is not the hash of its header"
  let (txRoot, _) := merklize c.transactions
  unless txRoot == c.header.txRoot do
    throw "the transactions do not hash to the tx_root of the chunk header"
  if c.header.heightCreated == 0 then
    unless c.prevOutgoingReceipts.isEmpty && c.header.prevOutgoingReceiptsRoot == CryptoHash.zero do
      throw "the first chunk carries receipts"
  else
    let prev := c.header.prevBlockHash
    let layout := (← (st.epochIdFromPrevBlock prev >>= st.epoch).mapError (·.kind)).layout
    let encoded := c.prevOutgoingReceipts.map Codec.encode
    let groups ← groupByShard layout encoded
    let (root, _) := merklize (← receiptHashes layout groups)
    unless root == c.header.prevOutgoingReceiptsRoot do
      throw "the receipts do not hash to the prev_outgoing_receipts_root of the chunk header"

/-- All the checks of `set_state_header`, for a header received for `shard` at `syncHash`. -/
def validateStateHeader (st : Near.Node.Chain.ChainState) (syncHash : CryptoHash) (shard : ShardId)
    (h : ShardStateSyncResponseHeader) : Except String ShardStart := do
  let .v2 h := h | fail' "a version 1 header"
  let .v2 chunk := h.chunk | fail' "a version 1 chunk"
  let lift {α : Type} (r : Result α) : Except String α := r.mapError (·.kind)
  let sync ← lift (st.block syncHash)
  let syncPrev ← lift (st.block sync.view.prevHash)
  let epoch ← lift (st.epoch sync.info.epochId)
  unless epoch.layout.getShardIndex shard |>.isSome do
    throw s!"state sync header: shard {shard} is not in the layout"
  unless chunk.header.shardId == shard do
    fail' "the chunk is of another shard"
  -- 1-2. the chunk is valid and was included in the block before the sync block
  validateChunkProofs st chunk
  unless verifyPath syncPrev.view.chunkHeadersRoot h.chunkProof chunk.header.hashHeight do
    fail' "the chunk is not included in the block before the sync block"
  let height := chunk.header.heightIncluded
  let included ← blockAtHeight st syncPrev height
  -- 3. the chunk before it
  let mut prevHeight : BlockHeight := 0
  match h.prevChunkHeader, h.prevChunkProof with
  | some prevChunk, some proof =>
    let prevBlock ← lift (st.block included.view.prevHash)
    unless verifyPath prevBlock.view.chunkHeadersRoot proof prevChunk.hashHeight do
      fail' "the previous chunk is not included in the block before the chunk's block"
    prevHeight := prevChunk.heightIncluded
  | none, none =>
    unless height == 0 do
      fail' "an empty state response for a chunk that is not at height 0"
  | _, _ =>
    fail' "the previous chunk header and its proof must both be present or both absent"
  -- 4. the incoming receipts
  unless h.rootProofs.size == h.incomingReceiptsProofs.size do
    fail' "the proofs of the incoming receipts do not match them"
  let mut expected := syncHash
  let mut delivered : Array ByteArray := #[]
  let mut incoming : Array (CryptoHash × Array ByteArray) := #[]
  for i in [0:h.incomingReceiptsProofs.size] do
    let response := h.incomingReceiptsProofs[i]!
    unless response.blockHash == expected do
      fail' "the incoming receipts are not of a continuous run of blocks"
    let block ← lift (st.block response.blockHash)
    expected := block.view.prevHash
    let roots := h.rootProofs[i]!
    unless response.proofs.size == roots.size do
      fail' "the proofs of the incoming receipts do not match them"
    let included := block.view.chunkMask.foldl (fun n new => if new then n + 1 else n) 0
    unless response.proofs.size == included do
      fail' "a block's incoming receipts are not one proof per chunk it included"
    let mut seen : Array ShardId := #[]
    let mut receipts : Array ByteArray := #[]
    for j in [0:response.proofs.size] do
      let proof := response.proofs[j]!
      let rootProof := roots[j]!
      if seen.contains proof.proof.fromShardId then
        fail' "two proofs of the same shard"
      seen := seen.push proof.proof.fromShardId
      let leaf := CryptoHash.hashBorsh (shard, proof.receipts)
      unless verifyPath rootProof.root proof.proof.proof leaf do
        fail' "receipts are not in the outgoing receipts root of their chunk"
      unless verifyPath block.view.prevChunkOutgoingReceiptsRoot rootProof.path rootProof.root do
        fail' "the outgoing receipts root of a chunk is not in the block"
      receipts := receipts ++ proof.receipts.map Codec.encode
    incoming := incoming.push (response.blockHash, receipts)
    if block.view.height ≤ height then
      delivered := delivered ++ receipts
  let last ← lift (st.block expected)
  unless last.view.height == prevHeight do
    fail' "the incoming receipts do not reach back to the previous chunk"
  -- 5. the state root
  let root := chunk.header.prevStateRoot
  unless validateRootNode h.stateRootNode root do
    fail' "the state root node is not the root of the state"
  let some parts := getNumStateParts h.stateRootNode.memoryUsage
    | fail' "the memory usage of the state overflows the part count"
  pure
      { shard, syncHash, height, root, numParts := parts,
        memoryUsage := h.stateRootNode.memoryUsage, prevHeight, transactions := chunk.transactions,
        delivered, incoming, rootNode := h.stateRootNode }

end Near.Node.Apply
