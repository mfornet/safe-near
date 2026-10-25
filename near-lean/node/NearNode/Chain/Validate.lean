import NearNode.Chain.State

/-!
# Header and block validation

Everything `Chain::start_process_block_async` checks before it would apply the chunks of a block
(`chain/chain/src/chain.rs` at the pinned nearcore), in nearcore's order, so that the first failing
check names the same `Error` variant:

* `verify_block_hash_and_signature`: the block body hash and the producer's signature;
* `preprocess_block`: the epoch is known, the number of chunk headers, the block is not known, the
  height is not absurd, an unknown parent makes an orphan (after `partial_verify_orphan_header_signature`
  and `check_validity`);
* `validate_header`: challenges, signature, epoch ids, protocol version, `next_bp_hash`, chunk mask,
  `prev_height`, timestamp, approvals (signatures and the Doomslug threshold), `last_ds_final_block`
  and `last_final_block`, `block_merkle_root`, `block_ordinal`, `epoch_sync_data_hash` and the chunk
  endorsements bitmap;
* the VRF (`verify_block_vrf`) and `random_value`;
* `validate_block`: the genesis chunks, and for every new chunk its shard, `prev_block_hash` and
  producer signature, then `check_validity` (the roots and the chunk mask);
* `validate_block_shard_split`, the gas price, the total supply, `validate_chunk_headers` (old
  chunks are the previous ones, `prev_validator_proposals`) and `validate_chunk_endorsements_in_block`.

Not checked, because they need what the node does not have yet: the clock (`InvalidBlockFutureTime`),
the chunk bodies and parts (`ping_missing_chunks`), the head and final head beyond their heights
(`check_if_finalizable`), garbage collection (`get_gc_stop_height`), catch-up and state sync, and
SPICE (rejected).
-/

namespace Near.Node.Chain

open Near.Node Borsh

/-! ### Doomslug and approvals -/

/-- `Doomslug::can_approved_block_be_produced` with the `TwoThirds` threshold: the stake of the
approvers is above two thirds of the total in both epochs (or the total is zero). -/
def canApprovedBlockBeProduced (approvals : Array (Option Signature)) (stakes : Array (Nat × Nat)) :
    Bool :=
  let total1 := stakes.foldl (fun a s => a + s.1) 0
  let total2 := stakes.foldl (fun a s => a + s.2) 0
  let threshold1 := total1 * 2 / 3
  let threshold2 := total2 * 2 / 3
  let pairs := approvals.zip stakes
  let approved1 := pairs.foldl (fun a (x, s) => if x.isSome then a + s.1 else a) 0
  let approved2 := pairs.foldl (fun a (x, s) => if x.isSome then a + s.2 else a) 0
  (approved1 > threshold1 || threshold1 == 0) && (approved2 > threshold2 || threshold2 == 0)

/-- `verify_approval_with_approvers_info`. -/
def verifyApprovalWithApproversInfo (prevHash : CryptoHash) (prevHeight height : BlockHeight)
    (approvals : Array (Option Signature)) (info : Array ApprovalStake) : Bool :=
  if approvals.size > info.size then false
  else
    let inner : ApprovalInner :=
      if prevHeight + 1 == height then .endorsement prevHash else .skip prevHeight
    let message := Approval.getDataForSig inner height
    (info.zip approvals).all fun (validator, sig) =>
      match sig with
      | some s => verifySignature s message validator.publicKey
      | none => true

/-! ### Roots and economics -/

/-- `From<BlockValidityError> for Error`. -/
def validityError : BlockValidityError → Err
  | .invalidStateRoot => ⟨"InvalidStateRoot", ""⟩
  | .invalidReceiptRoot => ⟨"InvalidChunkReceiptsRoot", ""⟩
  | .invalidChunkHeaderRoot => ⟨"InvalidChunkHeadersRoot", ""⟩
  | .invalidTransactionRoot => ⟨"InvalidTxRoot", ""⟩
  | .invalidChunkMask => ⟨"InvalidChunkMask", ""⟩

/-- `Block::check_validity` as a result. -/
def checkValidity (block : Block) : Result Unit :=
  match block.checkValidity with
  | none => pure ()
  | some e => .error (validityError e)

/-- `Block::compute_next_gas_price_checked`; `none` where nearcore's arithmetic overflows. -/
def computeNextGasPrice (gasPrice : Nat) (gasUsed gasLimit : Nat) (cfg : Config) : Option Nat :=
  if gasLimit == 0 then some gasPrice
  else
    let positive := 2 * cfg.rateDenom * gasLimit + 2 * cfg.rateNumer * gasUsed
    let negative := cfg.rateNumer * gasLimit
    if positive < negative then none
    else
      let numerator := positive - negative
      let denominator := 2 * cfg.rateDenom * gasLimit
      let next := gasPrice * numerator / denominator
      some (max cfg.minGasPrice.val (min cfg.maxGasPrice.val next))

private def u64Limit : Nat :=
  2 ^ 64

private def u128Limit : Nat :=
  2 ^ 128

/-- The chunks included in the block at `height`. -/
def newChunks (chunks : Array ShardChunkHeader) (height : BlockHeight) : Array ShardChunkHeader :=
  chunks.filter (·.isNewChunk height)

/-- Whether bit `i` of a bitmap row is set (little-endian bit order within a byte). -/
def bitAt (bytes : ByteArray) (i : Nat) : Bool :=
  (bytes.get! (i / 8)).toNat >>> (i % 8) % 2 == 1

/-- The number of bits of a bitmap row (`ChunkEndorsementsBitmap::len`). -/
def rowBits (row : ByteArray) : Nat :=
  row.size * 8

/-! ### The checks -/

/-- `verify_block_header_signature_with_epoch_manager`. -/
def verifyHeaderSignature (st : ChainState) (v : HeaderView) (hash : CryptoHash) : Result Bool := do
  let producer ← st.blockProducer v.epochId v.height
  pure (verifySignature v.signature hash.bytes producer.publicKey)

/-- `Chain::verify_block_hash_and_signature`: `true` when correct. -/
def verifyBlockHashAndSignature (st : ChainState) (block : Block) (v : HeaderView)
    (hash : CryptoHash) : Result Bool := do
  if hash == st.genesisHash then
    return true
  match block.computeBlockBodyHash with
  | none =>
    return false
  | some bodyHash =>
    if v.blockBodyHash != bodyHash then
      return false
    verifyHeaderSignature st v hash

/-- `validate_chunk_endorsements_in_header`. -/
def validateChunkEndorsementsInHeader (st : ChainState) (v : HeaderView) : Result Unit := do
  let some bitmap := v.chunkEndorsements
    | fail "InvalidChunkEndorsementBitmap" "expected chunk endorsements bitmap but found None"
  let epoch ← st.epoch (← st.epochIdFromPrevBlock v.prevHash)
  let shardIds := epoch.layout.shardIds
  guardErr (bitmap.inner.size != shardIds.size) "InvalidChunkEndorsementBitmap"
      "bitmap and epoch shards differ"
  for shard in shardIds do
    let some index := epoch.layout.getShardIndex shard
      | fail "InvalidShardId" "shard index"
    let mask := v.chunkMask[index]?.getD false
    let bits := (bitmap.inner[index]?.map rowBits).getD 0
    guardErr (mask != decide (bits > 0)) "InvalidChunkEndorsementBitmap"
        "bitmap must be non-empty iff the shard has a new chunk"

/-- `Chain::validate_header` with `Provenance::NONE` (the approvals and finality are checked). -/
def validateHeader (st : ChainState) (v : HeaderView) (hash : CryptoHash) : Result Unit := do
  guardErr v.challengesPresent "InvalidChallenge"
  guardErr (!(← verifyHeaderSignature st v hash)) "InvalidSignature"
  let prev ←
    match st.blocks[v.prevHash.bytes]? with
    | some p =>
      pure p
    | none =>
      fail "DBNotFoundErr" "block header not found"
  guardErr ((← st.epochIdFromPrevBlock v.prevHash) != v.epochId) "InvalidEpochHash"
  guardErr ((← st.nextEpochIdFromPrevBlock v.prevHash) != v.nextEpochId) "InvalidEpochHash"
  let epoch ← st.epoch v.epochId
  let protocolVersion := epoch.info.protocolVersion
  guardErr (v.latestProtocolVersion < protocolVersion) "InvalidProtocolVersion"
  if v.epochId == prev.view.epochId then
    guardErr (v.nextBpHash != prev.view.nextBpHash) "InvalidNextBPHash"
  else
    guardErr (v.nextBpHash != (← st.bpHashOf v.nextEpochId)) "InvalidNextBPHash"
  guardErr (v.chunkMask.size != epoch.layout.shardIds.size) "InvalidChunkMask"
  guardErr (v.prevHeight != prev.view.height) "Other" "Invalid prev_height"
  guardErr (v.timestamp ≤ prev.view.timestamp) "InvalidBlockPastTime"
  -- approvals
  let approvers ←
    st.blockApprovers v.prevHash (← st.epochIdFromPrevBlock v.prevHash)
        (← st.nextEpochIdFromPrevBlock v.prevHash)
  guardErr
      (!verifyApprovalWithApproversInfo prev.hash prev.view.height v.height v.approvals approvers)
      "InvalidApprovals"
  let stakes := approvers.map fun a => (a.stakeThisEpoch.val, a.stakeNextEpoch.val)
  guardErr (!canApprovedBlockBeProduced v.approvals stakes) "NotEnoughApprovals"
  -- finality
  let consecutive := prev.view.height + 1 == v.height
  let expectedDs := if consecutive then prev.hash else prev.view.lastDsFinalBlock
  let expectedFinal :=
    if consecutive && prev.view.lastDsFinalBlock == prev.view.prevHash then prev.view.prevHash
    else prev.view.lastFinalBlock
  guardErr (v.lastDsFinalBlock != expectedDs || v.lastFinalBlock != expectedFinal)
      "InvalidFinalityInfo"
  -- block merkle root, ordinal, epoch sync data
  let tree := prev.tree.insert prev.hash
  guardErr (tree.root != v.blockMerkleRoot) "InvalidBlockMerkleRoot"
  if protocolVersion ≥ 85 then
    guardErr (tree.size + 1 != v.blockOrdinal) "InvalidBlockOrdinal"
    let expected ← computeEpochSyncDataHash st v.prevHash
    guardErr (expected != v.epochSyncDataHash) "InvalidEpochSyncDataHash"
  validateChunkEndorsementsInHeader st v
where
  /-- `EpochManagerAdapter::compute_epoch_sync_data_hash`. -/
  computeEpochSyncDataHash (st : ChainState) (prevHash : CryptoHash) : Result (Option CryptoHash) :=
    do
    if !(← st.isNextBlockEpochStart prevHash) then
      return none
    let epochId ← st.epochIdFromPrevBlock prevHash
    let nextEpochId ← st.nextEpochIdFromPrevBlock prevHash
    let last ← st.block prevHash
    let firstOfEpoch ← st.block last.info.epochFirstBlock
    let secondLast ← st.block last.info.prevHash
    let data : EpochSyncProofLastEpochData :=
      { epochInfo := (← st.epoch last.info.epochId).info,
        nextEpochInfo := (← st.epoch epochId).info,
        nextNextEpochInfo := (← st.epoch nextEpochId).info,
        firstBlockInEpoch := .v4 firstOfEpoch.info, lastBlockInEpoch := .v4 last.info,
        secondLastBlockInEpoch := .v4 secondLast.info }
    pure (some data.computeEpochSyncDataHash)

/-- `validate_chunk_endorsements_in_block`. -/
def validateChunkEndorsementsInBlock (st : ChainState) (block : Block) (v : HeaderView)
    (chunks : Array ShardChunkHeader) : Result Unit := do
  let signatures := block.chunkEndorsements
  guardErr (chunks.size != signatures.size) "InvalidChunkEndorsement"
  let bitmap := v.chunkEndorsements
  if let some b := bitmap then
    guardErr (b.inner.size != signatures.size) "InvalidChunkEndorsementBitmap"
  let epochId ← st.epochIdFromPrevBlock v.prevHash
  let epoch ← st.epoch epochId
  for h : i in [0:chunks.size] do
    let chunk := chunks[i]
    let sigs := signatures[i]!
    if chunk.heightIncluded != v.height then
      guardErr (!sigs.isEmpty) "InvalidChunkEndorsement"
      continue
    let shard := chunk.shardId
    let some shardIndex := epoch.layout.getShardIndex shard
      | fail "InvalidShardId" "shard index"
    let assignments ← st.chunkValidatorAssignments epochId shard chunk.heightCreated
    guardErr (assignments.size != sigs.size) "InvalidChunkEndorsement"
    let signed := endorsementSignedBytes chunk.chunkHash
    let mut endorsed : Array (AccountId × Signature) := #[]
    for (assignment, sig) in assignments.zip sigs do
      let some s := sig
        | continue
      let validator ← st.validatorByAccount epochId assignment.1
      guardErr (!verifySignature s signed validator.publicKey) "InvalidChunkEndorsement"
      endorsed := (endorsed.filter (·.1 != assignment.1)).push (assignment.1, s)
    -- `compute_endorsement_state`
    let mut total := 0
    let mut stake := 0
    for (account, weight) in assignments do
      total := total + weight.val
      if endorsed.any (·.1 == account) then
        stake := stake + weight.val
        endorsed := endorsed.filter (·.1 != account)
    guardErr (stake < total * 2 / 3 + 1) "InvalidChunkEndorsement"
    if let some b := bitmap then
      let row := b.inner[shardIndex]?.getD ByteArray.empty
      guardErr (rowBits row != (sigs.size + 7) / 8 * 8) "InvalidChunkEndorsementBitmap"
          "bitmap length"
      for j in [0:sigs.size] do
        guardErr (bitAt row j != sigs[j]!.isSome) "InvalidChunkEndorsementBitmap"
            "bit does not match the signature"
      for j in [sigs.size:rowBits row] do
        guardErr (bitAt row j) "InvalidChunkEndorsementBitmap" "extra bit set"

/-- `Chain::validate_block_impl`. -/
def validateBlockImpl (st : ChainState) (block : Block) (v : HeaderView) : Result Unit := do
  let epoch ← st.epoch v.epochId
  let chunks := block.chunks
  for h : i in [0:chunks.size] do
    let chunk := chunks[i]
    let some shard := epoch.layout.getShardId i
      | fail "InvalidShardIndex" "shard id"
    if chunk.isGenesis then
      match st.genesisChunks[i]? with
      | none =>
        fail "InvalidChunk" "genesis chunk not found"
      | some g =>
        guardErr (g.chunkHash != chunk.chunkHash || g.signature != chunk.signature) "InvalidChunk"
            "genesis chunk mismatch"
    else if chunk.isNewChunk v.height then
      guardErr (chunk.shardId != shard) "InvalidShardId"
      guardErr (chunk.prevBlockHash != v.prevHash) "InvalidChunk" "chunk prev_block_hash mismatch"
      let producer ← st.chunkProducerAfter chunk.prevBlockHash chunk.shardId
      guardErr (!verifySignature chunk.signature chunk.chunkHash.hash.bytes producer.publicKey)
          "InvalidChunk" "invalid chunk header signature"
  checkValidity block

/-- `validate_block_shard_split` for a static shard layout: the header carries no split. -/
def validateBlockShardSplit (st : ChainState) (v : HeaderView) : Result Unit := do
  -- `is_produced_block_last_in_epoch`
  if !(← st.isNextBlockEpochStart v.prevHash) then
    let lastFinal ← st.block v.lastFinalBlock
    let parent ← st.block v.prevHash
    let _ ← st.isNextBlockInNextEpochImpl v.height lastFinal.info.height parent.info.epochFirstBlock
  if !st.config.staticShardLayout then
    failOther "dynamic resharding is not supported"
  guardErr v.shardSplit.isSome "InvalidBlockHeaderShardSplit"

/-- The gas price and total supply checks of `preprocess_block`. -/
def validateEconomics (st : ChainState) (v : HeaderView) (prev : BlockRec)
    (chunks : Array ShardChunkHeader) : Result Unit := do
  let fresh := newChunks chunks v.height
  let used := fresh.foldl (fun a c => a + c.prevGasUsed.toNat) 0
  let limit := fresh.foldl (fun a c => a + c.gasLimit.toNat) 0
  if used ≥ u64Limit || limit ≥ u64Limit then
    failOther "arithmetic overflow when checking gas price"
  let some expected := computeNextGasPrice prev.view.nextGasPrice.val used limit st.config
    | failOther "arithmetic overflow when checking gas price"
  guardErr (v.nextGasPrice.val != expected) "InvalidGasPrice"
  let minted ←
    if ← st.isNextBlockEpochStart prev.hash then
      pure ((← st.epoch v.nextEpochId).info.mintedAmount.val)
    else
      pure 0
  let burnt := fresh.foldl (fun a c => a + c.prevBalanceBurnt.val) 0
  if burnt ≥ u128Limit then
    failOther "arithmetic overflow when checking total supply"
  let available := prev.view.totalSupply.val + minted
  if available ≥ u128Limit then
    failOther "arithmetic overflow when checking total supply"
  guardErr (burnt > available || v.totalSupply.val != available - burnt) "InvalidTotalSupply"

/-- `Chain::validate_chunk_headers` with `validate_block_proposals`. -/
def validateChunkHeaders (st : ChainState) (v : HeaderView) (prev : BlockRec)
    (chunks : Array ShardChunkHeader) : Result Unit := do
  let epochId ← st.epochIdFromPrevBlock prev.hash
  let layout := (← st.epoch epochId).layout
  let prevLayout := (← st.epoch prev.info.epochId).layout
  if layout != prevLayout then
    failOther "resharding is not supported"
  let prevChunks := prev.chunks
  for i in [0:min chunks.size prevChunks.size] do
    let chunk := chunks[i]!
    if chunk.isNewChunk v.height then
      guardErr (chunk.prevBlockHash != v.prevHash) "InvalidChunk" "invalid prev_block_hash"
    else
      guardErr (prevChunks[i]! != chunk) "InvalidChunk" "invalid chunk header"
  let expected := (newChunks chunks v.height).foldl (fun a c => a ++ c.prevValidatorProposals) #[]
  guardErr (expected != v.prevValidatorProposals) "InvalidValidatorProposals"

/-- What `start_process_block_async` checks of a block beyond its header (`validate_header` and the
orphan and known checks are the caller's): the VRF and `random_value`, `validate_block_impl`, the
shard split, the gas price and total supply, the chunk headers and the chunk endorsements. `prev` is
the parent; where its chunk headers are not known (a header-only record) the comparison of old chunks
with them is empty. -/
def validateBody (st : ChainState) (block : Block) (v : HeaderView) (prev : BlockRec) :
    Result Unit := do
  let chunks := block.chunks
  -- the VRF
  let producer ← st.blockProducer v.epochId v.height
  let (vrfValue, vrfProof) := block.vrf
  match producer.publicKey with
  | .ed25519 key =>
    guardErr
        (!NearCrypto.Vrf.Impl.blockVrfValid key prev.view.randomValue.bytes vrfValue.bytes
            vrfProof.bytes)
        "InvalidRandomnessBeaconOutput"
  | _ =>
    fail "InvalidRandomnessBeaconOutput"
  guardErr (v.randomValue.bytes != NearCrypto.Vrf.Impl.randomValue vrfValue.bytes)
      "InvalidRandomnessBeaconOutput"
  validateBlockImpl st block v
  validateBlockShardSplit st v
  validateEconomics st v prev chunks
  validateChunkHeaders st v prev chunks
  validateChunkEndorsementsInBlock st block v chunks
  guardErr block.isSpiceBlock "Other" "encountered spice block without spice feature enabled"

/-- The block is rejected or accepted by nearcore's checks that need no chunk bodies; `Chain`'s
`start_process_block_async` up to `ping_missing_chunks`. -/
def validateBlock (st : ChainState) (block : Block) : Result Unit := do
  let header := block.header
  let some v := header.view?
    | fail "Unsupported" "header version"
  let hash := header.hash
  -- 0) hash and signature
  if !(← verifyBlockHashAndSignature st block v hash) then
    fail "InvalidSignature"
  -- 1) preprocess_block
  if !st.epochExists v.epochId then
    fail "EpochOutOfBounds"
  let chunks := block.chunks
  let epoch ← st.epoch v.epochId
  guardErr (chunks.size != epoch.layout.shardIds.size) "IncorrectNumberOfChunkHeaders"
  guardErr (st.blockExists hash) "BlockKnown"
  guardErr (v.height > st.headHeight + st.config.epochLength * 20) "InvalidBlockHeight"
  if v.prevHash != st.head && !st.blockExists v.prevHash then
    -- partial_verify_orphan_header_signature
    let producer ← st.blockProducer v.epochId v.height
    let validator ← st.validatorByAccount v.epochId producer.accountId
    guardErr (!verifySignature v.signature hash.bytes validator.publicKey) "InvalidSignature"
    checkValidity block
    fail "Orphan"
  let prev ← st.block v.prevHash
  validateHeader st v hash
  validateBody st block v prev

/-- Validate a block and, if it is accepted, record it. -/
def acceptBlock (st : ChainState) (block : Block) : Result ChainState := do
  validateBlock st block
  let some v := block.header.view?
    | fail "Unsupported" "header version"
  st.record block.header v block.chunks

end Near.Node.Chain
