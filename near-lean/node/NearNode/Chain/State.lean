import Std.Data.HashMap
import NearNode.Chain.Types

/-!
# Chain state: blocks, epochs and the epoch manager's questions

What the validator knows about the chain it has accepted so far: for each block its header, its
chunk headers, the `BlockInfo` the epoch manager derives from it (`BlockInfo::from_header` and
`EpochManager::record_block_info_impl`) and its block merkle tree
(`ChainStoreUpdate::update_and_save_block_merkle_tree`); for each epoch its `EpochInfo` and shard
layout. In M5a the `EpochInfo`s are given (computing the next one is M5b).

The questions `EpochManager` answers (`chain/epoch-manager/src/lib.rs`, `adapter.rs`) are
functions of this state: the epoch of a block, whether its successor starts a new epoch, the
approvers, the block and chunk producers and the chunk validator assignments.
-/

namespace Near.Node.Chain

open Near.Node Borsh

/-- The `EpochInfo` of an epoch and its shard layout (`EpochManager::get_shard_layout`). -/
structure EpochData where
  info : EpochInfo
  layout : ShardLayout

/-- The configuration the checks need (genesis config and block economics). -/
structure Config where
  epochLength : UInt64
  genesisHeight : BlockHeight
  minGasPrice : Balance
  maxGasPrice : Balance
  /-- `gas_price_adjustment_rate` as the fraction `numer / denom`. -/
  rateNumer : Nat
  rateDenom : Nat
  /-- The epoch config has a static shard layout (no dynamic resharding). -/
  staticShardLayout : Bool
  deriving Inhabited

/-- An accepted block. -/
structure BlockRec where
  hash : CryptoHash
  header : BlockHeader
  view : HeaderView
  chunks : Array ShardChunkHeader
  info : BlockInfoV4
  tree : PartialMerkleTree
  deriving Inhabited

/-- The accepted blocks and the known epochs. -/
structure ChainState where
  config : Config
  epochs : Std.HashMap ByteArray EpochData
  blocks : Std.HashMap ByteArray BlockRec
  /-- The hash and height of the head of the chain (the accepted block of the largest height). -/
  head : CryptoHash
  headHeight : BlockHeight
  genesisHash : CryptoHash
  genesisChunks : Array ShardChunkHeader
  deriving Inhabited

/-- `ApprovalStake`. -/
structure ApprovalStake where
  accountId : AccountId
  publicKey : PublicKey
  stakeThisEpoch : Balance
  stakeNextEpoch : Balance
  deriving Inhabited

namespace ChainState

/-- `EpochManager::get_epoch_info` and `get_shard_layout`. -/
def epoch (st : ChainState) (id : EpochId) : Result EpochData :=
  match st.epochs[id.hash.bytes]? with
  | some e => pure e
  | none => fail "EpochOutOfBounds"

/-- `EpochManager::epoch_exists`. -/
def epochExists (st : ChainState) (id : EpochId) : Bool :=
  st.epochs.contains id.hash.bytes

/-- `EpochManager::get_block_info`: the accepted block. -/
def block (st : ChainState) (hash : CryptoHash) : Result BlockRec :=
  match st.blocks[hash.bytes]? with
  | some b => pure b
  | none => fail "DBNotFoundErr" "epoch block"

/-- `Chain::block_exists`. -/
def blockExists (st : ChainState) (hash : CryptoHash) : Bool :=
  st.blocks.contains hash.bytes

/-- `EpochManager::is_next_block_in_next_epoch_impl`. -/
def isNextBlockInNextEpochImpl (st : ChainState) (blockHeight lastFinalHeight : BlockHeight)
    (epochFirstBlock : CryptoHash) : Result Bool := do
  let first ← st.block epochFirstBlock
  let _ ← st.epoch first.info.epochId
  let epochLength := st.config.epochLength
  let estimated := first.info.height + epochLength
  if epochLength ≤ 3 then
    pure (blockHeight + 1 ≥ estimated)
  else
    pure (lastFinalHeight + 3 ≥ estimated)

/-- `EpochManager::is_next_block_in_next_epoch`. -/
def isNextBlockInNextEpoch (st : ChainState) (info : BlockInfoV4) : Result Bool :=
  if info.prevHash == CryptoHash.zero then pure true
  else st.isNextBlockInNextEpochImpl info.height info.lastFinalizedHeight info.epochFirstBlock

/-- `EpochManager::is_next_block_epoch_start`. -/
def isNextBlockEpochStart (st : ChainState) (hash : CryptoHash) : Result Bool := do
  st.isNextBlockInNextEpoch (← st.block hash).info

/-- `EpochManager::get_epoch_id`. -/
def epochIdOf (st : ChainState) (hash : CryptoHash) : Result EpochId := do
  pure (← st.block hash).info.epochId

/-- `EpochManager::get_next_epoch_id`: the hash before the first block of the epoch. -/
def nextEpochIdOf (st : ChainState) (hash : CryptoHash) : Result EpochId := do
  let b ← st.block hash
  let first ← st.block b.info.epochFirstBlock
  pure ⟨first.info.prevHash⟩

/-- `get_epoch_id_from_prev_block`. -/
def epochIdFromPrevBlock (st : ChainState) (parent : CryptoHash) : Result EpochId := do
  if ← st.isNextBlockEpochStart parent then
    st.nextEpochIdOf parent
  else
    st.epochIdOf parent

/-- `get_next_epoch_id_from_prev_block`. -/
def nextEpochIdFromPrevBlock (st : ChainState) (parent : CryptoHash) : Result EpochId := do
  if ← st.isNextBlockEpochStart parent then
    pure ⟨parent⟩
  else
    st.nextEpochIdOf parent

/-- `EpochManager::next_block_need_approvals_from_next_epoch`. -/
def nextBlockNeedApprovalsFromNextEpoch (st : ChainState) (b : BlockRec) : Result Bool := do
  if ← st.isNextBlockInNextEpoch b.info then
    pure false
  else
    let _ ← st.epoch b.info.epochId
    let first ← st.block b.info.epochFirstBlock
    let estimated := first.info.height + st.config.epochLength
    pure (b.info.lastFinalizedHeight + 3 < estimated && b.info.height + 3 ≥ estimated)

/-- `get_all_block_producers_settlement`: the validator behind every seat. -/
def blockProducersSettlement (st : ChainState) (id : EpochId) : Result (Array ValidatorStake) := do
  let e ← st.epoch id
  e.info.blockProducersSettlement.mapM fun v =>
      match e.info.getValidator v with
      | some s => pure s
      | none => fail "ValidatorError" "validator index out of range"

/-- `get_all_block_producers_ordered`: the distinct block producers in seat order. -/
def blockProducersOrdered (st : ChainState) (id : EpochId) : Result (Array ValidatorStake) := do
  let settlement ← st.blockProducersSettlement id
  pure <|
      settlement.foldl (init := #[]) fun acc v =>
        if acc.any (·.accountId == v.accountId) then acc else acc.push v

/-- `get_all_block_approvers_ordered`: the approvers of the block that follows `parent`. -/
def blockApprovers (st : ChainState) (parent : CryptoHash) (current next : EpochId) :
    Result (Array ApprovalStake) := do
  let current_ ← st.blockProducersSettlement current
  let boundary := current_.size
  let b ← st.block parent
  let settlement ←
    if ← st.nextBlockNeedApprovalsFromNextEpoch b then
      pure (current_ ++ (← st.blockProducersSettlement next))
    else
      pure current_
  let mut result : Array ApprovalStake := #[]
  let mut index : Std.HashMap String Nat := {}
  for h : ord in [0:settlement.size] do
    let v := settlement[ord]
    match index[v.accountId.val]? with
    | none =>
      index := index.insert v.accountId.val result.size
      let isNext := ord ≥ boundary
      result :=
        result.push
          { accountId := v.accountId, publicKey := v.publicKey,
            stakeThisEpoch := if isNext then ⟨0⟩ else v.stake,
            stakeNextEpoch := if isNext then v.stake else ⟨0⟩ }
    | some old =>
      if ord ≥ boundary then
        result := result.modify old fun a => { a with stakeNextEpoch := v.stake }
  pure result

/-- `EpochManagerAdapter::get_block_producer_info`. -/
def blockProducer (st : ChainState) (epoch : EpochId) (height : BlockHeight) :
    Result ValidatorStake := do
  let e ← st.epoch epoch
  match e.info.sampleBlockProducer height >>= e.info.getValidator with
  | some v =>
    pure v
  | none =>
    fail "ValidatorError" "block producer selection failed"

/-- `EpochManagerAdapter::get_chunk_producer_info`. -/
def chunkProducer (st : ChainState) (epoch : EpochId) (height : BlockHeight) (shard : ShardId) :
    Result ValidatorStake := do
  let e ← st.epoch epoch
  match e.info.sampleChunkProducer e.layout shard height >>= e.info.getValidator with
  | some v =>
    pure v
  | none =>
    fail "ValidatorError" s!"ChunkProducerSelectionError: invalid shard {shard} for height {height}"

/-- `get_chunk_producer_info_db` without `EarlyKickout` (the stable protocol): the producer at the
height after `prev`, in the epoch of the block that follows it. -/
def chunkProducerAfter (st : ChainState) (prev : CryptoHash) (shard : ShardId) :
    Result ValidatorStake := do
  let epoch ← st.epochIdFromPrevBlock prev
  let b ← st.block prev
  st.chunkProducer epoch (b.info.height + 1) shard

/-- `get_chunk_validator_assignments`: the chunk validators of a shard at a height, with their
assignment weights, in order. -/
def chunkValidatorAssignments (st : ChainState) (epoch : EpochId) (shard : ShardId)
    (height : BlockHeight) : Result (Array (AccountId × Balance)) := do
  let e ← st.epoch epoch
  let perShard := (e.info.sampleChunkValidators height).getD #[]
  let some index := e.layout.getShardIndex shard
    | fail "ValidatorError" s!"ChunkValidatorSelectionError: invalid shard {shard}"
  let some row := perShard[index]?
    | fail "ValidatorError" s!"ChunkValidatorSelectionError: invalid shard {shard}"
  row.mapM fun (v, w) =>
      match e.info.getValidator v with
      | some s => pure (s.accountId, w)
      | none => fail "ValidatorError" "validator index out of range"

/-- `get_validator_by_account_id`. -/
def validatorByAccount (st : ChainState) (epoch : EpochId) (a : AccountId) :
    Result ValidatorStake := do
  match (← st.epoch epoch).info.getValidatorByAccount a with
  | some v =>
    pure v
  | none =>
    fail "NotAValidator" a.val

/-- `compute_bp_hash`: the hash of the block producers of an epoch (versioned format). -/
def bpHashOf (st : ChainState) (epoch : EpochId) : Result CryptoHash := do
  pure (bpHash (← st.blockProducersOrdered epoch))

end ChainState

/-! ### Recording a block -/

/-- `BlockInfo::from_header` for a protocol with dynamic resharding (`BlockInfo::V4`), with the
epoch fields still unset. -/
def blockInfoOf (hash : CryptoHash) (v : HeaderView) (lastFinalizedHeight : BlockHeight) :
    BlockInfoV4 :=
  { hash, height := v.height, lastFinalizedHeight, lastFinalBlockHash := v.lastFinalBlock,
    prevHash := v.prevHash, epochFirstBlock := CryptoHash.zero, epochId := ⟨CryptoHash.zero⟩,
    proposals := v.prevValidatorProposals, chunkMask := v.chunkMask,
    latestProtocolVersion := v.latestProtocolVersion, totalSupply := v.totalSupply,
    timestampNanosec := v.timestamp, chunkEndorsements := v.chunkEndorsements.getD ⟨#[]⟩,
    shardSplit := v.shardSplit }

/-- The block merkle tree of the block built on `prev` (`update_and_save_block_merkle_tree`). -/
def nextTree (prevHash : CryptoHash) (prevTree : PartialMerkleTree) : PartialMerkleTree :=
  prevTree.insert prevHash

namespace ChainState

/-- `ChainStoreUpdate`/`EpochManager::record_block_info_impl` for a block whose parent is known:
the `BlockInfo` with its epoch id and first block, and the block merkle tree. The block is
inserted first so that the epoch questions about it can be asked. -/
def record (st : ChainState) (header : BlockHeader) (v : HeaderView)
    (chunks : Array ShardChunkHeader) : Result ChainState := do
  let hash := header.hash
  let prev ← st.block v.prevHash
  let lastFinalized ←
    if v.lastFinalBlock == CryptoHash.zero then
      pure st.config.genesisHeight
    else
      pure (← st.block v.lastFinalBlock).info.height
  let info := blockInfoOf hash v lastFinalized
  let info ←
    if prev.info.prevHash == CryptoHash.zero then
      pure
          { info with
            epochId := ⟨CryptoHash.zero⟩, epochFirstBlock := hash }
    else if ← st.isNextBlockInNextEpoch prev.info then
      let first ← st.block prev.info.epochFirstBlock
      pure
          { info with
            epochId := ⟨first.info.prevHash⟩, epochFirstBlock := hash }
    else
      pure
          { info with
            epochId := prev.info.epochId, epochFirstBlock := prev.info.epochFirstBlock }
  let rec_ : BlockRec :=
    { hash, header, view := v, chunks, info, tree := nextTree prev.hash prev.tree }
  let (head, headHeight) :=
    if v.height > st.headHeight then (hash, v.height) else (st.head, st.headHeight)
  pure
      { st with
        blocks := st.blocks.insert hash.bytes rec_, head, headHeight }

end ChainState

end Near.Node.Chain
