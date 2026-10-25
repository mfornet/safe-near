import NearNode.Chain.Header
import NearNode.Epoch.Manager

/-!
# Accepting a block with the epoch manager

`acceptBlock` validates a block and records its `BlockInfo`; `EpochManager::record_block_info`
then finalizes the epoch if the block is the last of its epoch, which stores the `EpochInfo` of the
epoch after next under the id of the hash of this block. `processBlock` does both, so that the
epochs of a chain are computed and no longer given.
-/

namespace Near.Node.Epoch

open Near.Node Near.Node.Chain

/-- What finalizing an epoch produced. -/
structure Finalized where
  epochId : EpochId
  data : EpochData
  summary : Summary

/-- If the recorded block ends its epoch, compute and store the epoch two ahead
(`EpochManager::record_block_info`). -/
def finishBlock (setup : Setup) (st : ChainState) (header : BlockHeader) :
    Result (ChainState × Option Finalized) := do
  let hash := header.hash
  let rec_ ← st.block hash
  if ← st.isNextBlockInNextEpoch rec_.info then
    let some v := header.view? | fail "Unsupported" "header version"
    let (data, summary) ← finalizeEpoch setup st rec_ ⟨v.randomValue.bytes⟩
    let epochId : EpochId := ⟨hash⟩
    pure ({ st with epochs := st.epochs.insert hash.bytes data }, some { epochId, data, summary })
  else
    pure (st, none)

/-- Accept a block; if it ends its epoch, compute and store the epoch two ahead. -/
def processBlock (setup : Setup) (st : ChainState) (block : Block) :
    Result (ChainState × Option Finalized) := do
  finishBlock setup (← acceptBlock st block) block.header

/-- Accept a header (`Chain::sync_block_headers`); a header that ends its epoch finalizes the
epoch, as `add_validator_proposals` does for a header in nearcore. -/
def processHeader (setup : Setup) (st : ChainState) (header : BlockHeader) :
    Result (ChainState × Option Finalized) := do
  finishBlock setup (← acceptHeader st header) header

end Near.Node.Epoch

namespace Near.Node.Epoch

open Near.Node Near.Node.Chain

/-- `ValidatorAccountsUpdate` (`runtime/runtime/src/lib.rs`) as `NightshadeRuntime::process_state_update`
builds it for one shard: the part of the epoch's stake returns, rewards and last proposals that
belongs to the shard. -/
structure AccountsUpdate where
  stakeInfo : Array (AccountId × Balance)
  validatorRewards : Array (AccountId × Balance)
  lastProposals : Array (AccountId × Balance)
  protocolTreasury : Option AccountId
  deriving Inhabited

/-- The update of the chunk of `shard` that follows `prev`, or `none` unless the chunk starts an
epoch (`is_next_block_epoch_start(prev)`). `lastProposals` are `prev_validator_proposals` of the
chunk header. -/
def validatorAccountsUpdate (setup : Setup) (st : ChainState) (prev : CryptoHash) (shard : ShardId)
    (lastProposals : Array ValidatorStake) : Result (Option AccountsUpdate) := do
  if !(← st.isNextBlockEpochStart prev) then
    return none
  let epochId ← st.epochIdFromPrevBlock prev
  let layout := (← st.epoch epochId).layout
  let (stakeInfo, rewards) ← computeStakeReturnInfo st (← st.block prev)
  let mine (a : AccountId) : Bool := layout.accountIdToShardId a == some shard
  let mut proposals : Array (AccountId × Balance) := #[]
  for v in lastProposals do
    if mine v.accountId then
      proposals := assocInsert proposals v.accountId v.stake
  let treasury := setup.reward.protocolTreasuryAccount
  pure
      (some
        { stakeInfo := stakeInfo.filter (mine ·.1), validatorRewards := rewards.filter (mine ·.1),
          lastProposals := proposals,
          protocolTreasury := if mine treasury then some treasury else none })

end Near.Node.Epoch
