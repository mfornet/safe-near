import NearNode.Epoch.Selection

/-!
# The epoch manager's computation

`EpochInfoAggregator` (`chain/epoch-manager/src/epoch_info_aggregator.rs`), `RewardCalculator`
(`reward_calculator.rs`), the online ratio (`validator_stats.rs`) and `EpochManager`
(`lib.rs`): `collect_blocks_info`, `compute_validators_to_reward_and_kickout`, `finalize_epoch`,
`initialize_genesis_epoch_info` and `compute_stake_return_info`, at the pinned nearcore.

nearcore keeps the aggregator incrementally (`update_epoch_info_aggregator_upto_final`) and
merges the part past the last final block when an epoch ends. The result is the aggregate over
every block of the epoch up to its last, which is what this module computes from the chain
state; with one chain and no forks the two agree.
-/

namespace Near.Node.Epoch

open Near.Node Near.Node.Chain Borsh

/-! ### Statistics -/

/-- `ValidatorStats::less_than`. -/
def lessThan (produced expected threshold : Nat) : Bool :=
  produced * 100 < threshold * expected

/-- `BlockChunkValidatorStats` over unbounded numbers. -/
structure Stats where
  blockProduced : Nat := 0
  blockExpected : Nat := 0
  chunkProduced : Nat := 0
  chunkExpected : Nat := 0
  endorsementProduced : Nat := 0
  endorsementExpected : Nat := 0
  deriving Inhabited, BEq

def Stats.toNode (s : Stats) : BlockChunkValidatorStats :=
  { blockStats := ⟨s.blockProduced.toUInt64, s.blockExpected.toUInt64⟩,
    chunkStats :=
      { production := ⟨s.chunkProduced.toUInt64, s.chunkExpected.toUInt64⟩,
        endorsement := ⟨s.endorsementProduced.toUInt64, s.endorsementExpected.toUInt64⟩ } }

/-- `get_validator_online_ratio`: the average of the block, chunk and endorsement ratios as
`(numerator, denominator)`, unreduced. -/
def onlineRatio (s : Stats) (cutoff : Option Nat) : Nat × Nat :=
  let eb := s.blockExpected
  let ec := s.chunkExpected
  let (pe, ee) :=
    if s.endorsementExpected == 0 then (0, 0)
    else
      match cutoff with
      | some t => if lessThan s.endorsementProduced s.endorsementExpected t then (0, 1) else (1, 1)
      | none => (s.endorsementProduced, s.endorsementExpected)
  let pb := s.blockProduced
  let pc := s.chunkProduced
  if eb == 0 && ec == 0 && ee == 0 then (0, 1)
  else
    if eb == 0 && ec == 0 then (pe, ee)
    else
      if eb == 0 && ee == 0 then (pc, ec)
      else
        if ec == 0 && ee == 0 then (pb, eb)
        else
          if ee == 0 then (pb * ec + pc * eb, 2 * ec * eb)
          else
            if eb == 0 then (pe * ec + pc * ee, 2 * ec * ee)
            else
              if ec == 0 then (pe * eb + pb * ee, 2 * eb * ee)
              else (pb * ec * ee + pc * eb * ee + pe * eb * ec, 3 * ec * eb * ee)

/-! ### Rewards -/

/-- `RewardCalculator::calculate_reward`: the reward of every validator in `stats` (and of the
treasury) and the minted amount. `stakes` are the validators' stakes in the epoch. -/
def calculateReward (p : RewardParams) (stats : Array (AccountId × Stats))
    (stakes : Array (AccountId × Balance)) (totalSupply : Nat) (epochDuration : Nat)
    (minThreshold maxThreshold : Rat) (cutoff : Nat) (maxInflation : Rat) :
    Except String (Array (AccountId × Balance) × Balance) := do
  let protocolRate : Rat := if p.genesisProtocolVersion == 29 then ⟨1, 10⟩ else p.protocolRewardRate
  let totalReward :=
    maxInflation.numer * totalSupply * epochDuration /
      (p.numSecondsPerYear * maxInflation.denom * 1000000000)
  let treasury := totalReward * protocolRate.numer / protocolRate.denom
  let mut res : Array (AccountId × Balance) := #[(p.protocolTreasuryAccount, ⟨treasury⟩)]
  if stats.isEmpty then
    return (res, ⟨0⟩)
  let validatorReward := totalReward - treasury
  let mut actual := treasury
  let totalStake := stakes.foldl (fun s (_, b) => s + b.val) 0
  for (account, st) in stats do
    let (numer, denom) := onlineRatio st (some cutoff)
    let reward :=
      if
          numer * minThreshold.denom < minThreshold.numer * denom ||
            (st.chunkExpected == 0 && st.blockExpected == 0 && st.endorsementExpected == 0) then
        0
      else
        let stake := (assocFind? stakes account).map (·.val)
        match stake with
        | none => 0
        | some stake =>
          let onlineNumer :=
            maxThreshold.numer * minThreshold.denom - minThreshold.numer * maxThreshold.denom
          let upNumer0 :=
            (numer * minThreshold.denom - minThreshold.numer * denom) * maxThreshold.denom
          let upDenom := onlineNumer * denom
          let upNumer := if upNumer0 > upDenom then upDenom else upNumer0
          validatorReward * upNumer * stake / upDenom / totalStake
    res := assocInsert res account ⟨reward⟩
    actual := actual + reward
  return (res, ⟨actual⟩)

/-! ### The aggregate of an epoch -/

/-- `ChunkStats` of one validator on one shard. -/
structure ChunkSt where
  produced : Nat := 0
  expected : Nat := 0
  endorsementProduced : Nat := 0
  endorsementExpected : Nat := 0
  deriving Inhabited

/-- `EpochInfoAggregator`. -/
structure Aggregator where
  blockTracker : Std.HashMap Nat (Nat × Nat) := {}
  shardTracker : Std.HashMap UInt64 (Std.HashMap Nat ChunkSt) := {}
  versionTracker : Std.HashMap Nat ProtocolVersion := {}
  allProposals : Array (AccountId × ValidatorStake) := #[]
  deriving Inhabited

/-- Whether bit `i` of an endorsement bitmap row is set. -/
def bitSet (row : ByteArray) (i : Nat) : Bool :=
  (row.get! (i / 8)).toNat >>> (i % 8) % 2 == 1

/-- `EpochInfoAggregator::update_tail`: add the block `info`, whose predecessor has height
`prevHeight`, to an aggregator that holds the blocks after it. -/
def Aggregator.updateTail (a : Aggregator) (info : BlockInfoV4) (epoch : EpochInfo)
    (layout : ShardLayout) (prevHeight : BlockHeight) : Except String Aggregator := do
  let mut a := a
  -- Step 1: block production, including the heights nobody produced
  let height := info.height.toNat
  for h in [prevHeight.toNat + 1:height + 1] do
    let some bp := epoch.sampleBlockProducer h.toUInt64 | throw "block producer selection failed"
    let (p, e) := (a.blockTracker[bp.toNat]?).getD (0, 0)
    a :=
      { a with
        blockTracker := a.blockTracker.insert bp.toNat (p + (if h == height then 1 else 0), e + 1) }
  -- Step 2: chunk production and endorsements
  let atHeight := (prevHeight + 1)
  let some validators :=
    epoch.sampleChunkValidators atHeight | throw "chunk validator selection failed"
  for shardIndex in [0:info.chunkMask.size] do
    let mask := info.chunkMask[shardIndex]!
    let some shardId := layout.getShardId shardIndex | throw "shard index out of range"
    let some producer := epoch.sampleChunkProducer layout shardId atHeight
      | throw "chunk producer selection failed"
    let mut tracker := (a.shardTracker[shardId]?).getD {}
    let old := (tracker[producer.toNat]?).getD {}
    tracker :=
      tracker.insert producer.toNat
        { old with
          produced := old.produced + (if mask then 1 else 0), expected := old.expected + 1 }
    let ids := ((validators[shardIndex]?).getD #[]).map (·.1)
    let row := (info.chunkEndorsements.inner[shardIndex]?).getD ByteArray.empty
    let bits : Array Bool :=
      if mask then (Array.range (row.size * 8)).map (bitSet row) else Array.replicate ids.size false
    for j in [0:min ids.size bits.size] do
      let v := ids[j]!.toNat
      let old := (tracker[v]?).getD {}
      tracker :=
        tracker.insert v
          { old with
            endorsementProduced := old.endorsementProduced + (if bits[j]! then 1 else 0),
            endorsementExpected := old.endorsementExpected + 1 }
    a := { a with shardTracker := a.shardTracker.insert shardId tracker }
  -- Step 3: the version of the block producer
  let some bp := epoch.sampleBlockProducer info.height | throw "block producer selection failed"
  unless a.versionTracker.contains bp.toNat do
    a := { a with versionTracker := a.versionTracker.insert bp.toNat info.latestProtocolVersion }
  -- Step 4: proposals (the aggregator walks back from the last block, so the first one wins)
  for p in info.proposals do
    if (assocFind? a.allProposals p.accountId).isNone then
      a := { a with allProposals := a.allProposals.push (p.accountId, p) }
  return a

/-! ### Summaries and the next epoch -/

/-- `EpochSummary`. -/
structure Summary where
  prevEpochLastBlockHash : CryptoHash
  allProposals : Array ValidatorStake
  validatorKickout : Array (AccountId × ValidatorKickoutReason)
  stats : Array (AccountId × Stats)
  nextNextEpochVersion : ProtocolVersion
  deriving Inhabited

/-- `compute_validators_to_reward_and_kickout`: the statistics of every validator and the
validators to kick out. -/
def computeValidatorsToRewardAndKickout (cfg : EpochConfig) (epoch : EpochInfoView)
    (agg : Aggregator) (prevKickout : Array (AccountId × ValidatorKickoutReason)) :
    Array (AccountId × Stats) × Array (AccountId × ValidatorKickoutReason) :=
  Id.run do
    let mut stats : Array (AccountId × Stats) := #[]
    let mut totalStake := 0
    let mut maxProduced := 0
    let mut maxValidator : Option AccountId := none
    for i in [0:epoch.validators.size] do
      let v := epoch.validators[i]!
      let (bp, be) := (agg.blockTracker[i]?).getD (0, 0)
      let mut s : Stats := { blockProduced := bp, blockExpected := be }
      for (_, tracker) in agg.shardTracker.toList do
        if let some c := tracker[i]? then
          s :=
            { s with
              chunkProduced := s.chunkProduced + c.produced,
              chunkExpected := s.chunkExpected + c.expected,
              endorsementProduced := s.endorsementProduced + c.endorsementProduced,
              endorsementExpected := s.endorsementExpected + c.endorsementExpected }
      totalStake := totalStake + v.stake.val
      let already := (assocFind? prevKickout v.accountId).isSome
      if (maxValidator.isNone || bp > maxProduced) && !already then
        maxProduced := bp
        maxValidator := some v.accountId
      stats := assocInsert stats v.accountId s
    -- validators by online ratio, then stake, then account id (ascending)
    let stakeOf (a : AccountId) : Nat :=
      ((epoch.validators.find? (·.accountId == a)).map (·.stake.val)).getD 0
    let sorted :=
      stats.qsort fun (a, sa) (b, sb) =>
        let (na, da) := onlineRatio sa none
        let (nb, db) := onlineRatio sb none
        if na * db != nb * da then na * db < nb * da
        else if stakeOf a != stakeOf b then stakeOf a < stakeOf b else a.val < b.val
    let exemptPerc := 100 - cfg.validatorMaxKickoutStakePerc
    let minKeep := totalStake * exemptPerc / 100
    let mut exempted : Array AccountId := #[]
    let mut exemptedStake := 0
    for (a, _) in sorted.reverse do
      if exemptedStake ≥ minKeep then
        break
      if (assocFind? prevKickout a).isNone then
        exemptedStake := exemptedStake + stakeOf a
        exempted := exempted.push a
    let mut allKicked := true
    let mut kickout : Array (AccountId × ValidatorKickoutReason) := #[]
    for (a, s) in stats do
      if exempted.contains a then
        allKicked := false
        continue
      if lessThan s.blockProduced s.blockExpected cfg.blockProducerKickoutThreshold then
        kickout :=
          assocInsert kickout a (.notEnoughBlocks s.blockProduced.toUInt64 s.blockExpected.toUInt64)
      if lessThan s.chunkProduced s.chunkExpected cfg.chunkProducerKickoutThreshold then
        if (assocFind? kickout a).isNone then
          kickout :=
            assocInsert kickout a
              (.notEnoughChunks s.chunkProduced.toUInt64 s.chunkExpected.toUInt64)
      let chunkValidatorOnly := s.blockExpected == 0 && s.chunkExpected == 0
      if
          chunkValidatorOnly &&
            lessThan s.endorsementProduced s.endorsementExpected
              cfg.chunkValidatorOnlyKickoutThreshold then
        if (assocFind? kickout a).isNone then
          kickout :=
            assocInsert kickout a
              (.notEnoughChunkEndorsements s.endorsementProduced.toUInt64
                s.endorsementExpected.toUInt64)
      let already := (assocFind? prevKickout a).isSome
      if (assocFind? kickout a).isNone && !already then
        allKicked := false
    if allKicked then
      if let some v := maxValidator then
        kickout := kickout.filter (·.1 != v)
    return (stats, kickout)

/-- The blocks of the epoch that ends with `last`, last to first, each with the height of its
predecessor (`aggregate_epoch_info_upto`). -/
def _root_.Near.Node.Chain.ChainState.epochBlocks (st : ChainState) (last : BlockRec) :
    Result (Array (BlockRec × BlockHeight)) := do
  let epoch := last.info.epochId
  let mut out : Array (BlockRec × BlockHeight) := #[]
  let mut cur := last
  repeat
    if cur.info.epochId != epoch || cur.info.prevHash == CryptoHash.zero then
      break
    let prev ← st.block cur.info.prevHash
    out := out.push (cur, prev.info.height)
    cur := prev
  return out

/-- `EpochManager::get_next_epoch_id_from_info`. -/
def _root_.Near.Node.Chain.ChainState.nextEpochIdOfInfo (st : ChainState) (info : BlockInfoV4) :
    Result EpochId := do
  let first ← st.block info.epochFirstBlock
  pure ⟨first.info.prevHash⟩

/-- `EpochManager::collect_blocks_info`. -/
def collectBlocksInfo (setup : Setup) (st : ChainState) (last : BlockRec) : Result Summary := do
  let epoch ← st.epoch last.info.epochId
  let nextId ← st.nextEpochIdOfInfo last.info
  let next ← st.epoch nextId
  let view := epoch.info.view
  let blocks ← st.epochBlocks last
  let mut agg : Aggregator := {}
  for (b, prevHeight) in blocks do
    match agg.updateTail b.info epoch.info epoch.layout prevHeight with
    | .ok a =>
      agg := a
    | .error m =>
      failOther m
  let nextView := next.info.view
  -- the stake of the distinct block producers
  let mut seen : Array ValidatorId := #[]
  let mut totalBp := 0
  for id in view.blockProducers do
    unless seen.contains id do
      seen := seen.push id
      totalBp := totalBp + ((view.validators[id.toNat]?).map (·.stake.val)).getD 0
  -- the protocol version vote
  let mut versions : Array (ProtocolVersion × Nat) := #[]
  for (id, version) in agg.versionTracker.toList do
    let stake := ((view.validators[id]?).map (·.stake.val)).getD 0
    let old := ((versions.find? (·.1 == version)).map (·.2)).getD 0
    versions := assocInsert versions version (old + stake)
  let protocolVersion := nextView.protocolVersion
  let cfg := setup.config
  let nextNextVersion :=
    match
      versions.foldl
        (fun (best : Option (ProtocolVersion × Nat)) (v, s) =>
          match best with
          | none => some (v, s)
          | some (_, bs) => if s ≥ bs then some (v, s) else best)
        none with
    | some (v, s) =>
      let threshold :=
        totalBp * cfg.protocolUpgradeStakeThreshold.numer / cfg.protocolUpgradeStakeThreshold.denom
      if s > threshold then v else protocolVersion
    | none => protocolVersion
  let mut kickout : Array (AccountId × ValidatorKickoutReason) := #[]
  for (id, version) in agg.versionTracker.toList do
    if version ≥ nextNextVersion then
      continue
    if let some v := view.validators[id]? then
      kickout := assocInsert kickout v.accountId (.protocolVersionTooOld version nextNextVersion)
  let mut proposals : Array ValidatorStake := #[]
  let sortedProposals := agg.allProposals.qsort fun a b => a.1.val < b.1.val
  for (account, proposal) in sortedProposals do
    if proposal.stake.val == 0 then
      if let some c := assocFind? nextView.stakeChange account then
        if c.val != 0 then
          kickout := assocInsert kickout account .unstaked
    proposals := proposals.push proposal
  let first ← st.block last.info.epochFirstBlock
  let (stats, offline) := computeValidatorsToRewardAndKickout cfg view agg nextView.validatorKickout
  for (a, r) in offline do
    kickout := assocInsert kickout a r
  return { prevEpochLastBlockHash := first.info.prevHash, allProposals := proposals,
           validatorKickout := kickout, stats, nextNextEpochVersion := nextNextVersion }

/-- `EpochManager::finalize_epoch`: the `EpochInfo` and shard layout of the epoch after next,
stored under the id of the hash of `last`, which is the last block of its epoch. -/
def finalizeEpoch (setup : Setup) (st : ChainState) (last : BlockRec) (rngSeed : RngSeed) :
    Result (EpochData × Summary) := do
  let summary ← collectBlocksInfo setup st last
  let epoch ← st.epoch last.info.epochId
  let view := epoch.info.view
  let cfg := setup.config
  let nextId ← st.nextEpochIdOfInfo last.info
  let next ← st.epoch nextId
  let nextView := next.info.view
  let first ← st.block last.info.epochFirstBlock
  let prevLast ← st.block first.info.prevHash
  if last.info.timestampNanosec ≤ prevLast.info.timestampNanosec then
    failOther "epoch duration is not positive"
  let duration := (last.info.timestampNanosec - prevLast.info.timestampNanosec).toNat
  let rewarded :=
    summary.stats.filter fun (a, _) =>
      match assocFind? summary.validatorKickout a with
      | some (.notEnoughBlocks ..) | some (.notEnoughChunks ..) |
        some (.notEnoughChunkEndorsements ..) => false
      | _ => true
  let stakes := view.validators.map fun v => (v.accountId, v.stake)
  let (reward, minted) ←
    match
      calculateReward setup.reward rewarded stakes last.info.totalSupply.val duration
        cfg.onlineMinThreshold cfg.onlineMaxThreshold cfg.chunkValidatorOnlyKickoutThreshold
        cfg.maxInflationRate with
    | .ok r =>
      pure r
    | .error m =>
      failOther m
  let nextNextLayout := cfg.shardLayout
  if nextNextLayout != next.layout then
    failOther "a change of shard layout is not represented"
  let lastResharding := nextView.lastResharding
  let info ←
    match
      proposalsToEpochInfo cfg rngSeed next.info summary.allProposals summary.validatorKickout
        reward minted summary.nextNextEpochVersion nextNextLayout .carryOver lastResharding with
    | .ok i =>
      pure i
    | .error .notEnoughValidators =>
      pure next.info.bumpHeight
    | .error (.other m) =>
      failOther m
  pure ({ info, layout := nextNextLayout }, summary)

/-- The `EpochInfo` of the genesis epoch (`make_genesis_epoch_info`): the validators of the
genesis config as proposals, no rewards. -/
def genesisEpochInfo (setup : Setup) (validators : Array ValidatorStake) : Result EpochData := do
  let cfg := setup.config
  let reward := #[(setup.reward.protocolTreasuryAccount, (⟨0⟩ : Balance))]
  match
    proposalsToEpochInfo cfg ⟨ByteArray.mk (Array.replicate 32 0)⟩ (.v2 default) validators #[]
      reward ⟨0⟩ setup.reward.genesisProtocolVersion cfg.shardLayout .fresh none with
  | .ok info =>
    pure { info, layout := cfg.shardLayout }
  | .error .notEnoughValidators =>
    failOther "not enough validators for the genesis epoch"
  | .error (.other m) =>
    failOther m

/-- `compute_stake_return_info`: for the epoch that ended with block `last` (an epoch's last
block), the maximum of the stakes of the past three epochs by account and the validator rewards
of the epoch. -/
def computeStakeReturnInfo (st : ChainState) (last : BlockRec) :
    Result (Array (AccountId × Balance) × Array (AccountId × Balance)) := do
  let nextNext ← st.epoch ⟨last.hash⟩
  let reward := nextNext.info.view.validatorReward
  let nextId ← st.nextEpochIdOfInfo last.info
  let prevPrev := (← st.epoch last.info.epochId).info.view.stakeChange
  let prev := (← st.epoch nextId).info.view.stakeChange
  let cur := nextNext.info.view.stakeChange
  let accounts :=
    (prevPrev ++ prev ++ cur).foldl
      (fun (acc : Array AccountId) (a, _) => if acc.contains a then acc else acc.push a) #[]
  let value (m : Array (AccountId × Balance)) (a : AccountId) : Nat :=
    ((assocFind? m a).map (·.val)).getD 0
  let info :=
    accounts.map fun a =>
      (a, (⟨max (value prevPrev a) (max (value prev a) (value cur a))⟩ : Balance))
  pure (info, reward)

end Near.Node.Epoch
