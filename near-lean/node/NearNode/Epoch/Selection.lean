import NearNode.Epoch.Config

/-!
# Validator selection and shard assignment

`proposals_to_epoch_info` (`chain/epoch-manager/src/validator_selection.rs`) and
`assign_chunk_producers_to_shards` (`shard_assignment/mod.rs`) at the pinned nearcore, for the
strategies a static shard layout needs: `Fresh` (the genesis epoch) and `CarryOver`. A change of
layout (`StickyResharding`) is not represented. Where nearcore panics the functions return an
`Except`.
-/

namespace Near.Node.Epoch

open Near.Node Near.Node.Chain Borsh

/-- `gen_range(0..n)` on `usize` (64 bits): `UniformInt::sample_single_inclusive` over `u64`. -/
def genRangeU64 (r : ChaCha20Rng) (n : Nat) : Nat × ChaCha20Rng :=
  let zone := ((n <<< (63 - n.log2)) % 2 ^ 64 + 2 ^ 64 - 1) % 2 ^ 64
  let rec go : Nat → ChaCha20Rng → Nat × ChaCha20Rng
    | 0, r => (0, r)
    | fuel + 1, r =>
      let (v, r) := r.nextU64
      let m := v.toNat * n
      if m % 2 ^ 64 ≤ zone then (m >>> 64, r) else go fuel r
  go 4096 r

/-- `EpochInfo::shard_assignment_rng`. -/
def shardAssignmentRng (seed : RngSeed) : ChaCha20Rng :=
  .fromSeed (CryptoHash.hash (seed.bytes ++ "shard_assignment_shuffling_rng".toUTF8)).bytes

/-- `AssignmentStrategy`. -/
inductive Strategy where
  | carryOver
  | fresh
  deriving BEq, Inhabited

/-- `ValidatorsFirstShardAssignmentItem`: ordered by validators, stake, then shard index. -/
structure HeapItem where
  validators : Nat
  stake : Nat
  shardIndex : Nat
  deriving Inhabited

private def HeapItem.lt (a b : HeapItem) : Bool :=
  a.validators < b.validators ||
    (a.validators == b.validators &&
      (a.stake < b.stake || (a.stake == b.stake && a.shardIndex < b.shardIndex)))

/-- The smallest item of a heap and the heap without it. -/
private def popMin (heap : Array HeapItem) : Option (HeapItem × Array HeapItem) :=
  if heap.isEmpty then none
  else
    let i :=
      (List.range heap.size).foldl (fun best j => if (heap[j]!).lt (heap[best]!) then j else best) 0
    some (heap[i]!, heap.eraseIdx! i)

/-- `assign_to_satisfy_shards`: producers may repeat when there are too few. -/
def assignToSatisfyShards (producers : Array ValidatorStake) (numShards minPerShard : Nat) :
    Except String (Array (Array ValidatorStake)) := do
  let mut result : Array (Array ValidatorStake) := Array.replicate numShards #[]
  let mut heap : Array HeapItem :=
    (Array.range numShards).map fun i => { validators := 0, stake := 0, shardIndex := i }
  let mut seen : Array (Nat × Nat) := #[]
  let mut next := 0
  if producers.isEmpty then
    throw "no chunk producers"
  let mut fuel := 1000000
  repeat
    let some (top, _) := popMin heap | throw "empty shard heap"
    if top.validators ≥ minPerShard then
      break
    fuel := fuel - 1
    if fuel == 0 then
      throw "shard assignment does not terminate"
    let cpIndex := next % producers.size
    let cp := producers[cpIndex]!
    next := next + 1
    let mut buffer : Array HeapItem := #[]
    repeat
      match popMin heap with
      | none =>
        break
      | some (top, rest) =>
        if top.validators ≥ minPerShard then
          break
        else if !seen.contains (top.shardIndex, cpIndex) then
          seen := seen.push (top.shardIndex, cpIndex)
          heap :=
            rest.push
              { top with
                validators := top.validators + 1, stake := top.stake + cp.stake.val }
          result := result.modify top.shardIndex (·.push cp)
          break
        else
          buffer := buffer.push top
          heap := rest
    heap := heap ++ buffer
  return result

/-- `assign_to_balance_shards` with the `CarryOver` or `Fresh` seeding. -/
def assignToBalanceShards (producers : Array ValidatorStake)
    (numShards minPerShard changesLimit : Nat) (seed : RngSeed) (strategy : Strategy)
    (prev : Array (Array ValidatorStake)) : Except String (Array (Array ValidatorStake)) := do
  let numProducers := producers.size
  let indexOf (a : AccountId) : Option Nat := producers.findIdx? (·.accountId == a)
  let mut assignment : Array (Array Nat) := Array.replicate numShards #[]
  if strategy == .carryOver then
    for s in [0:min prev.size numShards] do
      assignment := assignment.set! s ((prev[s]!).filterMap fun v => indexOf v.accountId)
  let old := assignment.foldl (fun acc a => acc ++ a) #[]
  let newValidators := (Array.range numProducers).filter fun i => !old.contains i
  -- the shard set, ordered by (count, index)
  let ordered (assignment : Array (Array Nat)) : Array (Nat × Nat) :=
    ((Array.range numShards).map fun s => ((assignment[s]!).size, s)).qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut newAssignments := newValidators.size
  for v in newValidators do
    let (_, s) := (ordered assignment)[0]!
    assignment := assignment.modify s (·.push v)
  let mut rng := shardAssignmentRng seed
  let hardLimit := max numProducers changesLimit
  repeat
    let set := ordered assignment
    let (minNum, minShard) := set[0]!
    let (maxNum, maxShard) := set[set.size - 1]!
    let minimalSatisfied := minNum ≥ minPerShard
    let balanced := maxNum - minNum ≤ 1
    if minimalSatisfied && (balanced || newAssignments ≥ changesLimit) then
      break
    if newAssignments > hardLimit then
      throw "could not balance the shards"
    if minShard == maxShard then
      throw "minimal shard and maximal shard are the same"
    let (pos, r) := genRangeU64 rng (assignment[maxShard]!).size
    rng := r
    let row := assignment[maxShard]!
    let validator := row[pos]!
    -- `swap_remove`
    let row := (row.set! pos row[row.size - 1]!).pop
    assignment := assignment.set! maxShard row
    assignment := assignment.modify minShard (·.push validator)
    newAssignments := newAssignments + 1
  return assignment.map fun a => (a.qsort (· < ·)).map fun i => producers[i]!

/-- `assign_chunk_producers_to_shards`; `none` is nearcore's `NotEnoughValidators`. -/
def assignChunkProducersToShards (producers : Array ValidatorStake)
    (numShards minPerShard changesLimit : Nat) (seed : RngSeed) (strategy : Strategy)
    (prev : Array (Array ValidatorStake)) : Except String (Option (Array (Array ValidatorStake))) :=
  do
  if producers.size < minPerShard then
    return none
  if producers.size < minPerShard * numShards then
    return some (← assignToSatisfyShards producers numShards minPerShard)
  else
    return some
        (← assignToBalanceShards producers numShards minPerShard changesLimit seed strategy prev)

/-! ### Selecting validators from proposals -/

/-- `OrderedValidatorStake` order, best first: the larger stake, then the smaller account id. -/
def orderProposals (ps : Array ValidatorStake) : Array ValidatorStake :=
  ps.qsort fun a b =>
    a.stake.val > b.stake.val || (a.stake.val == b.stake.val && a.accountId.val < b.accountId.val)

/-- `select_validators`: the leading proposals that hold more than the minimum stake ratio of the
total so far, and the threshold stake to be included. -/
def selectValidators (sorted : Array ValidatorStake) (maxSelected : Nat) (ratio : Rat) :
    Array ValidatorStake × Nat :=
  Id.run do
    let n := min maxSelected sorted.size
    let mut total := 0
    let mut selected : Array ValidatorStake := #[]
    for i in [0:n] do
      let p := sorted[i]!
      let t := total + p.stake.val
      if t > 0 && p.stake.val * ratio.denom > ratio.numer * t then
        selected := selected.push p
        total := t
      else
        break
    let threshold :=
      if selected.size == maxSelected then (selected.back?.map (·.stake.val)).getD 0 + 1
      else
        -- `ceil(ratio * total / (1 - ratio))`
        let num := ratio.numer * total
        let den := ratio.denom - ratio.numer
        (num + den - 1) / den
    return (selected, threshold)

/-- `apply_epoch_update_to_proposals`: the proposals that count for the next epoch and the stake
changes. `kickout` and `reward` are keyed by account. -/
def applyEpochUpdateToProposals (proposals : Array ValidatorStake) (prev : EpochInfoView)
    (reward : Array (AccountId × Balance)) (kickout : Array (AccountId × ValidatorKickoutReason)) :
    Array ValidatorStake × Array (AccountId × Balance) :=
  Id.run do
    let mut byAccount : Array (AccountId × ValidatorStake) := #[]
    let mut stakeChange : Array (AccountId × Balance) := #[]
    for p in proposals do
      let a := p.accountId
      if (assocFind? kickout a).isSome then
        stakeChange := assocInsert stakeChange a ⟨0⟩
      else
        match assocFind? prev.validatorKickout a with
        | some (.protocolVersionTooOld _ _) =>
          pure ()
        | _ =>
          stakeChange := assocInsert stakeChange a p.stake
          byAccount := assocInsert byAccount a p
    for r in prev.validators do
      let a := r.accountId
      if (assocFind? kickout a).isSome then
        stakeChange := assocInsert stakeChange a ⟨0⟩
      else
        let p := (assocFind? byAccount a).getD r
        let p :=
          match assocFind? reward a with
          | some rw =>
            match p with
            | .v1 v => ValidatorStake.v1 { v with stake := ⟨v.stake.val + rw.val⟩ }
          | none => p
        byAccount := assocInsert byAccount a p
        stakeChange := assocInsert stakeChange a p.stake
    return (byAccount.map (·.2), stakeChange)

/-- `StakeWeightedIndex` over the stakes of validators `ids`. -/
def stakeWeights (validators : Array ValidatorStake) (ids : Array ValidatorId) :
    Except String StakeWeightedIndex :=
  match StakeWeightedIndex.new (ids.map fun i => (validators[i.toNat]!).stake) with
  | some s => pure s
  | none => throw "stake weighted index overflows"

/-- `EpochError` variants `proposals_to_epoch_info` returns. -/
inductive SelectionError where
  | notEnoughValidators
  | other (message : String)

/-- `proposals_to_epoch_info` for protocol 85 and later (an `EpochInfo::V5`). -/
def proposalsToEpochInfo (cfg : EpochConfig) (seed : RngSeed) (prev : EpochInfo)
    (proposals : Array ValidatorStake) (kickout : Array (AccountId × ValidatorKickoutReason))
    (reward : Array (AccountId × Balance)) (minted : Balance) (protocolVersion : ProtocolVersion)
    (layout : ShardLayout) (strategy : Strategy) (lastResharding : Option EpochHeight) :
    Except SelectionError EpochInfo := do
  let prevView := prev.view
  let numShards := layout.numShards.toNat
  let (candidates, stakeChange0) := applyEpochUpdateToProposals proposals prevView reward kickout
  let ordered := orderProposals candidates
  let ratio := cfg.minimumStakeRatio
  let (chunkProducers, cpT) := selectValidators ordered cfg.numChunkProducerSeats ratio
  let (blockProducers, bpT) := selectValidators ordered cfg.numBlockProducerSeats ratio
  let (chunkValidators, cvT) := selectValidators ordered cfg.numChunkValidatorSeats ratio
  let selected (a : AccountId) : Bool :=
    chunkProducers.any (·.accountId == a) || blockProducers.any (·.accountId == a) ||
      chunkValidators.any (·.accountId == a)
  let unselected := ordered.filter fun p => !selected p.accountId
  let threshold := min bpT (min cpT cvT)
  let mut stakeChange := stakeChange0
  let mut kickout := kickout
  for p in unselected do
    stakeChange := assocInsert stakeChange p.accountId ⟨0⟩
    if (prev.getValidatorId p.accountId).isSome then
      kickout := assocInsert kickout p.accountId (.notEnoughStake p.stake ⟨threshold⟩)
  -- local validator indices: chunk producers, then block producers, then chunk validators
  let mut allValidators : Array ValidatorStake := #[]
  for v in chunkProducers ++ blockProducers ++ chunkValidators do
    unless allValidators.any (·.accountId == v.accountId) do
      allValidators := allValidators.push v
  let indexOf (a : AccountId) : ValidatorId :=
    ((allValidators.findIdx? (·.accountId == a)).getD 0).toUInt64
  let prevAssignment : Array (Array ValidatorStake) :=
    prevView.chunkProducers.map fun ids => ids.filterMap fun i => prevView.validators[i.toNat]?
  let assignment ←
    match
      assignChunkProducersToShards chunkProducers numShards cfg.minimumValidatorsPerShard
        cfg.chunkProducerAssignmentChangesLimit seed strategy prevAssignment with
    | .error m =>
      throw (.other m)
    | .ok none =>
      throw .notEnoughValidators
    | .ok (some a) =>
      pure a
  let mut settlement : Array (Array ValidatorId) :=
    assignment.map fun vs => vs.map fun v => indexOf v.accountId
  if cfg.shuffleShardAssignmentForChunkProducers then
    settlement := ((shardAssignmentRng seed).shuffle settlement).1
  let blockSettlement := blockProducers.map fun b => indexOf b.accountId
  let mandates ←
    match
      ValidatorMandates.new ⟨cfg.targetValidatorMandatesPerShard.toUInt64, numShards.toUInt64⟩
        allValidators with
    | some m =>
      pure m
    | none =>
      throw (.other "validator mandates")
  let bpSampler ←
    match stakeWeights allValidators blockSettlement with
    | .ok s =>
      pure s
    | .error m =>
      throw (.other m)
  let cpSamplers ←
    match settlement.mapM (stakeWeights allValidators) with
    | .ok s =>
      pure s
    | .error m =>
      throw (.other m)
  let validatorToIndex := toSortedMap (allValidators.mapIdx fun i v => (v.accountId, i.toUInt64))
  return .v5
      { epochHeight := (prevView.epochHeight + 1).toUInt64, validators := allValidators,
        validatorToIndex, blockProducersSettlement := blockSettlement,
        chunkProducersSettlement := settlement, stakeChange := toSortedMap stakeChange,
        validatorReward := toSortedMap reward, validatorKickout := toSortedMap kickout,
        mintedAmount := minted, seatPrice := ⟨threshold⟩, protocolVersion, shardLayout := layout,
        lastResharding, rngSeed := seed, blockProducersSampler := bpSampler,
        chunkProducersSampler := cpSamplers, validatorMandates := mandates }

end Near.Node.Epoch
