import NearNode.Chain.State

/-!
# Epoch configuration and the views of an `EpochInfo` the epoch manager reads

`EpochConfig` (`core/primitives/src/epoch_manager.rs`) as `EpochConfig::genesis_test` builds it,
which is what `EpochManager::new_arc_handle` uses on a chain that has no `epoch_configs` directory
and is neither mainnet nor testnet (the localnets of the corpus), and the parameters of
`RewardCalculator::new`. `EpochInfoView` is the part of any `EpochInfo` version that
`validator_selection.rs` and `lib.rs` read; `EpochInfo::new` for protocol 85 and later is `V5`.
-/

namespace Near.Node.Epoch

open Near.Node Near.Node.Chain Borsh

/-- `Rational32`: kept as written (`Ratio::new_raw`) or reduced by the caller. -/
structure Rat where
  numer : Nat
  denom : Nat
  deriving BEq, Inhabited, Repr

/-- `a < b` for positive denominators. -/
def Rat.lt (a b : Rat) : Bool :=
  a.numer * b.denom < b.numer * a.denom

/-- `EpochConfig`, the fields the epoch manager reads. -/
structure EpochConfig where
  epochLength : Nat
  numBlockProducerSeats : Nat
  numChunkProducerSeats : Nat := 100
  numChunkValidatorSeats : Nat := 300
  minimumValidatorsPerShard : Nat := 1
  /-- `minimum_stake_ratio`: `Rational32::new(160, 1_000_000)`, which reduces. -/
  minimumStakeRatio : Rat := ⟨1, 6250⟩
  chunkProducerAssignmentChangesLimit : Nat := 5
  shuffleShardAssignmentForChunkProducers : Bool := false
  targetValidatorMandatesPerShard : Nat := 68
  validatorMaxKickoutStakePerc : Nat := 100
  onlineMinThreshold : Rat := ⟨90, 100⟩
  onlineMaxThreshold : Rat := ⟨99, 100⟩
  minimumStakeDivisor : Nat := 10
  protocolUpgradeStakeThreshold : Rat := ⟨4, 5⟩
  blockProducerKickoutThreshold : Nat := 90
  chunkProducerKickoutThreshold : Nat := 90
  chunkValidatorOnlyKickoutThreshold : Nat := 80
  maxInflationRate : Rat := ⟨1, 40⟩
  /-- The static shard layout of the config. -/
  shardLayout : ShardLayout
  deriving Inhabited

/-- `RewardCalculator` and the genesis facts the epoch manager keeps. -/
structure RewardParams where
  protocolRewardRate : Rat
  protocolTreasuryAccount : AccountId
  genesisProtocolVersion : ProtocolVersion
  numSecondsPerYear : Nat := 24 * 60 * 60 * 365
  deriving Inhabited

/-- Everything the epoch manager is configured with. -/
structure Setup where
  config : EpochConfig
  reward : RewardParams
  deriving Inhabited

/-! ### Views of `EpochInfo` -/

/-- The fields of an `EpochInfo`, whatever its version. -/
structure EpochInfoView where
  epochHeight : Nat
  validators : Array ValidatorStake
  blockProducers : Array ValidatorId
  chunkProducers : Array (Array ValidatorId)
  stakeChange : Array (AccountId × Balance)
  validatorReward : Array (AccountId × Balance)
  validatorKickout : Array (AccountId × ValidatorKickoutReason)
  seatPrice : Balance
  protocolVersion : ProtocolVersion
  lastResharding : Option EpochHeight
  deriving Inhabited

/-- Read an `EpochInfo`. -/
def _root_.Near.Node.EpochInfo.view : EpochInfo → EpochInfoView
  | .v1 e =>
    { epochHeight := e.epochHeight.toNat, validators := e.validators.map .v1,
      blockProducers := e.blockProducersSettlement, chunkProducers := e.chunkProducersSettlement,
      stakeChange := e.stakeChange.entries, validatorReward := e.validatorReward.entries,
      validatorKickout := e.validatorKickout.entries, seatPrice := e.seatPrice,
      protocolVersion := e.protocolVersion, lastResharding := none }
  | .v2 e =>
    { epochHeight := e.epochHeight.toNat, validators := e.validators,
      blockProducers := e.blockProducersSettlement, chunkProducers := e.chunkProducersSettlement,
      stakeChange := e.stakeChange.entries, validatorReward := e.validatorReward.entries,
      validatorKickout := e.validatorKickout.entries, seatPrice := e.seatPrice,
      protocolVersion := e.protocolVersion, lastResharding := none }
  | .v3 e =>
    { epochHeight := e.base.epochHeight.toNat, validators := e.base.validators,
      blockProducers := e.base.blockProducersSettlement,
      chunkProducers := e.base.chunkProducersSettlement, stakeChange := e.base.stakeChange.entries,
      validatorReward := e.base.validatorReward.entries,
      validatorKickout := e.base.validatorKickout.entries, seatPrice := e.base.seatPrice,
      protocolVersion := e.base.protocolVersion, lastResharding := none }
  | .v4 e =>
    { epochHeight := e.epochHeight.toNat, validators := e.validators,
      blockProducers := e.blockProducersSettlement, chunkProducers := e.chunkProducersSettlement,
      stakeChange := e.stakeChange.entries, validatorReward := e.validatorReward.entries,
      validatorKickout := e.validatorKickout.entries, seatPrice := e.seatPrice,
      protocolVersion := e.protocolVersion, lastResharding := none }
  | .v5 e =>
    { epochHeight := e.epochHeight.toNat, validators := e.validators,
      blockProducers := e.blockProducersSettlement, chunkProducers := e.chunkProducersSettlement,
      stakeChange := e.stakeChange.entries, validatorReward := e.validatorReward.entries,
      validatorKickout := e.validatorKickout.entries, seatPrice := e.seatPrice,
      protocolVersion := e.protocolVersion, lastResharding := e.lastResharding }

/-- `*epoch_info.epoch_height_mut() += 1`. -/
def _root_.Near.Node.EpochInfo.bumpHeight : EpochInfo → EpochInfo
  | .v1 e => .v1 { e with epochHeight := e.epochHeight + 1 }
  | .v2 e => .v2 { e with epochHeight := e.epochHeight + 1 }
  | .v3 e => .v3 { e with base := { e.base with epochHeight := e.base.epochHeight + 1 } }
  | .v4 e => .v4 { e with epochHeight := e.epochHeight + 1 }
  | .v5 e => .v5 { e with epochHeight := e.epochHeight + 1 }

/-- An association list read by key. -/
def assocFind? [BEq K] (xs : Array (K × V)) (k : K) : Option V :=
  xs.findSome? fun (k', v) => if k' == k then some v else none

/-- Insert or replace by key, keeping the position of an existing key. -/
def assocInsert [BEq K] (xs : Array (K × V)) (k : K) (v : V) : Array (K × V) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.set! i (k, v)
  | none => xs.push (k, v)

/-- A `HashMap` or `BTreeMap` as the sorted map Borsh writes. -/
def toSortedMap [Ord K] (xs : Array (K × V)) : SortedMap K V :=
  ⟨xs.qsort fun a b => compare a.1 b.1 == .lt⟩

end Near.Node.Epoch
