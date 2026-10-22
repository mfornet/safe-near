import Model.Initialize

namespace SputnikDAO2

/-! Borsh image of the root `Contract`. LazyOption and LookupMap serialize only
their one-byte storage prefixes (as length-prefixed vectors). Their values
live at separate trie keys. This does not serialize the complete trie or prove
the Wasm wrapper. -/

def rootHandle (tag : UInt8) : BountyBytes := bountyLE 4 1 ++ [tag]

def rootStakingBytes : Option String → BountyBytes
  | none => [0]
  | some account => 1 :: bountyBorshString account

inductive RootAction where
  | addProposal | removeProposal | voteApprove | voteReject
  | voteRemove | finalize | moveToHub
  deriving Repr, DecidableEq

def rootActionTag : RootAction → UInt8
  | .addProposal => 0
  | .removeProposal => 1
  | .voteApprove => 2
  | .voteReject => 3
  | .voteRemove => 4
  | .finalize => 5
  | .moveToHub => 6

structure RootActionLog where
  accountId : String
  proposalId : Nat
  action : RootAction
  blockHeight : Nat
  deriving Repr, DecidableEq

def rootActionLogBytes (log : RootActionLog) : BountyBytes :=
  bountyBorshString log.accountId ++
  bountyLE 8 log.proposalId ++
  [rootActionTag log.action] ++
  bountyLE 8 log.blockHeight

structure RootStateScalars where
  lockedAmount : Nat
  stakingId : Option String
  totalDelegationAmount : Nat
  lastProposalId : Nat
  lastBountyId : Nat
  actionsLog : List RootActionLog
  deriving Repr, DecidableEq

def rootScalarsOfStateCore (core : StateCore) : RootStateScalars :=
  ⟨core.lockedAmount, core.stakingId, core.totalDelegationAmount,
    core.lastProposalId, core.lastBountyId, []⟩

def validRootLogWidths (log : RootActionLog) : Prop :=
  log.accountId.toUTF8.data.toList.length < 256 ^ 4 ∧
  log.proposalId < 256 ^ 8 ∧
  log.blockHeight < 256 ^ 8

def validRootScalarWidths (state : RootStateScalars) : Prop :=
  state.lockedAmount < 256 ^ 16 ∧
  state.totalDelegationAmount < 256 ^ 16 ∧
  state.lastProposalId < 256 ^ 8 ∧
  state.lastBountyId < 256 ^ 8 ∧
  (state.stakingId.map (fun account =>
    account.toUTF8.data.toList.length < 256 ^ 4)).getD true ∧
  state.actionsLog.length < 256 ^ 4 ∧
  state.actionsLog.length ≤ 20 ∧
  ∀ log ∈ state.actionsLog, validRootLogWidths log

def rootBeforeProposal (state : RootStateScalars) : BountyBytes :=
  rootHandle 0 ++ rootHandle 1 ++
  bountyLE 16 state.lockedAmount ++
  rootStakingBytes state.stakingId ++
  bountyLE 16 state.totalDelegationAmount ++
  rootHandle 2

def rootBeforeBounty (state : RootStateScalars) : BountyBytes :=
  rootBeforeProposal state ++ bountyLE 8 state.lastProposalId ++ rootHandle 3

def rootAfterBounty (state : RootStateScalars) : BountyBytes :=
  rootHandle 4 ++
  rootHandle 5 ++ rootHandle 6 ++ rootHandle 7 ++
  bountyLE 4 state.actionsLog.length ++
  state.actionsLog.flatMap rootActionLogBytes

def rootStateScalarBytes (state : RootStateScalars) : BountyBytes :=
  rootBeforeBounty state ++
  bountyLE 8 state.lastBountyId ++ rootAfterBounty state

-- ContractV1 has the identical ordered fields through `blobs` but no
-- `actions_log` field. This is the migration's root-wire compatibility
-- condition, independent of the separate policy and collection trie keys.
def rootStateV1Bytes (state : RootStateScalars) : BountyBytes :=
  rootBeforeBounty state ++
  bountyLE 8 state.lastBountyId ++
  rootHandle 4 ++ rootHandle 5 ++ rootHandle 6 ++ rootHandle 7

def rootStateBytes (lastProposalId lastBountyId : Nat) : BountyBytes :=
  rootStateScalarBytes ⟨0, none, 0, lastProposalId, lastBountyId, []⟩

def initializedRootBytes : BountyBytes := rootStateBytes 0 0

def populatedRootFixture : RootStateScalars :=
  ⟨17, some "staking.near", 19, 7, 9,
    [⟨"alice.near", 7, .voteApprove, 123⟩]⟩

-- Physical offsets of the two u64 counters in the 93-byte constructor image.
def rootProposalIdBytes (bytes : BountyBytes) : BountyBytes :=
  (bytes.drop 48).take 8

def rootBountyIdBytes (bytes : BountyBytes) : BountyBytes :=
  (bytes.drop 61).take 8

end SputnikDAO2
