import Model.FactoryGovernanceExport
import Model.VoteSignal

namespace SputnikDAO2

structure FactoryVoteState where
  ballot : MultiVoteState
  proposer : String
  locked : Nat
  globalLog : List SignalVoteLog
  deriving Repr, DecidableEq

structure FactoryVoteResult where
  ballot : MultiVoteState
  locked : Nat
  globalLog : List SignalVoteLog
  detachedRefund : BondTransfer
  deriving Repr, DecidableEq

/-! Approved voting path for a stored `FactoryInfoUpdate` proposal. Role
selection, per-role policy rules, account weights, policy readability and
stored-kind equality are explicit inputs. The state/result records bind the
approved status, log and current-policy bond refund; serializers still need
to refine the complete Proposal and Contract values. -/
def runFactoryApprovalVote (state : FactoryVoteState)
    (account : String) (id : Nat) (choice : VoteChoice)
    (blockHeight userWeight submission period now totalSupply : Nat)
    (policy : BondPolicyAmounts) : Option FactoryVoteResult := do
  let ballot ← multiVoteStep state.ballot account choice userWeight
    submission period now totalSupply
  if ballot.status != .approved then none else
  let bonds := returnProposalBonds state.locked policy state.proposer false
  some ⟨ballot, bonds.lockedAfter,
    appendLog20 state.globalLog ⟨account, id, choice, blockHeight⟩,
    bonds.returnedTransfer⟩

def runFactoryApprovalVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option FactoryVoteState)
    (id : Nat) (info : FactoryInfo) (choice : VoteChoice)
    (blockHeight userWeight submission period now totalSupply : Nat)
    (policy : BondPolicyAmounts)
    (policyReadable permissionAllowed exactKindMatches : Bool)
    (encodeProposal : FactoryVoteResult → BountyBytes)
    (encodeRoot : FactoryVoteResult → BountyBytes) :
    Option (BountyRawTrie × FactoryVoteResult) := do
  let before ← state
  if id > maxU64 || blockHeight > maxU64 ||
      !policyReadable || !permissionAllowed || !exactKindMatches then none
  else pure ()
  let result ← runFactoryApprovalVote before wrapper.predecessor id choice
    blockHeight userWeight submission period now totalSupply policy
  let final ← runApprovedFactoryInfoUpdateExport raw wrapper
    state.isSome true id info (encodeProposal result) (encodeRoot result)
  some (final, result)

end SputnikDAO2
