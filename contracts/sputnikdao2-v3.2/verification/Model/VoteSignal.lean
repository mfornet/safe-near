import Model.MultiVote
import Model.ProposalBonds
import Model.ProposalCreate

namespace SputnikDAO2

/-! `ProposalKind::Vote` has no application action: its Approved execution
returns `Value(())`, then `internal_return_bonds` schedules the current
proposal-bond refund. This model joins multi-role voting to the exported
`act_proposal` branch's proposal, lock, log and detached-transfer effects.
No BountyDone, external-action or callback branch is claimed here. -/

structure SignalVoteLog where
  account : String
  proposalId : Nat
  choice : VoteChoice
  blockHeight : Nat
  deriving Repr, DecidableEq

structure SignalVoteState where
  proposalPresent : Bool
  ballot : MultiVoteState
  proposer : String
  locked : Nat
  globalLog : List SignalVoteLog
  deriving Repr, DecidableEq

structure SignalVoteContext where
  permissionAllowed : Bool
  exactKindMatches : Bool
  account : String
  proposalId : Nat
  choice : VoteChoice
  blockHeight : Nat
  userWeight : Nat
  submission : Nat
  period : Nat
  now : Nat
  totalSupply : Nat
  currentBondPolicy : BondPolicyAmounts
  deriving Repr, DecidableEq

inductive SignalVoteEffect where
  | storeOnly | refundBond | deleteProposal
  deriving Repr, DecidableEq

structure SignalVoteResult where
  proposalPresent : Bool
  ballot : MultiVoteState
  locked : Nat
  globalLog : List SignalVoteLog
  detachedRefunds : List BondTransfer
  effect : SignalVoteEffect
  deriving Repr, DecidableEq

-- A failed branch returns `none` and relies on host transaction rollback for
-- the log/count writes that the source attempted before the failing check.
def runSignalVote (state : SignalVoteState) (ctx : SignalVoteContext) :
    Option SignalVoteResult := do
  if !state.proposalPresent || !ctx.permissionAllowed ||
      !ctx.exactKindMatches then none else
  let next ← multiVoteStep state.ballot ctx.account ctx.choice ctx.userWeight
    ctx.submission ctx.period ctx.now ctx.totalSupply
  let log := appendLog20 state.globalLog
    ⟨ctx.account, ctx.proposalId, ctx.choice, ctx.blockHeight⟩
  match next.status with
  | .approved | .rejected =>
      let refund := returnProposalBonds state.locked
        ctx.currentBondPolicy state.proposer false
      some ⟨true, next, refund.lockedAfter, log,
        [refund.returnedTransfer], .refundBond⟩
  | .removed =>
      some ⟨false, next, state.locked, log, [], .deleteProposal⟩
  | .inProgress | .expired =>
      some ⟨true, next, state.locked, log, [], .storeOnly⟩
  | .moved | .failed => none

end SputnikDAO2
