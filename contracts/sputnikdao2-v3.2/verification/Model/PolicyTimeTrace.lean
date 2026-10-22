import Model.SyncGovernance
import Model.ProposalCreate
import Model.MultiVote
import Model.Finalize

namespace SputnikDAO2

/-! Conditional cross-method trace: a successful approved parameter patch,
then public proposal creation, then vote and Finalize status evaluation.
Approval of the patch, permission lookup and host rollback are inputs to the
component models. `.other` is the Vote-kind creation branch here. -/

structure PeriodPatchVoteTrace where
  governance : SyncGovernanceOutcome
  created : ProposalCreateState
  proposalId : Nat
  storedProposal : CreatedProposal
  voteResult : Option MultiVoteState
  finalizeResult : Option FinalizePlan
  deriving Repr, DecidableEq

def runPeriodPatchVoteTrace
    (governance : SyncGovernanceState)
    (patch : GovernanceParameterPatch)
    (creation : ProposalCreateState) (createCtx : ProposalCreateContext)
    (ballot : MultiVoteState) (account : String) (choice : VoteChoice)
    (userWeight now totalSupply : Nat) : Option PeriodPatchVoteTrace := do
  let updated ← executeSyncGovernance governance (.updateParameters patch)
    createCtx.predecessor
  let (created, id) ← addProposal creation createCtx .other "vote"
  let stored ← proposalAt created.proposals id
  let period := updated.state.policy.proposalPeriod
  let vote := multiVoteStep ballot account choice userWeight
    stored.submissionTime period now totalSupply
  let finalize := selectFinalize
    ⟨true, true, true, .inProgress, stored.submissionTime,
      period, now, totalSupply, ballot.selectedRoles⟩
  some ⟨updated, created, id, stored, vote, finalize⟩

end SputnikDAO2
