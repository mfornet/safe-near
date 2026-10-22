import Model.PolicyTimeTrace

namespace SputnikDAO2

private def timeTraceGovernance : SyncGovernanceState :=
  ⟨⟨1, 10, 1, 1⟩, none, 1⟩

private def timeTracePatch : GovernanceParameterPatch :=
  ⟨none, some maxU64, none, none⟩

private def timeTraceCreation : ProposalCreateState :=
  ⟨0, 0, false, [], []⟩

private def timeTraceContext : ProposalCreateContext :=
  ⟨"alice.near", 1, 1, 1, 1, true⟩

private def timeTraceBallot : MultiVoteState :=
  ⟨.inProgress, [], [⟨.group 1, .role, 0, .weight 1, 0, 0, 0⟩]⟩

theorem public_period_patch_trace_reaches_vote_and_finalize_abort :
    (runPeriodPatchVoteTrace timeTraceGovernance timeTracePatch
      timeTraceCreation timeTraceContext timeTraceBallot
      "alice.near" .approve 0 1 0).map
        (fun trace =>
          (trace.governance.state.policy.proposalPeriod,
            trace.storedProposal.submissionTime,
            trace.voteResult, trace.finalizeResult)) =
      some (maxU64, 1, none, none) := by
  decide

theorem period_patch_retains_bond_while_maximizing_period :
    applyParameterPatch timeTraceGovernance.policy timeTracePatch =
      ⟨1, maxU64, 1, 1⟩ := by
  rfl

theorem maximal_period_overflows_after_positive_submission
    (submission : Nat) (hpositive : 0 < submission) :
    maxU64 < submission + maxU64 := by
  omega

theorem maximal_period_blocks_vote_after_positive_submission
    (ballot : MultiVoteState) (account : String)
    (choice : VoteChoice) (userWeight submission now supply : Nat)
    (hpositive : 0 < submission) :
    multiVoteStep ballot account choice userWeight
      submission maxU64 now supply = none := by
  have hoverflow :=
    maximal_period_overflows_after_positive_submission submission hpositive
  simp [multiVoteStep, hoverflow]

theorem maximal_period_blocks_finalize_after_positive_submission
    (ctx : FinalizeContext)
    (hperiod : ctx.period = maxU64)
    (hpositive : 0 < ctx.submission) :
    selectFinalize ctx = none := by
  have hoverflow : maxU64 < ctx.submission + ctx.period := by
    rw [hperiod]
    exact maximal_period_overflows_after_positive_submission
      ctx.submission hpositive
  cases hp : ctx.proposalExists <;>
    cases ha : ctx.permissionAllowed <;>
      cases hk : ctx.exactKindMatches <;>
        simp [selectFinalize, proposalStatusChecked, hp, ha, hk,
          hoverflow]

end SputnikDAO2
