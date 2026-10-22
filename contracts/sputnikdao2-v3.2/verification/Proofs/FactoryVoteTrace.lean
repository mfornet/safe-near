import Model.FactoryVoteTrace
import Proofs.FactoryGovernanceExport

namespace SputnikDAO2

theorem factory_approval_vote_effects
    (state : FactoryVoteState) (account : String) (id : Nat)
    (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (policy : BondPolicyAmounts) (ballot : MultiVoteState)
    (hstep : multiVoteStep state.ballot account choice weight
      submission period now supply = some ballot)
    (happroved : ballot.status = .approved) :
    runFactoryApprovalVote state account id choice height weight
      submission period now supply policy =
      some ⟨ballot,
        (returnProposalBonds state.locked policy state.proposer false).lockedAfter,
        appendLog20 state.globalLog ⟨account, id, choice, height⟩,
        (returnProposalBonds state.locked policy state.proposer false).returnedTransfer⟩ := by
  simp [runFactoryApprovalVote, hstep, happroved]

theorem factory_approval_vote_has_approved_status
    (state : FactoryVoteState) (account : String) (id : Nat)
    (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (policy : BondPolicyAmounts) (result : FactoryVoteResult)
    (h : runFactoryApprovalVote state account id choice height weight
      submission period now supply policy = some result) :
    result.ballot.status = .approved := by
  unfold runFactoryApprovalVote at h
  cases hstep : multiVoteStep state.ballot account choice weight
      submission period now supply with
  | none => simp [hstep] at h
  | some ballot =>
      by_cases hstatus : ballot.status = .approved
      · simp [hstep, hstatus] at h
        cases h
        exact hstatus
      · simp [hstep, hstatus] at h

theorem factory_approval_vote_export_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : FactoryVoteState) (id : Nat) (info : FactoryInfo)
    (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : FactoryVoteResult → BountyBytes)
    (result : FactoryVoteResult) (oldProposal : BountyBytes)
    (hid : id ≤ maxU64) (hheight : height ≤ maxU64)
    (hstep : runFactoryApprovalVote state wrapper.predecessor id choice
      height weight submission period now supply policy = some result)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runFactoryApprovalVoteExport raw wrapper (some state) id info choice
      height weight submission period now supply policy true true true
      encodeProposal encodeRoot =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoFactoryKey (encodeFactoryInfo info))
          (daoProposalEntryKey id) (encodeProposal result))
        daoRootKey (encodeRoot result), result) := by
  have hwrite := approved_factory_update_three_key_image raw wrapper id info
    (encodeProposal result) (encodeRoot result) oldProposal
    hid hproposal hargs hdeposit
  simp [runFactoryApprovalVoteExport, Nat.not_lt.mpr hid,
    Nat.not_lt.mpr hheight, hstep, hwrite]

end SputnikDAO2
