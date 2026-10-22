import Model.ConfigVoteTrace
import Proofs.ConfigGovernanceExport
import Proofs.FactoryVoteTrace

namespace SputnikDAO2

theorem config_approval_vote_export_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : FactoryVoteState) (id : Nat) (config : WireConfig)
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
    runConfigApprovalVoteExport raw wrapper (some state) id config choice
      height weight submission period now supply policy true true true
      encodeProposal encodeRoot =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoConfigKey (encodeWireConfig config))
          (daoProposalEntryKey id) (encodeProposal result))
        daoRootKey (encodeRoot result), result) := by
  have hwrite := approved_config_update_three_key_image raw wrapper id config
    (encodeProposal result) (encodeRoot result) oldProposal
    hid hproposal hargs hdeposit
  simp [runConfigApprovalVoteExport, Nat.not_lt.mpr hid,
    Nat.not_lt.mpr hheight, hstep, hwrite]

theorem config_approval_vote_result_is_approved
    (state : FactoryVoteState) (account : String) (id : Nat)
    (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (policy : BondPolicyAmounts) (result : FactoryVoteResult)
    (h : runFactoryApprovalVote state account id choice height weight
      submission period now supply policy = some result) :
    result.ballot.status = .approved :=
  factory_approval_vote_has_approved_status state account id choice
    height weight submission period now supply policy result h

end SputnikDAO2
