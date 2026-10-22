import Model.PolicyVoteTrace
import Proofs.PolicyGovernanceExport
import Proofs.FactoryVoteTrace

namespace SputnikDAO2

theorem policy_vote_unreadable_old_policy_aborts
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option FactoryVoteState) (id : Nat)
    (newPolicy : WireVersionedPolicy) (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (oldBondPolicy : BondPolicyAmounts)
    (permissionAllowed exactKindMatches : Bool)
    (encodeProposal encodeRoot : FactoryVoteResult → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runPolicyApprovalVoteExport raw wrapper state id newPolicy choice
      height weight submission period now supply oldBondPolicy
      permissionAllowed exactKindMatches encodeProposal encodeRoot = none := by
  cases state with
  | none => simp [runPolicyApprovalVoteExport]
  | some before =>
      simp [runPolicyApprovalVoteExport,
        runApprovedChangePolicyExport, hread]

theorem policy_approval_vote_export_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : FactoryVoteState) (id : Nat)
    (newPolicy : WireVersionedPolicy) (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (oldBondPolicy : BondPolicyAmounts)
    (encodeProposal encodeRoot : FactoryVoteResult → BountyBytes)
    (result : FactoryVoteResult) (oldProposal : BountyBytes)
    (hid : id ≤ maxU64) (hheight : height ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hstep : runFactoryApprovalVote state wrapper.predecessor id choice
      height weight submission period now supply oldBondPolicy =
      some result)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runPolicyApprovalVoteExport raw wrapper (some state) id newPolicy choice
      height weight submission period now supply oldBondPolicy true true
      encodeProposal encodeRoot =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoPolicyKey
            (encodeWireVersionedPolicy newPolicy))
          (daoProposalEntryKey id) (encodeProposal result))
        daoRootKey (encodeRoot result), result) := by
  have hwrite := approved_policy_update_three_key_image raw wrapper id
    newPolicy (encodeProposal result) (encodeRoot result) oldProposal
    hid hread hproposal hargs hdeposit
  simp [runPolicyApprovalVoteExport, Nat.not_lt.mpr hid,
    Nat.not_lt.mpr hheight, hstep, hwrite]

theorem approved_legacy_policy_vote_breaks_next_view
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : FactoryVoteState) (id : Nat) (council : List String)
    (choice : VoteChoice)
    (height weight submission period now supply : Nat)
    (oldBondPolicy : BondPolicyAmounts)
    (encodeProposal encodeRoot : FactoryVoteResult → BountyBytes)
    (result : FactoryVoteResult) (oldProposal : BountyBytes)
    (deposit : Nat)
    (hid : id ≤ maxU64) (hheight : height ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hstep : runFactoryApprovalVote state wrapper.predecessor id choice
      height weight submission period now supply oldBondPolicy =
      some result)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hfits : wireVersionedPolicyFits (.default council)) :
    let final := bountyRawWrite
      (bountyRawWrite
        (bountyRawWrite raw daoPolicyKey
          (encodeWireVersionedPolicy (.default council)))
        (daoProposalEntryKey id) (encodeProposal result))
      daoRootKey (encodeRoot result)
    runPolicyApprovalVoteExport raw wrapper (some state) id
      (.default council) choice height weight submission period now supply
      oldBondPolicy true true encodeProposal encodeRoot =
      some (final, result) ∧
    runParsedPolicyView final (some ()) deposit = none := by
  dsimp
  constructor
  · exact policy_approval_vote_export_three_key_image raw wrapper state id
      (.default council) choice height weight submission period now supply
      oldBondPolicy encodeProposal encodeRoot result oldProposal
      hid hheight hread hstep hproposal hargs hdeposit
  · have hwrite := approved_policy_update_three_key_image raw wrapper id
      (.default council) (encodeProposal result) (encodeRoot result)
      oldProposal hid hread hproposal hargs hdeposit
    exact approved_legacy_policy_makes_next_view_abort raw
      (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoPolicyKey
            (encodeWireVersionedPolicy (.default council)))
          (daoProposalEntryKey id) (encodeProposal result))
        daoRootKey (encodeRoot result))
      wrapper id council (encodeProposal result) (encodeRoot result)
      oldProposal deposit hid hread hproposal hargs hdeposit hwrite hfits

end SputnikDAO2
