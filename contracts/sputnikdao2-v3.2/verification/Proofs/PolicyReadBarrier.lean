import Model.PolicyReadBarrier
import Proofs.PolicyGovernanceExport

namespace SputnikDAO2

theorem unreadable_policy_blocks_add_proposal
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option ProposalCreateState) (create : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String)
    (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyAddProposalExport raw wrapper state create kind description
      oldProposalDecoded encodeProposal encodeRoot = none := by
  simp [runRawPolicyAddProposalExport, hread]

theorem unreadable_policy_blocks_nonvote_action
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyActNonVoteExport raw wrapper state ctx id action
      encodeRoot = none := by
  simp [runRawPolicyActNonVoteExport, runActNonVoteExport, hread]

theorem unreadable_policy_blocks_signal_vote
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (kindMatches storedDecoded : Bool)
    (encodeProposal : SignalVoteResult → BountyBytes)
    (encodeRoot : SignalVoteResult → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicySignalVoteExport raw wrapper state ctx id kindMatches
      storedDecoded encodeProposal encodeRoot = none := by
  simp [runRawPolicySignalVoteExport, runSignalVoteExport, hread]

theorem unreadable_policy_blocks_vote_finalize
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (kindMatches storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal : VoteFinalizeResult → BountyBytes)
    (encodeRoot : VoteFinalizeResult → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyVoteFinalizeExport raw wrapper state ctx id height
      kindMatches storedDecoded policy encodeProposal encodeRoot = none := by
  simp [runRawPolicyVoteFinalizeExport, runVoteFinalizeExport, hread]

theorem legacy_policy_blocks_raw_proposal_creation
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option ProposalCreateState) (create : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String)
    (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes)
    (council : List String)
    (hraw : raw daoPolicyKey =
      some (encodeWireVersionedPolicy (.default council)))
    (hfits : wireVersionedPolicyFits (.default council)) :
    runRawPolicyAddProposalExport raw wrapper state create kind description
      oldProposalDecoded encodeProposal encodeRoot = none := by
  exact unreadable_policy_blocks_add_proposal raw wrapper state create kind
    description oldProposalDecoded encodeProposal encodeRoot
    (encoded_legacy_policy_is_unreadable raw council hraw hfits)

theorem approved_legacy_policy_write_closes_proposal_barrier
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (council : List String)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangePolicyExport raw wrapper true true id
      (.default council) proposalBytes rootBytes = some final)
    (hfits : wireVersionedPolicyFits (.default council)) :
    policyReadableFromRaw final = false := by
  have hraw := approved_policy_update_stores_policy_bytes raw final
    wrapper id (.default council) proposalBytes rootBytes oldProposal
    hid hread hproposal hargs hdeposit hrun
  exact encoded_legacy_policy_is_unreadable final council hraw hfits

end SputnikDAO2
