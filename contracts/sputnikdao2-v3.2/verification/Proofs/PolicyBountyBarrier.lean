import Model.PolicyBountyBarrier
import Proofs.PolicyReadBarrier

namespace SputnikDAO2

theorem unreadable_policy_blocks_bounty_claim
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState)
    (bounty : Option (Nat × Nat)) (policyBond : Option Nat)
    (id now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyBountyClaimExport raw ctx state bounty policyBond id now
      deadline encodeRoot = none := by
  simp [runRawPolicyBountyClaimExport, hread]

theorem unreadable_policy_blocks_bounty_giveup
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState)
    (policy : Option (Nat × Nat)) (id now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyBountyGiveupExport raw ctx state policy id now
      encodeRoot = none := by
  simp [runRawPolicyBountyGiveupExport, hread]

theorem unreadable_policy_blocks_timely_bounty_done
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (id : Nat) (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (proposalId : Nat)
    (hread : policyReadableFromRaw raw = false)
    (hbody : runBountyDoneExport raw wrapper state create target id
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, .proposal proposalId)) :
    runRawPolicyBountyDoneExport raw wrapper state create target id
      description oldProposalDecoded encodeProposal encodeRoot = none := by
  simp [runRawPolicyBountyDoneExport, hbody, hread]

theorem expired_bounty_done_does_not_read_policy
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (id : Nat) (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (hbody : runBountyDoneExport raw wrapper state create target id
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, .expired)) :
    runRawPolicyBountyDoneExport raw wrapper state create target id
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, .expired) := by
  simp [runRawPolicyBountyDoneExport, hbody]

end SputnikDAO2
