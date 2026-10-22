import Model.PolicyCallbackBarrier
import Proofs.PolicyReadBarrier
import Proofs.CallbackExport

namespace SputnikDAO2

theorem unreadable_policy_blocks_successful_ordinary_callback
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option TransferCallbackState) (id resultCount : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyOrdinaryCallbackExport raw ctx state id resultCount
      .success policy encodeProposal encodeRoot = none := by
  simp [runRawPolicyOrdinaryCallbackExport, hread]

theorem failed_ordinary_callback_skips_policy_read
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option TransferCallbackState) (id resultCount : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes) :
    runRawPolicyOrdinaryCallbackExport raw ctx state id resultCount
      .failure policy encodeProposal encodeRoot =
      runOrdinaryCallbackExport raw ctx state id resultCount .failure
        policy encodeProposal encodeRoot := by
  rfl

theorem failed_ordinary_callback_with_unreadable_policy_keeps_lock
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : TransferCallbackState) (id resultCount : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (after : TransferCallbackResult)
    (h : runRawPolicyOrdinaryCallbackExport raw ctx (some state)
      id resultCount .failure policy encodeProposal encodeRoot =
      some (final, after)) :
    after = ⟨.failed, state.locked, none⟩ := by
  rw [failed_ordinary_callback_skips_policy_read] at h
  exact ordinary_failed_callback_keeps_lock raw final ctx state id
    resultCount policy encodeProposal encodeRoot after h

theorem unreadable_policy_blocks_successful_bounty_callback
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyResolutionState)
    (present : Bool) (proposalId bountyId resultCount : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runRawPolicyBountyCallbackExport raw ctx state present proposalId
      bountyId resultCount .success policy proposer encodeBounty
      encodeProposal encodeRoot = none := by
  simp [runRawPolicyBountyCallbackExport, hread]

theorem failed_bounty_callback_skips_policy_read
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyResolutionState)
    (present : Bool) (proposalId bountyId resultCount : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes) :
    runRawPolicyBountyCallbackExport raw ctx state present proposalId
      bountyId resultCount .failure policy proposer encodeBounty
      encodeProposal encodeRoot =
      runBountyCallbackExport raw ctx state present proposalId bountyId
        resultCount .failure policy proposer encodeBounty encodeProposal
        encodeRoot := by
  rfl

end SputnikDAO2
