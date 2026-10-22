import Model.PolicyReadBarrier
import Model.CallbackExport
import Model.BountyCallbackExport

namespace SputnikDAO2

/-! The callback branches split before `internal_callback_proposal_success`
reads current policy. A failed promise result marks the proposal Failed without
that read. This applies to ordinary and BountyDone callbacks; the generated
wrapper's private caller, result count and root write remain in each model. -/
def runRawPolicyOrdinaryCallbackExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal : TransferCallbackResult → BountyBytes)
    (encodeRoot : TransferCallbackResult → BountyBytes) :
    Option (BountyRawTrie × TransferCallbackResult) :=
  if result == .success && !policyReadableFromRaw raw then none
  else runOrdinaryCallbackExport raw ctx state proposalId resultCount
    result policy encodeProposal encodeRoot

def runRawPolicyBountyCallbackExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyResolutionState)
    (proposalPresent : Bool) (proposalId bountyId resultCount : Nat)
    (result : CallbackResult) (policy : BondPolicyAmounts)
    (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes) :
    Option (BountyRawTrie × BountyPayoutCallbackOutcome) :=
  if result == .success && !policyReadableFromRaw raw then none
  else runBountyCallbackExport raw ctx state proposalPresent proposalId
    bountyId resultCount result policy proposer encodeBounty encodeProposal
    encodeRoot

end SputnikDAO2
