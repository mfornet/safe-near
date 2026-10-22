import Model.BountyResolution
import Model.TransferExecution

namespace SputnikDAO2

/-! Approved BountyDone execution after the caller has selected the branch.
`scheduleBountyPayout` removes the matching claim first. The payout uses
`internal_payout` with no message, so a fungible token uses `ft_transfer`,
never `ft_transfer_call`. Token-ID parsing is a precondition, and the plan
describes receipts rather than their eventual outcome. -/

structure BountyPayoutPlan where
  afterClaimRemoval : BountyResolutionState
  transfer : TransferExecutionPlan
  deriving Repr

def planBountyDoneApproval (state : BountyResolutionState)
    (asset : TransferAsset) (receiver : String) (amount : Nat)
    (bountyId : Nat) (current : String) (proposalId : Nat) :
    Option BountyPayoutPlan := do
  let next ← scheduleBountyPayout state receiver
  let memo := "Bounty " ++ toString bountyId ++ " payout"
  some ⟨next, planTransfer asset receiver amount memo none current proposalId⟩

structure BountyPayoutCallbackOutcome where
  state : BountyResolutionState
  refund : Option BondReturn
  deriving Repr, DecidableEq

def finishBountyPayout (state : BountyResolutionState)
    (proposalPresent callerSelf : Bool) (resultCount : Nat)
    (result : CallbackResult) (policy : BondPolicyAmounts)
    (proposer : String) : Option BountyPayoutCallbackOutcome := do
  if !proposalPresent || !callerSelf || resultCount != 1 then none else
  match result with
  | .failure => some ⟨failedPayoutCallback state, none⟩
  | .success =>
      let (next, refund) ← successfulPayoutCallback state policy proposer
      some ⟨next, some refund⟩

end SputnikDAO2
