import Model.BountyPayoutExecution
import Proofs.BountyResolution

namespace SputnikDAO2

theorem bounty_payout_missing_claim_aborts
    (state : BountyResolutionState) (asset : TransferAsset)
    (receiver : String) (amount bountyId : Nat)
    (current : String) (proposalId : Nat)
    (h : removeFirstClaim state.bonds.claims receiver = none) :
    planBountyDoneApproval state asset receiver amount bountyId current proposalId =
      none := by
  simp [planBountyDoneApproval, scheduleBountyPayout, h]

theorem bounty_payout_uses_no_message
    (state next : BountyResolutionState) (asset : TransferAsset)
    (receiver : String) (amount bountyId : Nat)
    (current : String) (proposalId : Nat)
    (h : scheduleBountyPayout state receiver = some next) :
    planBountyDoneApproval state asset receiver amount bountyId current proposalId =
      some ⟨next,
        planTransfer asset receiver amount
          ("Bounty " ++ toString bountyId ++ " payout") none current proposalId⟩ := by
  simp [planBountyDoneApproval, h]

theorem ft_bounty_payout_is_ft_transfer
    (state next : BountyResolutionState) (token receiver : String)
    (amount bountyId : Nat) (current : String) (proposalId : Nat)
    (h : scheduleBountyPayout state receiver = some next) :
    (planBountyDoneApproval state (.fungible token) receiver amount
      bountyId current proposalId).map (fun plan => plan.transfer.primary) =
      some (.ftCall token "ft_transfer" receiver amount
        ("Bounty " ++ toString bountyId ++ " payout") none 1 ftTransferGas) := by
  simp [bounty_payout_uses_no_message state next (.fungible token)
    receiver amount bountyId current proposalId h, planTransfer]

theorem bounty_payout_schedules_callback_without_immediate_refund
    (state next : BountyResolutionState) (asset : TransferAsset)
    (receiver : String) (amount bountyId : Nat)
    (current : String) (proposalId : Nat)
    (h : scheduleBountyPayout state receiver = some next) :
    (planBountyDoneApproval state asset receiver amount bountyId current proposalId).map
      (fun plan => (plan.transfer.callback, plan.transfer.immediateBondRefund)) =
      some (⟨current, "on_proposal_callback", proposalId, 0, ftTransferGas⟩, false) := by
  cases asset <;>
    simp [bounty_payout_uses_no_message state next _ receiver amount
      bountyId current proposalId h, planTransfer]

theorem bounty_callback_requires_guards
    (state : BountyResolutionState) (self present : Bool)
    (count : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts) (proposer : String)
    (h : present = false ∨ self = false ∨ count ≠ 1) :
    finishBountyPayout state present self count result policy proposer = none := by
  rcases h with hp | hs | hc
  · simp [finishBountyPayout, hp]
  · simp [finishBountyPayout, hs]
  · simp [finishBountyPayout, hc]

theorem failed_bounty_payout_keeps_removed_claim_and_lock
    (state : BountyResolutionState) (policy : BondPolicyAmounts)
    (proposer : String) :
    finishBountyPayout state true true 1 .failure policy proposer =
      some ⟨failedPayoutCallback state, none⟩ := by
  simp [finishBountyPayout]

theorem successful_bounty_payout_returns_both_current_bonds
    (state next : BountyResolutionState) (policy : BondPolicyAmounts)
    (proposer : String) (refund : BondReturn)
    (h : successfulPayoutCallback state policy proposer = some (next, refund)) :
    finishBountyPayout state true true 1 .success policy proposer =
      some ⟨next, some refund⟩ := by
  simp [finishBountyPayout, h]

theorem repeated_success_callback_removes_bounty_and_refunds_twice
    (state : BountyResolutionState) (policy : BondPolicyAmounts)
    (proposer : String) (h : state.times = some 1) :
    ((finishBountyPayout state true true 1 .success policy proposer).bind
      (fun first => finishBountyPayout first.state true true 1 .success
        policy proposer)).map
      (fun second => (second.state.times, second.refund.isSome)) =
      some (none, true) := by
  simp [finishBountyPayout, successfulPayoutCallback, h]

theorem current_bond_refunds_can_exceed_previous_lock :
    let state : BountyResolutionState :=
      ⟨⟨[], 0, 2⟩, some 1, .approved⟩
    let policy : BondPolicyAmounts := ⟨3, 2⟩
    (finishBountyPayout state true true 1 .success policy "bob.near").map
      (fun outcome =>
        (outcome.state.bonds.locked,
          outcome.refund.map totalScheduledRefund)) =
      some (0, some 5) := by
  decide

end SputnikDAO2
