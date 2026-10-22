import Model.BountyResolution
import Proofs.Finalize

namespace SputnikDAO2

theorem schedule_removes_claim_and_decrements_count
    (state next : BountyResolutionState) (receiver : String)
    (claim : BondClaim) (remaining : List BondClaim) (times : Nat)
    (hclaim : removeFirstClaim state.bonds.claims receiver =
      some (claim, remaining))
    (hcount : state.bonds.claimCount > 0)
    (htimes : state.times = some times)
    (hschedule : scheduleBountyPayout state receiver = some next) :
    next.bonds.claims = remaining ∧
      next.bonds.claimCount + 1 = state.bonds.claimCount ∧
      next.bonds.locked = state.bonds.locked ∧
      next.times = state.times := by
  simp [scheduleBountyPayout, htimes, hclaim,
    Nat.ne_of_gt hcount] at hschedule
  cases hschedule
  simp
  constructor
  · omega
  · exact htimes.symm

theorem failed_callback_preserves_removed_claim_and_times
    (state : BountyResolutionState) :
    (failedPayoutCallback state).bonds = state.bonds ∧
    (failedPayoutCallback state).times = state.times ∧
    (failedPayoutCallback state).status = .failed := by
  simp [failedPayoutCallback]

theorem retry_without_matching_claim_aborts
    (state : BountyResolutionState) (receiver : String)
    (habsent : removeFirstClaim state.bonds.claims receiver = none) :
    scheduleBountyPayout (failedPayoutCallback state) receiver = none := by
  simp [scheduleBountyPayout, failedPayoutCallback, habsent]

theorem success_with_one_time_stores_zero
    (state : BountyResolutionState) (policy : BondPolicyAmounts)
    (proposer : String) (htimes : state.times = some 1) :
    (successfulPayoutCallback state policy proposer).map
      (fun result => result.1.times) = some (some 0) := by
  simp [successfulPayoutCallback, htimes]

theorem success_with_zero_times_removes_bounty
    (state : BountyResolutionState) (policy : BondPolicyAmounts)
    (proposer : String) (htimes : state.times = some 0) :
    (successfulPayoutCallback state policy proposer).map
      (fun result => result.1.times) = some none := by
  simp [successfulPayoutCallback, htimes]

theorem failed_payout_can_leave_no_claim_for_retry :
    let claim : BondClaim := ⟨"alice.near", 0, 10, true, 5⟩
    let initial : BountyResolutionState :=
      ⟨⟨[claim], 1, 12⟩, some 1, .approved⟩
    let scheduled := scheduleBountyPayout initial "alice.near"
    scheduled.map (fun s => decide (
      let failed := failedPayoutCallback s
      failed.status = .failed ∧ failed.times = some 1 ∧
      failed.bonds.claimCount = 0 ∧
      scheduleBountyPayout failed "alice.near" = none)) =
      some true := by
  decide

theorem removed_bounty_done_forfeits_bonds
    (state removed : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String)
    (hschedule : scheduleBountyPayout state receiver = some removed) :
    rejectBountyDone state receiver policy proposer .removed = some {
      state := { removed with status := .removed }
      detachedRefunds := []
      proposalStored := false } := by
  simp [rejectBountyDone, hschedule, BountyRejection.status]

theorem rejected_bounty_done_detaches_both_bonds
    (state removed : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String)
    (hschedule : scheduleBountyPayout state receiver = some removed) :
    let refund := returnProposalBonds removed.bonds.locked policy proposer true
    rejectBountyDone state receiver policy proposer .rejected = some {
      state := { removed with
        bonds := { removed.bonds with locked := refund.lockedAfter }
        status := .rejected }
      detachedRefunds := refund.detachedTransfers ++ [refund.returnedTransfer]
      proposalStored := true } := by
  simp [rejectBountyDone, hschedule, BountyRejection.status]

theorem rejected_bounty_done_without_claim_aborts
    (state : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String)
    (habsent : removeFirstClaim state.bonds.claims receiver = none) :
    rejectBountyDone state receiver policy proposer .rejected = none := by
  simp [rejectBountyDone, scheduleBountyPayout, habsent]

theorem every_bounty_rejection_without_claim_aborts
    (state : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String)
    (kind : BountyRejection)
    (habsent : removeFirstClaim state.bonds.claims receiver = none) :
    rejectBountyDone state receiver policy proposer kind = none := by
  simp [rejectBountyDone, scheduleBountyPayout, habsent]

theorem expired_finalize_without_claim_aborts
    (ctx : FinalizeContext) (state : BountyResolutionState)
    (receiver : String) (policy : BondPolicyAmounts) (proposer : String)
    (habsent : removeFirstClaim state.bonds.claims receiver = none) :
    scheduleBountyExpiry ctx state receiver policy proposer = none := by
  cases hplan : selectFinalize ctx with
  | none => simp [scheduleBountyExpiry, hplan]
  | some plan =>
      cases plan.effect <;>
        simp [scheduleBountyExpiry, hplan, rejectBountyDone,
          scheduleBountyPayout, habsent]

theorem expired_finalize_with_claim_detaches_both_bonds
    (ctx : FinalizeContext) (state removed : BountyResolutionState)
    (receiver : String) (policy : BondPolicyAmounts) (proposer : String)
    (hplan : selectFinalize ctx =
      some ⟨.expired, .expireAndReturnBonds⟩)
    (hschedule : scheduleBountyPayout state receiver = some removed) :
    let refund := returnProposalBonds removed.bonds.locked policy proposer true
    scheduleBountyExpiry ctx state receiver policy proposer = some {
      state := { removed with
        bonds := { removed.bonds with locked := refund.lockedAfter }
        status := .expired }
      detachedRefunds := refund.detachedTransfers ++ [refund.returnedTransfer]
      proposalStored := true } := by
  simp [scheduleBountyExpiry, hplan, rejectBountyDone,
    hschedule, BountyRejection.status]

theorem expired_bounty_finalize_from_status_guards
    (ctx : FinalizeContext) (state removed : BountyResolutionState)
    (receiver : String) (policy : BondPolicyAmounts) (proposer : String)
    (hexists : ctx.proposalExists = true)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true)
    (hstatus : ctx.originalStatus = .inProgress ∨
      ctx.originalStatus = .failed)
    (hwidth : ctx.submission ≤ maxU64 ∧ ctx.period ≤ maxU64 ∧
      ctx.now ≤ maxU64 ∧ ctx.submission + ctx.period ≤ maxU64)
    (hexpired : ctx.submission + ctx.period < ctx.now)
    (hschedule : scheduleBountyPayout state receiver = some removed) :
    let refund := returnProposalBonds removed.bonds.locked policy proposer true
    scheduleBountyExpiry ctx state receiver policy proposer = some {
      state := { removed with
        bonds := { removed.bonds with locked := refund.lockedAfter }
        status := .expired }
      detachedRefunds := refund.detachedTransfers ++ [refund.returnedTransfer]
      proposalStored := true } := by
  exact expired_finalize_with_claim_detaches_both_bonds ctx state removed
    receiver policy proposer
    (expired_finalize_selects_refund ctx hexists hpermission hkind
      hstatus hwidth hexpired) hschedule

end SputnikDAO2
