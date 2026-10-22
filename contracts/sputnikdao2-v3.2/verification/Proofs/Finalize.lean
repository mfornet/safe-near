import Model.Finalize
import Proofs.Status

namespace SputnikDAO2

theorem finalize_requires_existing_proposal (ctx : FinalizeContext)
    (h : ctx.proposalExists = false) :
    selectFinalize ctx = none := by
  simp [selectFinalize, h]

theorem finalize_requires_permission (ctx : FinalizeContext)
    (h : ctx.permissionAllowed = false) :
    selectFinalize ctx = none := by
  cases hp : ctx.proposalExists <;> simp [selectFinalize, hp, h]

theorem finalize_requires_exact_kind (ctx : FinalizeContext)
    (h : ctx.exactKindMatches = false) :
    selectFinalize ctx = none := by
  cases hp : ctx.proposalExists <;>
    cases ha : ctx.permissionAllowed <;>
      simp [selectFinalize, hp, ha, h]

theorem terminal_status_cannot_finalize (ctx : FinalizeContext)
    (hprogress : ctx.originalStatus ≠ .inProgress)
    (hfailed : ctx.originalStatus ≠ .failed) :
    selectFinalize ctx = none := by
  cases hp : ctx.proposalExists <;>
    cases ha : ctx.permissionAllowed <;>
      cases hk : ctx.exactKindMatches <;>
        simp [selectFinalize, proposalStatusChecked, hp, ha, hk,
          hprogress, hfailed]

theorem expired_finalize_selects_refund (ctx : FinalizeContext)
    (hexists : ctx.proposalExists = true)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true)
    (hstatus : ctx.originalStatus = .inProgress ∨
      ctx.originalStatus = .failed)
    (hwidth : ctx.submission ≤ maxU64 ∧ ctx.period ≤ maxU64 ∧
      ctx.now ≤ maxU64 ∧ ctx.submission + ctx.period ≤ maxU64)
    (hexpired : ctx.submission + ctx.period < ctx.now) :
    selectFinalize ctx = some ⟨.expired, .expireAndReturnBonds⟩ := by
  rcases hwidth with ⟨hsub, hperiod, hnow, hsum⟩
  rcases hstatus with hs | hs
  · simp [selectFinalize, proposalStatusChecked, hs, hexists, hpermission,
      hkind, Nat.not_lt.mpr hsub, Nat.not_lt.mpr hperiod,
      Nat.not_lt.mpr hnow, Nat.not_lt.mpr hsum, expired, hexpired]
  · simp [selectFinalize, proposalStatusChecked, hs, hexists, hpermission,
      hkind, Nat.not_lt.mpr hsub, Nat.not_lt.mpr hperiod,
      Nat.not_lt.mpr hnow, Nat.not_lt.mpr hsum, expired, hexpired]

theorem ordinary_expired_finalization_schedules_current_bond
    (ctx : FinalizeContext) (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (hexists : ctx.proposalExists = true)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true)
    (hstatus : ctx.originalStatus = .inProgress ∨
      ctx.originalStatus = .failed)
    (hwidth : ctx.submission ≤ maxU64 ∧ ctx.period ≤ maxU64 ∧
      ctx.now ≤ maxU64 ∧ ctx.submission + ctx.period ≤ maxU64)
    (hexpired : ctx.submission + ctx.period < ctx.now) :
    scheduleOrdinaryExpiry ctx locked policy proposer =
      some ⟨.expired, locked - policy.proposalBond,
        ⟨proposer, policy.proposalBond⟩, true⟩ := by
  have hs := expired_finalize_selects_refund ctx
    hexists hpermission hkind hstatus hwidth hexpired
  simp [scheduleOrdinaryExpiry, hs, returnProposalBonds]

theorem approved_finalize_selects_execution (ctx : FinalizeContext)
    (hexists : ctx.proposalExists = true)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true)
    (hstatus : proposalStatusChecked ctx.originalStatus
      ctx.submission ctx.period ctx.now ctx.totalSupply
      ctx.policyRolesInVectorOrder = some .approved) :
    selectFinalize ctx = some ⟨.approved, .executeProposal⟩ := by
  simp [selectFinalize, hexists, hpermission, hkind, hstatus]

theorem failed_without_decision_cannot_finalize :
    selectFinalize
      ⟨true, true, true, .failed, 0, 10, 10, 0, []⟩ = none := by
  decide

theorem in_progress_zero_threshold_can_finalize_early :
    selectFinalize
      ⟨true, true, true, .inProgress, 0, 10, 0, 0,
        [⟨.group 0, .role, 0, .ratio 1 2, 0, 0, 0⟩]⟩ =
      some ⟨.approved, .executeProposal⟩ := by
  decide

theorem rejected_vote_result_cannot_finalize :
    selectFinalize
      ⟨true, true, true, .inProgress, 0, 10, 0, 1,
        [⟨.group 1, .role, 1, .weight 1, 0, 1, 0⟩]⟩ = none := by
  decide

theorem finalize_unsafe_ratio_aborts :
    selectFinalize
      ⟨true, true, true, .inProgress, 0, 1, 0, maxU128,
        [⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩]⟩ = none := by
  decide

theorem expired_finalize_skips_unsafe_ratio :
    selectFinalize
      ⟨true, true, true, .inProgress, 0, 0, 1, maxU128,
        [⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩]⟩ =
      some ⟨.expired, .expireAndReturnBonds⟩ := by
  decide

end SputnikDAO2
