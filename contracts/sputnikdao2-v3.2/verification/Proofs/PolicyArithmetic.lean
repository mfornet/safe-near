import Model.PolicyArithmetic
import Proofs.SyncGovernance
import Proofs.Delegation

namespace SputnikDAO2

theorem checked_ratio_matches_mathematical_weight
    (numerator denominator total : Nat)
    (h : ratioArithmeticSafe numerator denominator total) :
    checkedRatioWeight numerator denominator total =
      some (toWeight (.ratio numerator denominator) total) := by
  rcases h with ⟨hn, hd, hdu, ht, hp, hq⟩
  simp [checkedRatioWeight, toWeight, Nat.not_lt.mpr hn,
    Nat.ne_of_gt hd, Nat.not_lt.mpr hdu, Nat.not_lt.mpr ht,
    Nat.not_lt.mpr hp, Nat.ne_of_lt hq]

theorem checked_ratio_success_implies_safe
    (numerator denominator total result : Nat)
    (h : checkedRatioWeight numerator denominator total = some result) :
    ratioArithmeticSafe numerator denominator total := by
  simp only [checkedRatioWeight] at h
  split at h
  · simp at h
  · rename_i hfirst
    split at h
    · simp at h
    · rename_i hproduct
      split at h
      · simp at h
      · rename_i hquotient
        simp only [ratioArithmeticSafe]
        simp at hfirst hquotient
        have hle : numerator * total / denominator ≤ maxU128 := by
          exact Nat.le_trans (Nat.div_le_self _ _) (Nat.le_of_not_gt hproduct)
        omega

theorem checked_ratio_succeeds_iff_safe
    (numerator denominator total : Nat) :
    (∃ result, checkedRatioWeight numerator denominator total = some result) ↔
      ratioArithmeticSafe numerator denominator total := by
  constructor
  · rintro ⟨result, h⟩
    exact checked_ratio_success_implies_safe numerator denominator total result h
  · intro h
    exact ⟨toWeight (.ratio numerator denominator) total,
      checked_ratio_matches_mathematical_weight numerator denominator total h⟩

theorem existing_valid_ratio_suffices
    (numerator denominator total : Nat)
    (h : validRatio numerator denominator total) :
    ratioArithmeticSafe numerator denominator total := by
  rcases h with ⟨hn, hd, hdu, ht, hp⟩
  refine ⟨hn, hd, hdu, ht, Nat.le_of_lt hp, ?_⟩
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp

theorem old_ratio_guard_excludes_safe_half_maximum :
    ratioArithmeticSafe 1 2 maxU128 ∧
    ¬ validRatio 1 2 maxU128 := by
  simp [ratioArithmeticSafe, validRatio, maxU64, maxU128]

theorem decisive_role_skips_later_ratio_checks
    (totalSupply : Nat) (first : StatusRole) (rest : List StatusRole)
    (decision : Decision)
    (hfirst : checkedRoleDecision first totalSupply = some decision)
    (hdec : decision ≠ .inProgress) :
    firstCheckedDecision totalSupply (first :: rest) = some decision := by
  simp [firstCheckedDecision, hfirst, hdec]

theorem checked_role_success_is_mathematical_decision
    (role : StatusRole) (totalSupply : Nat) (decision : Decision)
    (h : checkedRoleDecision role totalSupply = some decision) :
    decision = roleDecision role totalSupply := by
  cases hk : role.kind with
  | everyone =>
      simp [checkedRoleDecision, hk] at h
      simpa [roleDecision, hk] using h.symm
  | group size =>
      cases ht : role.threshold with
      | weight amount =>
          simp [checkedRoleDecision, hk, ht] at h
          exact h.symm
      | ratio numerator denominator =>
          simp [checkedRoleDecision, hk, ht] at h
          cases hc : checkedRatioWeight numerator denominator
              (roleTotal role totalSupply) with
          | none => simp [hc] at h
          | some weight =>
              simp [hc] at h
              exact h.symm
  | member =>
      cases ht : role.threshold with
      | weight amount =>
          simp [checkedRoleDecision, hk, ht] at h
          exact h.symm
      | ratio numerator denominator =>
          simp [checkedRoleDecision, hk, ht] at h
          cases hc : checkedRatioWeight numerator denominator
              (roleTotal role totalSupply) with
          | none => simp [hc] at h
          | some weight =>
              simp [hc] at h
              exact h.symm

theorem checked_roles_match_mathematical_status
    (totalSupply : Nat) (roles : List StatusRole)
    (hsafe : ∀ role ∈ roles,
      ∃ decision, checkedRoleDecision role totalSupply = some decision) :
    firstCheckedDecision totalSupply roles =
      some (firstDecisive (roles.map (roleDecision · totalSupply))) := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      obtain ⟨decision, hdecision⟩ := hsafe role (by simp)
      have heq := checked_role_success_is_mathematical_decision
        role totalSupply decision hdecision
      subst decision
      by_cases hprogress : roleDecision role totalSupply = .inProgress
      · have hrest : ∀ r ∈ rest,
            ∃ decision, checkedRoleDecision r totalSupply = some decision := by
          intro r hr
          exact hsafe r (by simp [hr])
        simpa [firstCheckedDecision, hdecision, hprogress,
          firstDecisive] using ih hrest
      · simp [firstCheckedDecision, hdecision, hprogress,
          firstDecisive]

private def approvingRole : StatusRole :=
  ⟨.group 1, .role, 0, .weight 1, 1, 0, 0⟩

private def unsafeLaterRole : StatusRole :=
  ⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩

theorem checked_status_matches_mathematical_on_safe_roles
    (original : ProposalStatus)
    (submission period now totalSupply : Nat) (roles : List StatusRole)
    (hstatus : original = .inProgress ∨ original = .failed)
    (hbounds : submission ≤ maxU64 ∧ period ≤ maxU64 ∧
      now ≤ maxU64 ∧ submission + period ≤ maxU64)
    (hsafe : ∀ role ∈ roles,
      ∃ decision, checkedRoleDecision role totalSupply = some decision) :
    proposalStatusChecked original submission period now totalSupply roles =
      proposalStatusForRoles original submission period now totalSupply roles := by
  have hroles := checked_roles_match_mathematical_status
    totalSupply roles hsafe
  rcases hbounds with ⟨hsub, hperiod, hnow, hsum⟩
  rcases hstatus with h | h <;> subst original <;>
    simp [proposalStatusChecked, proposalStatusForRoles,
      Nat.not_lt.mpr hsub, Nat.not_lt.mpr hperiod,
      Nat.not_lt.mpr hnow, Nat.not_lt.mpr hsum, hroles]
  all_goals split <;> simp

theorem checked_status_expiration_skips_unsafe_ratio :
    proposalStatusChecked .inProgress 0 0 1 maxU128
      [unsafeLaterRole] = some .expired := by
  decide

theorem checked_status_live_unsafe_ratio_aborts :
    proposalStatusChecked .inProgress 0 1 0 maxU128
      [unsafeLaterRole] = none := by
  decide

theorem checked_status_overflowing_expiry_precedes_roles :
    proposalStatusChecked .inProgress maxU64 1 maxU64 maxU128
      [unsafeLaterRole] = none := by
  decide

theorem ordered_status_skips_unsafe_later_ratio :
    firstCheckedDecision maxU128 [approvingRole, unsafeLaterRole] =
      some .approved ∧
    firstCheckedDecision maxU128 [unsafeLaterRole] = none := by
  decide

theorem authorized_delegation_can_reach_unsafe_ratio_weight
    (byteCost : Nat) :
    let initial : DelegationState := ⟨some "staking.near", [], 0⟩
    let registered : DelegationState :=
      ⟨some "staking.near", [("alice.near", 0)], 0⟩
    let maximal : DelegationState :=
      ⟨some "staking.near", [("alice.near", maxU128)], maxU128⟩
    registerDelegation initial "staking.near" "alice.near"
      (registrationDeposit byteCost) byteCost = some registered ∧
    delegate registered "staking.near" "alice.near" maxU128 =
      some maximal ∧
    checkedRoleDecision unsafeLaterRole maximal.total = none := by
  simp [registerDelegation, delegate, balanceOf, setBalance,
    checkedRoleDecision, unsafeLaterRole, roleTotal,
    checkedRatioWeight, maxU128]

theorem product_can_overflow_before_cap :
    checkedRatioWeight 2 1 maxU128 = none ∧
    toWeight (.ratio 2 1) maxU128 = maxU128 := by
  decide

theorem increment_can_overflow_before_cap :
    checkedRatioWeight 1 1 maxU128 = none ∧
    toWeight (.ratio 1 1) maxU128 = maxU128 := by
  decide

theorem version_checked_replacement_can_install_arithmetic_trap :
    executeValidatedPolicyReplacement
      (some (.current (WeightOrRatio.ratio 1 2)))
      (.current (WeightOrRatio.ratio 1 1)) =
        some (.current (WeightOrRatio.ratio 1 1)) ∧
    checkedRatioWeight 1 1 maxU128 = none := by
  constructor
  · rfl
  · decide

end SputnikDAO2
