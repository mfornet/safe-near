import Model.Delegation

namespace SputnikDAO2

theorem balance_sum_set (balances : List (String × Nat))
    (account : String) (newAmount : Nat) :
    balanceSum (setBalance balances account newAmount) +
      (balanceOf balances account).getD 0 =
    balanceSum balances + newAmount := by
  induction balances with
  | nil => simp [balanceSum, setBalance, balanceOf]
  | cons entry rest ih =>
      obtain ⟨user, amount⟩ := entry
      by_cases h : user = account
      · subst user
        simp [balanceSum, setBalance, balanceOf]
        omega
      · simp only [balanceSum, setBalance, balanceOf, beq_iff_eq, h,
          ↓reduceIte, Option.getD]
        simp only [Option.getD] at ih
        omega

theorem registration_requires_staking_caller (state : DelegationState)
    (caller account : String) (deposit byteCost : Nat)
    (h : state.stakingId ≠ some caller) :
    registerDelegation state caller account deposit byteCost = none := by
  simp [registerDelegation, h]

theorem fresh_registration_preserves_accounting (state : DelegationState)
    (caller account : String) (byteCost : Nat)
    (hcaller : state.stakingId = some caller)
    (hfresh : balanceOf state.balances account = none)
    (hcoherent : coherentDelegation state) :
    ∃ next,
      registerDelegation state caller account
        (registrationDeposit byteCost) byteCost = some next ∧
      coherentDelegation next := by
  let next : DelegationState :=
    { state with balances := setBalance state.balances account 0 }
  have hstep : registerDelegation state caller account
      (registrationDeposit byteCost) byteCost = some next := by
    simp [registerDelegation, hcaller, next]
  have hsum := balance_sum_set state.balances account 0
  simp [hfresh] at hsum
  refine ⟨next, hstep, ?_⟩
  simp only [coherentDelegation, next]
  rw [hsum]
  exact hcoherent

theorem delegation_preserves_accounting (state : DelegationState)
    (caller account : String) (amount previous : Nat)
    (hcaller : state.stakingId = some caller)
    (hregistered : balanceOf state.balances account = some previous)
    (hbalance : previous + amount ≤ maxU128)
    (htotal : state.total + amount ≤ maxU128)
    (hcoherent : coherentDelegation state) :
    ∃ next, delegate state caller account amount = some next ∧
      coherentDelegation next := by
  let next : DelegationState :=
    ⟨state.stakingId, setBalance state.balances account (previous + amount),
      state.total + amount⟩
  have hstep : delegate state caller account amount = some next := by
    simp [delegate, hcaller, hregistered, Nat.not_lt.mpr hbalance,
      Nat.not_lt.mpr htotal, next]
  have hsum := balance_sum_set state.balances account (previous + amount)
  simp [hregistered] at hsum
  refine ⟨next, hstep, ?_⟩
  simp only [coherentDelegation, next] at *
  omega

theorem undelegation_preserves_accounting (state : DelegationState)
    (caller account : String) (amount : Nat)
    (hcaller : state.stakingId = some caller)
    (hbalance : amount ≤ (balanceOf state.balances account).getD 0)
    (htotal : amount ≤ state.total)
    (hcoherent : coherentDelegation state) :
    ∃ next, undelegate state caller account amount = some next ∧
      coherentDelegation next := by
  let previous := (balanceOf state.balances account).getD 0
  let next : DelegationState :=
    ⟨state.stakingId, setBalance state.balances account (previous - amount),
      state.total - amount⟩
  have hstep : undelegate state caller account amount = some next := by
    simp [undelegate, hcaller, Nat.not_lt.mpr hbalance,
      Nat.not_lt.mpr htotal, previous, next]
  have hsum := balance_sum_set state.balances account (previous - amount)
  refine ⟨next, hstep, ?_⟩
  simp only [coherentDelegation, next] at *
  omega

theorem register_existing_can_break_accounting :
    let state : DelegationState := ⟨some "stake.near", [("alice.near", 1)], 1⟩
    coherentDelegation state ∧
    registerDelegation state "stake.near" "alice.near" 0 0 =
      some ⟨some "stake.near", [("alice.near", 0)], 1⟩ ∧
    ¬ coherentDelegation ⟨some "stake.near", [("alice.near", 0)], 1⟩ := by
  simp [coherentDelegation, registerDelegation, registrationDeposit,
    setBalance, balanceSum, maxU128]

theorem zero_undelegation_registers_absent_account :
    undelegate ⟨some "stake.near", [], 0⟩
      "stake.near" "alice.near" 0 =
      some ⟨some "stake.near", [("alice.near", 0)], 0⟩ := by
  decide

theorem incoherent_total_blocks_undelegation :
    undelegate ⟨some "stake.near", [("alice.near", 1)], 0⟩
      "stake.near" "alice.near" 1 = none := by
  decide

theorem checked_delegation_overflow_aborts :
    delegate ⟨some "stake.near", [("alice.near", maxU128)], maxU128⟩
      "stake.near" "alice.near" 1 = none := by
  simp [delegate, balanceOf, maxU128]

end SputnikDAO2
