import Proofs.StateLemmas

/-!
# Model outcomes for initialized `near_deposit`

These equations expose the model's checks in the order used by `DepositBody.dcase`.
They cover failures as well as success, for the method's agreement proof.
-/

namespace WNear.Binary.NearDepositMethod

/-- A zero deposit panics before registration or balance checks. -/
theorem nearDeposit_zero (s : WNear.State) (env : WNear.Env) (hd : env.attachedDeposit = 0) :
    WNear.nearDeposit s env = .error .requiresPositiveDeposit := by
  simp [WNear.nearDeposit, WNear.require, hd]

/-- An unregistered predecessor must cover the registration fee before minting. -/
theorem nearDeposit_too_small (s : WNear.State) (env : WNear.Env)
    (hr : env.predecessor ∉ s.registered) (hd : 0 < env.attachedDeposit)
    (hm : env.attachedDeposit < s.storageMin) :
    WNear.nearDeposit s env = .error .depositTooSmall := by
  simp [WNear.nearDeposit, WNear.require, hr, hd, Nat.not_le.mpr hm]

/-- Once registration is affordable, the new account receives the deposit less its fee.
Keep the minting operation separate so its checked additions can be matched independently. -/
theorem nearDeposit_after_registration (s : WNear.State) (env : WNear.Env)
    (hr : env.predecessor ∉ s.registered) (hd : 0 < env.attachedDeposit)
    (hm : s.storageMin ≤ env.attachedDeposit) :
    WNear.nearDeposit s env = (do
      let s' ← (s.register env.predecessor).deposit env.predecessor (env.attachedDeposit - s.storageMin)
      pure { state := s', logs := [s!"Deposit {env.attachedDeposit - s.storageMin} NEAR to {env.predecessor}"] }) := by
  have hreg : s.registerAccount env.predecessor = .ok (s.register env.predecessor) :=
    WNear.State.registerAccount_ok.mpr ⟨hr, rfl⟩
  have hmin : (s.register env.predecessor).storageMin = s.storageMin := rfl
  simp only [WNear.nearDeposit, bind, WNear.bind_require, hd, ite_true, hr, ite_false, hm,
    hreg, WNear.pure_eq_ok, WNear.bind_ok']
  rw [hmin]

/-- The two checked additions of `internal_deposit`, in their execution order. -/
theorem deposit_registered_cases (s : WNear.State) (a : WNear.AccountId) (amount : Nat)
    (hr : a ∈ s.registered) :
    s.deposit a amount =
      if WNear.u128Bound ≤ s.balance a + amount then .error .balanceOverflow
      else if WNear.u128Bound ≤ s.totalSupply + amount then .error .totalSupplyOverflow
      else .ok { s.setBalance a (s.balance a + amount) with totalSupply := s.totalSupply + amount } := by
  simp [WNear.State.deposit, WNear.State.unwrapBalance, WNear.require, hr]
  split_ifs <;> simp_all <;> omega

/-- All minting outcomes after a new predecessor has paid the registration fee. -/
theorem nearDeposit_unregistered (s : WNear.State) (env : WNear.Env)
    (hr : env.predecessor ∉ s.registered) (hd : 0 < env.attachedDeposit)
    (hm : s.storageMin ≤ env.attachedDeposit) :
    WNear.nearDeposit s env =
      if WNear.u128Bound ≤ env.attachedDeposit - s.storageMin then .error .balanceOverflow
      else if WNear.u128Bound ≤ s.totalSupply + (env.attachedDeposit - s.storageMin) then
        .error .totalSupplyOverflow
      else .ok
        { state := { (s.register env.predecessor).setBalance env.predecessor
              (env.attachedDeposit - s.storageMin) with
                totalSupply := s.totalSupply + (env.attachedDeposit - s.storageMin) }
          logs := [s!"Deposit {env.attachedDeposit - s.storageMin} NEAR to {env.predecessor}"] } := by
  rw [nearDeposit_after_registration s env hr hd hm]
  rw [deposit_registered_cases _ _ _ (by simp)]
  simp only [WNear.State.register_balance, Function.update_self, Nat.zero_add, WNear.State.register_totalSupply]
  split_ifs <;> rfl

/-- For a registered predecessor, mint the entire attached deposit. The balance overflow
check precedes the total-supply overflow check, as in the binary. -/
theorem nearDeposit_registered (s : WNear.State) (env : WNear.Env)
    (hr : env.predecessor ∈ s.registered) :
    WNear.nearDeposit s env =
      if env.attachedDeposit = 0 then .error .requiresPositiveDeposit
      else if WNear.u128Bound ≤ s.balance env.predecessor + env.attachedDeposit then
        .error .balanceOverflow
      else if WNear.u128Bound ≤ s.totalSupply + env.attachedDeposit then
        .error .totalSupplyOverflow
      else .ok
        { state := { s.setBalance env.predecessor (s.balance env.predecessor + env.attachedDeposit) with
              totalSupply := s.totalSupply + env.attachedDeposit }
          logs := [s!"Deposit {env.attachedDeposit} NEAR to {env.predecessor}"] } := by
  by_cases hd : env.attachedDeposit = 0
  · simp [nearDeposit_zero s env hd, hd]
  have hpos : 0 < env.attachedDeposit := Nat.pos_of_ne_zero hd
  simp [WNear.nearDeposit, WNear.require, hd, hpos, hr, WNear.State.deposit, WNear.State.unwrapBalance]
  split_ifs <;> simp_all <;> omega

end WNear.Binary.NearDepositMethod
