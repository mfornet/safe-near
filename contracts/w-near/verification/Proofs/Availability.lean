import Spec.Availability
import Proofs.StateLemmas

/-!
# Availability
-/

namespace WNear

open State

/-- `step` on a payable, non-private method is just the method. -/
theorem step_nearWithdraw (cfg : Config) (s : State) (env : Env) (amount : Nat) :
    step cfg (some s) env (.nearWithdraw amount) = nearWithdraw s env amount := rfl

theorem step_nearDeposit (cfg : Config) (s : State) (env : Env) :
    step cfg (some s) env .nearDeposit = nearDeposit s env := rfl

@[blueprint "thm:withdraw-available"
  (statement := /-- \cref{spec:withdraw-available} holds. -/)]
theorem withdraw_available : WithdrawAvailable := by
  intro cfg s env amount hs hreg hamt hdep hbound
  have hts : amount ≤ s.totalSupply := le_trans hamt (hs.supply ▸ balance_le_supply hreg)
  have hw : s.withdraw env.predecessor amount =
      .ok { s.setBalance env.predecessor (s.balance env.predecessor - amount) with
            totalSupply := s.totalSupply - amount } :=
    withdraw_ok.mpr ⟨hreg, hamt, hts, rfl⟩
  rw [step_nearWithdraw]
  unfold WNear.nearWithdraw
  simp only [bind, bind_require, bind_ok', pure_eq_ok, hdep, ite_true, hw, hbound]

@[blueprint "thm:deposit-available"
  (statement := /-- \cref{spec:deposit-available} holds. -/)]
theorem deposit_available : DepositAvailable := by
  intro cfg s env hs hpos hbound hcond
  rw [step_nearDeposit]
  unfold WNear.nearDeposit
  simp only [bind, bind_require, bind_ok', pure_eq_ok, bind_ite, hpos, ite_true]
  have hd : env.attachedDeposit < u128Bound := by omega
  by_cases hreg : env.predecessor ∈ s.registered
  · have hb : s.balance env.predecessor + env.attachedDeposit < u128Bound :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right (hs.supply ▸ balance_le_supply hreg) _) hbound
    have hdep : s.deposit env.predecessor env.attachedDeposit =
        .ok { s.setBalance env.predecessor (s.balance env.predecessor + env.attachedDeposit) with
              totalSupply := s.totalSupply + env.attachedDeposit } :=
      deposit_ok.mpr ⟨hreg, hb, hbound, rfl⟩
    simp only [hreg, ite_true, hdep, bind_ok']
    refine ⟨_, rfl, ?_⟩
    simp [hreg]
  · have hmin : s.storageMin ≤ env.attachedDeposit := hcond.resolve_left hreg
    have hr : s.registerAccount env.predecessor = .ok (s.register env.predecessor) :=
      registerAccount_ok.mpr ⟨hreg, rfl⟩
    have hmem : env.predecessor ∈ (s.register env.predecessor).registered := by simp
    have hbal : (s.register env.predecessor).balance env.predecessor = 0 := by simp
    have hmin' : (s.register env.predecessor).storageMin = s.storageMin := rfl
    have hdep : (s.register env.predecessor).deposit env.predecessor
        (env.attachedDeposit - s.storageMin) =
        .ok { (s.register env.predecessor).setBalance env.predecessor
                (0 + (env.attachedDeposit - s.storageMin)) with
              totalSupply := s.totalSupply + (env.attachedDeposit - s.storageMin) } := by
      refine deposit_ok.mpr ⟨hmem, ?_, ?_, ?_⟩
      · rw [hbal]; omega
      · show s.totalSupply + (env.attachedDeposit - s.storageMin) < u128Bound; omega
      · rw [hbal]; rfl
    simp only [hreg, ite_false, hmin, ite_true, hr, bind_ok', hmin', hdep]
    refine ⟨_, rfl, ?_⟩
    have hz : s.balance env.predecessor = 0 := hs.unregistered_zero _ hreg
    simp [hreg, hz]
    omega

end WNear
