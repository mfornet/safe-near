import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic
import Spec.Conservation
import Proofs.Authorization

namespace WNear


/-- Refund resolution neither creates NEAR promises nor adds liabilities. -/
theorem resolveRefund_accounting {s : State} {sender receiver : AccountId}
    {amount unused : Nat} {o : Outcome}
    (h : resolveRefund s sender receiver amount unused = .ok o) :
    o.state.totalSupply ≤ s.totalSupply ∧
    o.state.registered = s.registered ∧ o.nearOut = 0 := by
  unfold resolveRefund at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> simp_all <;> subst o <;>
    simp [Outcome.nearOut]

theorem ftResolveTransfer_accounting {s : State} {env : Env}
    {sender receiver : AccountId} {amount : Nat} {o : Outcome}
    (h : ftResolveTransfer s env sender receiver amount = .ok o) :
    o.state.totalSupply ≤ s.totalSupply ∧
    o.state.registered = s.registered ∧ o.nearOut = 0 := by
  unfold ftResolveTransfer at h
  cases hr : env.promiseResult with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, pure_eq_ok, bind, bind_ok'] at h
    obtain ⟨unused, _, h⟩ := bind_ok_iff.mp h
    exact resolveRefund_accounting h

private theorem conditional_transfer_sum (receiver : AccountId) (amount : Nat) :
    ((if 0 < amount then [Promise.transfer receiver amount] else []).map Promise.transferred).sum = amount := by
  by_cases h : 0 < amount <;> simp [h, Promise.transferred]; omega

private theorem retained_fee (deposit fee : Nat) (h : fee ≤ deposit) :
    (fee : Int) ≤ (deposit : Int) - ((deposit - fee : Nat) : Int) := by omega

private theorem storageDeposit_conservation {s : State} {env : Env}
    {account : Option AccountId} {registrationOnly : Option Bool} {o : Outcome}
    (h : storageDeposit s env account registrationOnly = .ok o) :
    (o.state.totalSupply : Int) - s.totalSupply +
      s.storageMin * ((o.state.registered.card : Int) - s.registered.card) ≤
      (env.attachedDeposit : Int) - o.nearOut := by
  unfold storageDeposit at h
  dsimp only at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    subst o
    simp only [sub_self, mul_zero, zero_add, Outcome.nearOut]
    rw [conditional_transfer_sum]
    omega
  · simp only [bind, bind_require, pure_eq_ok] at h
    by_cases hfee : s.storageMin ≤ env.attachedDeposit
    · simp only [ite_eq_left hfee] at h
      obtain ⟨s1, hreg, h⟩ := bind_ok_iff.mp h
      obtain ⟨ha, rfl⟩ := State.registerAccount_ok.mp hreg
      simp only [Except.ok.injEq] at h
      subst o
      have hmin : (s.register (account.getD env.predecessor)).storageMin = s.storageMin := rfl
      simp only [State.register_registered, State.register_totalSupply, hmin,
        Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one,
        add_sub_cancel_left, mul_one, sub_self, zero_add, Outcome.nearOut]
      rw [conditional_transfer_sum]
      exact retained_fee _ _ hfee
    · simp [hfee] at h

@[blueprint "thm:conservation"
  (statement := /-- \cref{spec:conservation} holds. -/)]
theorem conservation : Conservation := by
  intro cfg s env call o hinv h
  clear hinv
  replace h := step_some_ok h
  cases call <;> simp only [dispatch] at h
  case ftResolveTransfer sender receiver amount =>
    obtain ⟨hsupply, hregistered, hout⟩ := ftResolveTransfer_accounting h
    simp only [hregistered, sub_self, mul_zero, add_zero, hout, Nat.cast_zero, sub_zero]
    omega
  case storageDeposit account registrationOnly =>
    exact storageDeposit_conservation h
  all_goals
    try simp only [nearDeposit, nearWithdraw, ftTransfer, ftTransferCall,
      storageWithdraw, storageUnregister, State.transfer] at h
    try simp only [bind, bind_require, bind_ok', bind_error', pure_eq_ok, throw_eq, bind_ite] at h
    try split_ifs at h
    all_goals
      try simp only [bind_ok_iff, State.deposit_ok, State.withdraw_ok,
        State.registerAccount_ok, Except.ok.injEq, reduceCtorEq] at h
      all_goals
        simp only [State.storageMin] at *
        generalize hprice : storagePricePerByte = price at *
        clear hprice
        first
        | solve
          | aesop (add norm simp [State.setBalance, State.register, State.unregister,
              Outcome.nearOut, Promise.transferred, Function.update_apply,
              Finset.card_insert_of_notMem, Finset.card_erase_of_mem, Nat.cast_add,
              Nat.cast_sub]) (add safe (by omega))
        | subst o
          have hc : 1 ≤ s.registered.card := by
            have : 0 < s.registered.card := Finset.card_pos.mpr ⟨env.predecessor, by assumption⟩
            omega
          simp_all [State.unregister, Outcome.nearOut, Promise.transferred, Nat.cast_sub]


end WNear
