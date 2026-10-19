import Spec.Authorization
import Proofs.Invariants

namespace WNear

/-- A receiver can lose at most the unused amount during refund resolution.
No other account loses balance, even when sender and receiver coincide. -/
theorem resolveRefund_balance_loss {s : State} {sender receiver a : AccountId}
    {amount unused : Nat} {o : Outcome} (hwf : s.WF)
    (h : resolveRefund s sender receiver amount unused = .ok o)
    (hloss : o.state.balance a < s.balance a) :
    a = receiver ∧ s.balance a - o.state.balance a ≤ unused := by
  unfold resolveRefund at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> simp_all <;> subst o
  all_goals
    by_cases hr : a = receiver <;> by_cases hs : a = sender <;>
      simp_all [State.setBalance, Function.update_apply, State.balanceOf_eq_balance hwf] <;> omega

/-- Every successful decoding branch caps the refund by the transfer amount. -/
theorem unusedAmount_le {amount unused : Nat} {result : PromiseResult}
    (h : unusedAmount amount result = .ok unused) : unused ≤ amount := by
  cases result with
  | notReady => simp [unusedAmount] at h
  | failed => simp [unusedAmount] at h; omega
  | successful value =>
    cases value <;> simp [unusedAmount] at h <;> omega

theorem ftResolveTransfer_balance_loss {s : State} {env : Env}
    {sender receiver a : AccountId} {amount : Nat} {o : Outcome} (hwf : s.WF)
    (h : ftResolveTransfer s env sender receiver amount = .ok o)
    (hloss : o.state.balance a < s.balance a) :
    a = receiver ∧ s.balance a - o.state.balance a ≤ amount := by
  unfold ftResolveTransfer at h
  cases hr : env.promiseResult with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, pure_eq_ok, bind, bind_ok'] at h
    obtain ⟨unused, hu, h⟩ := bind_ok_iff.mp h
    obtain ⟨ha, hbound⟩ := resolveRefund_balance_loss hwf h hloss
    exact ⟨ha, hbound.trans (unusedAmount_le hu)⟩

@[blueprint "thm:balance-authorization"
  (statement := /-- \cref{spec:balance-authorization} holds. -/)]
theorem balance_authorization : BalanceAuthorization := by
  intro cfg s env call o hinv h a hne hloss
  have hz := hinv.unregistered_zero
  have h := step_some_ok h
  cases call <;> simp only [dispatch] at h
  case ftResolveTransfer sender receiver amount =>
    obtain ⟨rfl, hbound⟩ := ftResolveTransfer_balance_loss hinv.toWF h hloss
    exact ⟨_, _, rfl, hbound⟩
  all_goals
    exfalso
    try simp only [nearDeposit, nearWithdraw, ftTransfer, ftTransferCall,
      storageDeposit, storageWithdraw, storageUnregister, State.transfer] at h
    try simp only [bind, bind_require, bind_ok', bind_error', pure_eq_ok, throw_eq, bind_ite] at h
    try split_ifs at h
    all_goals
      try simp only [bind_ok_iff, State.deposit_ok, State.withdraw_ok,
        State.registerAccount_ok, Except.ok.injEq, reduceCtorEq] at h
      all_goals aesop (add norm simp [State.setBalance, State.register, State.unregister,
        Function.update_apply]) (add safe (by omega))

/-- Callback refunds change balances and supply, never registration. -/
theorem resolveRefund_registered {s : State} {sender receiver : AccountId}
    {amount unused : Nat} {o : Outcome}
    (h : resolveRefund s sender receiver amount unused = .ok o) :
    o.state.registered = s.registered := by
  unfold resolveRefund at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> simp_all <;> subst o <;> rfl

theorem ftResolveTransfer_registered {s : State} {env : Env}
    {sender receiver : AccountId} {amount : Nat} {o : Outcome}
    (h : ftResolveTransfer s env sender receiver amount = .ok o) :
    o.state.registered = s.registered := by
  unfold ftResolveTransfer at h
  cases hr : env.promiseResult with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, pure_eq_ok, bind, bind_ok'] at h
    obtain ⟨unused, _, h⟩ := bind_ok_iff.mp h
    exact resolveRefund_registered h

@[blueprint "thm:registration-authorization"
  (statement := /-- \cref{spec:registration-authorization} holds. -/)]
theorem registration_authorization : RegistrationAuthorization := by
  intro cfg s env call o _ h a ha hmissing
  have h := step_some_ok h
  cases call <;> simp only [dispatch] at h
  case ftResolveTransfer sender receiver amount =>
    exact False.elim (hmissing ((ftResolveTransfer_registered h).symm ▸ ha))
  all_goals
    try simp only [nearDeposit, nearWithdraw, ftTransfer, ftTransferCall,
      storageDeposit, storageWithdraw, storageUnregister, State.transfer] at h
    try simp only [bind, bind_require, bind_ok', bind_error', pure_eq_ok, throw_eq, bind_ite] at h
    try split_ifs at h
    all_goals
      try simp only [bind_ok_iff, State.deposit_ok, State.withdraw_ok,
        State.registerAccount_ok, Except.ok.injEq, reduceCtorEq] at h
      all_goals aesop

end WNear
