import Spec.Authorization
import Proofs.Invariants

namespace WNear

@[blueprint "thm:balance-authorization"
  (statement := /-- \cref{spec:balance-authorization} holds. -/)]
theorem balance_authorization : BalanceAuthorization := by
  sorry

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
