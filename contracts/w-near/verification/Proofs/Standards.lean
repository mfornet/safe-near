import NearSdk.Nep141
import NearSdk.Nep145
import Proofs.StateLemmas

/-!
# wNEAR meets the NEP-141 and NEP-145 environment assumptions

`NearSdk.Nep141` and `NearSdk.Nep145` state what a caller may assume of a
NEP-141 token with NEP-145 storage management. wNEAR's model meets them: its
transfers, resolutions and storage deposits change the observable views
(`ft_balance_of`, `ft_total_supply`, `storage_balance_of`, `storage_balance_bounds`)
as the standards say.
-/

namespace WNear
open NearSdk

/-- wNEAR as callers observe it. -/
def State.ftView (s : State) : Nep141.View AccountId := ⟨s.balanceOf, s.totalSupply⟩

/-- `internal_transfer` is a NEP-141 transfer. -/
theorem transfer_nep141 {s : State} {sender receiver : AccountId} {amount : Nat}
    {memo : Option String} {s' : State} {logs : List String}
    (h : s.transfer sender receiver amount memo = .ok (s', logs)) :
    Nep141.Transfer s.ftView s'.ftView sender receiver amount := by
  unfold State.transfer at h
  simp only [bind, bind_require, pure_eq_ok] at h
  by_cases hd : sender = receiver
  · simp [hd] at h
  by_cases hp : 0 < amount
  swap
  · simp [hd, hp] at h
  simp only [ne_eq, hd, hp, not_false_eq_true, ↓reduceIte] at h
  obtain ⟨w, hw, h⟩ := bind_ok_iff.mp h
  obtain ⟨d, hdep, h⟩ := bind_ok_iff.mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨hreg, hcov, hts, rfl⟩ := State.withdraw_ok.mp hw
  obtain ⟨hrreg, -, -, rfl⟩ := State.deposit_ok.mp hdep
  simp only [State.setBalance_registered] at hrreg
  refine ⟨hd, hp, by simp [State.ftView, State.balanceOf, hreg, hcov], ?_⟩
  simp only [State.ftView, Nep141.View.move, Nep141.View.mk.injEq]
  refine ⟨?_, Nat.sub_add_cancel hts⟩
  funext a
  by_cases has : a = sender
  · subst has
    simp [State.balanceOf, State.setBalance, hreg, Function.update, hd]
  · by_cases har : a = receiver
    · subst har
      simp [State.balanceOf, State.setBalance, hrreg, Function.update, has]
    · simp [State.balanceOf, State.setBalance, Function.update, has, har]

/-- `ft_transfer` is a NEP-141 transfer from the predecessor. -/
theorem ftTransfer_nep141 {s : State} {env : Env} {receiver : AccountId} {amount : Nat}
    {memo : Option String} {o : Outcome} (h : ftTransfer s env receiver amount memo = .ok o) :
    Nep141.Transfer s.ftView o.state.ftView env.predecessor receiver amount := by
  unfold ftTransfer at h
  simp only [bind, bind_require, pure_eq_ok] at h
  by_cases hy : env.attachedDeposit = 1
  swap
  · simp [hy] at h
  simp only [hy, ↓reduceIte] at h
  obtain ⟨⟨t, logs⟩, ht, h⟩ := bind_ok_iff.mp h
  simp only [Except.ok.injEq] at h
  subst h
  exact transfer_nep141 ht

/-- No refund leaves the view as it was: a move of nothing. -/
private theorem move_zero (v : Nep141.View AccountId) (source target : AccountId) :
    v.move source target 0 = v := by
  cases v with
  | mk balanceOf totalSupply =>
    simp only [Nep141.View.move, Nat.sub_zero, Nat.add_zero, Nep141.View.mk.injEq, and_true]
    funext a
    by_cases hs : a = source
    · subst hs; simp
    · by_cases ht : a = target
      · subst ht; simp [hs]
      · simp [hs, ht]

/-- The refund half of `ft_resolve_transfer` is a NEP-141 resolution, for an unused amount
within the transfer and distinct accounts (which the transfer guaranteed). -/
theorem resolveRefund_nep141 {s : State} {sender receiver : AccountId} {amount unused used : Nat}
    {o : Outcome} (hdistinct : receiver ≠ sender) (hunused : unused ≤ amount)
    (h : resolveRefund s sender receiver amount unused = .ok o) (hret : o.ret = .u128 used) :
    Nep141.Resolve s.ftView o.state.ftView sender receiver amount unused used := by
  have hmin : min unused (s.ftView.balanceOf receiver) = min (s.balanceOf receiver) unused :=
    Nat.min_comm _ _
  unfold resolveRefund at h
  by_cases hu : 0 < unused
  swap
  · simp only [hu, ↓reduceIte, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp only [Ret.u128.injEq] at hret
    have h0 : min unused (s.ftView.balanceOf receiver) = 0 := by omega
    exact .refund hunused hdistinct (by rw [h0, move_zero]) (by omega)
  simp only [hu, ↓reduceIte] at h
  by_cases hb : 0 < s.balanceOf receiver
  swap
  · simp only [hb, ↓reduceIte, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp only [Ret.u128.injEq] at hret
    have h0 : min unused (s.ftView.balanceOf receiver) = 0 := by
      simp only [State.ftView]; omega
    exact .refund hunused hdistinct (by rw [h0, move_zero]) (by omega)
  simp only [hb, ↓reduceIte] at h
  obtain ⟨hrreg, hrbal⟩ := State.balanceOf_pos_mem hb
  by_cases hsreg : sender ∈ s.registered
  · simp only [State.setBalance_registered, hsreg, ↓reduceIte, bind, bind_require, pure_eq_ok] at h
    split_ifs at h with hover
    simp only [Except.ok.injEq] at h
    subst h
    simp only [Ret.u128.injEq] at hret
    refine .refund hunused hdistinct ?_ (by rw [hmin]; exact hret.symm)
    rw [hmin]
    simp only [State.ftView, Nep141.View.move, Nep141.View.mk.injEq, State.setBalance_totalSupply,
      and_true]
    funext a
    by_cases har : a = receiver
    · subst har
      simp [State.balanceOf, State.setBalance, hrreg, Function.update, hdistinct]
    · by_cases has : a = sender
      · subst has
        simp [State.balanceOf, State.setBalance, hsreg, Function.update, Ne.symm hdistinct]
      · simp [State.balanceOf, State.setBalance, Function.update, har, has]
  · simp only [State.setBalance_registered, hsreg, ↓reduceIte, bind, bind_require, pure_eq_ok] at h
    split_ifs at h with hsupply
    simp only [Except.ok.injEq] at h
    subst h
    simp only [Ret.u128.injEq] at hret
    refine .burn hunused (by rw [hmin]; exact hsupply) ?_ hret.symm
    rw [hmin]
    simp only [State.ftView, Nep141.View.burn, Nep141.View.mk.injEq]
    refine ⟨?_, rfl⟩
    funext a
    by_cases har : a = receiver
    · subst har
      simp [State.balanceOf, State.setBalance, hrreg, Function.update]
    · simp [State.balanceOf, State.setBalance, Function.update, har]

/-- `ft_on_transfer` can report at most the whole amount unused. -/
theorem unusedAmount_le {amount u : Nat} {r : PromiseResult} (h : unusedAmount amount r = .ok u) :
    u ≤ amount := by
  cases r with
  | notReady => simp [unusedAmount] at h
  | failed => simp only [unusedAmount, pure_eq_ok, Except.ok.injEq] at h; omega
  | successful v =>
    cases v with
    | none => simp only [unusedAmount, pure_eq_ok, Except.ok.injEq] at h; omega
    | some n => simp only [unusedAmount, pure_eq_ok, Except.ok.injEq] at h; omega

/-- `ft_resolve_transfer` is a NEP-141 resolution of a transfer between distinct accounts, for
the unused amount `ft_on_transfer` reported. -/
theorem ftResolveTransfer_nep141 {s : State} {env : Env} {sender receiver : AccountId}
    {amount used : Nat} {o : Outcome} (hdistinct : receiver ≠ sender)
    (h : ftResolveTransfer s env sender receiver amount = .ok o) (hret : o.ret = .u128 used) :
    ∃ unused, Nep141.Resolve s.ftView o.state.ftView sender receiver amount unused used := by
  unfold ftResolveTransfer at h
  cases hr : env.promiseResult with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, bind, pure_eq_ok] at h
    obtain ⟨u, hu, h⟩ := bind_ok_iff.mp (by simpa only [bind_ok'] using h)
    exact ⟨u, resolveRefund_nep141 hdistinct (unusedAmount_le hu) h hret⟩

/-- wNEAR's storage registration as callers observe it. -/
def State.storageView (s : State) : Nep145.View AccountId :=
  ⟨fun a => (s.storageBalanceOf a).map fun b => ⟨b.total, b.available⟩, s.storageMin, some s.storageMin⟩

/-- `storage_deposit` is a NEP-145 deposit for the account it names (default: the
predecessor). -/
theorem storageDeposit_nep145 {s : State} {env : Env} {account : Option AccountId}
    {registrationOnly : Option Bool} {o : Outcome}
    (h : storageDeposit s env account registrationOnly = .ok o) :
    Nep145.Deposit s.storageView o.state.storageView (account.getD env.predecessor)
      env.attachedDeposit := by
  unfold storageDeposit at h
  by_cases hreg : account.getD env.predecessor ∈ s.registered
  · simp only [hreg, ↓reduceIte, pure_eq_ok, Except.ok.injEq] at h
    subst h
    refine ⟨fun hnot => ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · simp [State.storageView, Nep145.View.registered, State.storageBalanceOf, hreg] at hnot
    · simp [State.storageView, Nep145.View.registered, State.storageBalanceOf, hreg]
  · simp only [hreg, ↓reduceIte, bind, bind_require, pure_eq_ok] at h
    split_ifs at h with hmin
    obtain ⟨t, ht, h⟩ := bind_ok_iff.mp h
    obtain ⟨-, rfl⟩ := State.registerAccount_ok.mp ht
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨fun _ => hmin, ?_, fun a ha => ?_, rfl, rfl⟩
    · simp [State.storageView, Nep145.View.registered, State.storageBalanceOf, State.register,
        State.storageMin]
    · simp [State.storageView, State.storageBalanceOf, State.register, State.storageMin, ha]

end WNear
