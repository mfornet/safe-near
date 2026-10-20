import Proofs.StateLemmas

/-!
# Invariant preservation

One lemma per method, then `inv_preserved` assembles them through `step`.
-/

namespace WNear

open State

/-- A successful `step` on an initialised contract is a successful `dispatch`. -/
theorem step_some_ok {cfg : Config} {s : State} {env : Env} {call : Call} {o : Outcome}
    (h : step cfg (some s) env call = .ok o) : dispatch s env call = .ok o := by
  unfold step at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> cases call <;> simp_all [dispatch]

/-- A successful `step` on an uninitialised contract is `new`. -/
theorem step_none_ok {cfg : Config} {env : Env} {call : Call} {o : Outcome}
    (h : step cfg none env call = .ok o) : call = .new ∧ o = new cfg := by
  unfold step at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> cases call <;> simp_all

theorem Inv.mk' {cfg : Config} {s : State} (hwf : s.WF) (hsup : s.supply = s.totalSupply)
    (husage : s.accountStorageUsage = cfg.measuredAccountStorageUsage) : Inv cfg s :=
  { toWF := hwf, supply := hsup, usage := husage }

theorem Inv.deposit {cfg : Config} {s s' : State} {a : AccountId} {amount : Nat}
    (hs : Inv cfg s) (h : s.deposit a amount = .ok s') : Inv cfg s' := by
  obtain ⟨ha, h1, h2, rfl⟩ := deposit_ok.mp h
  refine Inv.mk' ((hs.toWF.setBalance ha (b := s.balance a + amount) h1).withTotalSupply
    (t := s.totalSupply + amount) h2) ?_ hs.usage
  have e := supply_setBalance_of_mem ha (s.balance a + amount)
  have hsup := hs.supply
  show (s.setBalance a (s.balance a + amount)).supply = s.totalSupply + amount
  omega

theorem Inv.withdraw {cfg : Config} {s s' : State} {a : AccountId} {amount : Nat}
    (hs : Inv cfg s) (h : s.withdraw a amount = .ok s') : Inv cfg s' := by
  obtain ⟨ha, h1, h2, rfl⟩ := withdraw_ok.mp h
  have hb : s.balance a - amount < u128Bound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hs.balance_lt a)
  have ht : s.totalSupply - amount < u128Bound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs.totalSupply_lt
  refine Inv.mk' ((hs.toWF.setBalance ha hb).withTotalSupply ht) ?_ hs.usage
  have e := supply_setBalance_of_mem ha (s.balance a - amount)
  have hsup := hs.supply
  show (s.setBalance a (s.balance a - amount)).supply = s.totalSupply - amount
  omega

theorem Inv.registerAccount {cfg : Config} {s s' : State} {a : AccountId}
    (hs : Inv cfg s) (h : s.registerAccount a = .ok s') : Inv cfg s' := by
  obtain ⟨ha, rfl⟩ := registerAccount_ok.mp h
  exact Inv.mk' (hs.toWF.register a) (by rw [supply_register_of_not_mem ha]; exact hs.supply) hs.usage

theorem Inv.transfer {cfg : Config} {s s' : State} {sender receiver : AccountId}
    {amount : Nat} {memo : Option String} {logs : List String}
    (hs : Inv cfg s) (h : s.transfer sender receiver amount memo = .ok (s', logs)) :
    Inv cfg s' := by
  unfold State.transfer at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h
  obtain ⟨s1, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := bind_ok_iff.mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact (hs.withdraw h1).deposit h2

theorem Inv.new {cfg : Config} (hcfg : cfg.WF) : Inv cfg (new cfg).state := by
  refine Inv.mk' ⟨fun _ _ => rfl, fun _ => ?_, ?_, hcfg⟩ ?_ rfl
  · simp [WNear.new, u128Bound]
  · simp [WNear.new, u128Bound]
  · simp [WNear.new, State.supply]

theorem Inv.nearDeposit {cfg : Config} {s : State} {env : Env} {o : Outcome}
    (hs : Inv cfg s) (h : nearDeposit s env = .ok o) : Inv cfg o.state := by
  unfold WNear.nearDeposit at h
  simp only [bind, bind_require, bind_ok', pure_eq_ok] at h
  split_ifs at h
  · -- already registered
    obtain ⟨s1, h1, h⟩ := bind_ok_iff.mp h
    simp only [Except.ok.injEq] at h
    subst h
    exact hs.deposit h1
  · -- register first, then deposit the remainder
    obtain ⟨s1, h1, h⟩ := bind_ok_iff.mp h
    obtain ⟨s2, h2, h⟩ := bind_ok_iff.mp h
    simp only [Except.ok.injEq] at h
    subst h
    exact (hs.registerAccount h1).deposit h2

theorem Inv.nearWithdraw {cfg : Config} {s : State} {env : Env} {amount : Nat} {o : Outcome}
    (hs : Inv cfg s) (h : nearWithdraw s env amount = .ok o) : Inv cfg o.state := by
  unfold WNear.nearWithdraw at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> first
    | exact (bind_const_error h).elim
    | (obtain ⟨s1, h1, h⟩ := bind_ok_iff.mp h
       simp only [Except.ok.injEq] at h
       subst h
       exact hs.withdraw h1)

theorem Inv.ftTransfer {cfg : Config} {s : State} {env : Env} {receiver : AccountId}
    {amount : Nat} {memo : Option String} {o : Outcome}
    (hs : Inv cfg s) (h : ftTransfer s env receiver amount memo = .ok o) : Inv cfg o.state := by
  unfold WNear.ftTransfer at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h
  obtain ⟨⟨s1, logs⟩, h1, h⟩ := bind_ok_iff.mp h
  simp only [Except.ok.injEq] at h
  subst h
  exact hs.transfer h1

theorem Inv.ftTransferCall {cfg : Config} {s : State} {env : Env} {receiver : AccountId}
    {amount : Nat} {memo : Option String} {msg : String} {o : Outcome}
    (hs : Inv cfg s) (h : ftTransferCall s env receiver amount memo msg = .ok o) :
    Inv cfg o.state := by
  unfold WNear.ftTransferCall at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> first
    | exact (bind_const_error h).elim
    | (obtain ⟨⟨s1, logs⟩, h1, h⟩ := bind_ok_iff.mp h
       simp only [Except.ok.injEq] at h
       subst h
       exact hs.transfer h1)

theorem Inv.resolveRefund {cfg : Config} {s : State} {sender receiver : AccountId}
    {amount unused : Nat} {o : Outcome}
    (hs : Inv cfg s) (h : resolveRefund s sender receiver amount unused = .ok o) :
    Inv cfg o.state := by
  unfold WNear.resolveRefund at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h with hu hrb hsender hover hburn <;>
    simp only [Except.ok.injEq] at h <;> subst h
  · -- refund to the sender
    obtain ⟨hrecv, hrb_eq⟩ := State.balanceOf_pos_mem hrb
    simp only
    have hle : min (s.balanceOf receiver) unused ≤ s.balanceOf receiver := Nat.min_le_left _ _
    have hwf1 : (s.setBalance receiver (s.balanceOf receiver - min (s.balanceOf receiver) unused)).WF :=
      hs.toWF.setBalance hrecv (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hrb_eq ▸ hs.balance_lt receiver))
    have hsender' : sender ∈ (s.setBalance receiver
        (s.balanceOf receiver - min (s.balanceOf receiver) unused)).registered := by
      simpa using hsender
    refine Inv.mk' (hwf1.setBalance hsender' hover) ?_ hs.usage
    have e1 := supply_setBalance_of_mem hrecv (s.balanceOf receiver - min (s.balanceOf receiver) unused)
    have e2 := supply_setBalance_of_mem hsender'
      ((s.setBalance receiver (s.balanceOf receiver - min (s.balanceOf receiver) unused)).balance sender
        + min (s.balanceOf receiver) unused)
    have hsup := hs.supply
    simp only [setBalance_totalSupply] at *
    omega
  · -- the sender unregistered meanwhile: burn
    obtain ⟨hrecv, hrb_eq⟩ := State.balanceOf_pos_mem hrb
    simp only
    have hle : min (s.balanceOf receiver) unused ≤ s.balanceOf receiver := Nat.min_le_left _ _
    have hwf1 : (s.setBalance receiver (s.balanceOf receiver - min (s.balanceOf receiver) unused)).WF :=
      hs.toWF.setBalance hrecv (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hrb_eq ▸ hs.balance_lt receiver))
    have ht : s.totalSupply - min (s.balanceOf receiver) unused < u128Bound :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs.totalSupply_lt
    refine Inv.mk' (hwf1.withTotalSupply ht) ?_ hs.usage
    have e1 := supply_setBalance_of_mem hrecv (s.balanceOf receiver - min (s.balanceOf receiver) unused)
    have hsup := hs.supply
    show (s.setBalance receiver (s.balanceOf receiver - min (s.balanceOf receiver) unused)).supply
      = s.totalSupply - min (s.balanceOf receiver) unused
    omega
  · exact hs
  · exact hs

theorem Inv.ftResolveTransfer {cfg : Config} {s : State} {env : Env} {sender receiver : AccountId}
    {amount : Nat} {o : Outcome}
    (hs : Inv cfg s) (h : ftResolveTransfer s env sender receiver amount = .ok o) :
    Inv cfg o.state := by
  unfold WNear.ftResolveTransfer at h
  simp only [bind] at h
  split at h
  · simp only [pure_eq_ok, bind_ok'] at h
    obtain ⟨unused, -, h⟩ := bind_ok_iff.mp h
    exact hs.resolveRefund h
  · simp at h

theorem Inv.storageDeposit {cfg : Config} {s : State} {env : Env} {account : Option AccountId}
    {ro : Option Bool} {o : Outcome}
    (hs : Inv cfg s) (h : storageDeposit s env account ro = .ok o) : Inv cfg o.state := by
  unfold WNear.storageDeposit at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h <;> first
    | (simp only [Except.ok.injEq] at h; subst h; exact hs)
    | (obtain ⟨s1, h1, h⟩ := bind_ok_iff.mp h
       simp only [Except.ok.injEq] at h
       subst h
       exact hs.registerAccount h1)

theorem Inv.storageWithdraw {cfg : Config} {s : State} {env : Env} {amount : Option Nat}
    {o : Outcome}
    (hs : Inv cfg s) (h : storageWithdraw s env amount = .ok o) : Inv cfg o.state := by
  unfold WNear.storageWithdraw at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h
  cases amount <;> simp only at h <;> (try split_ifs at h) <;>
    simp only [Except.ok.injEq] at h <;> subst h <;> exact hs

theorem Inv.storageUnregister {cfg : Config} {s : State} {env : Env} {force : Option Bool}
    {o : Outcome}
    (hs : Inv cfg s) (h : storageUnregister s env force = .ok o) : Inv cfg o.state := by
  unfold WNear.storageUnregister at h
  simp only [bind, bind_require, pure_eq_ok] at h
  split_ifs at h with h1 h2 h3 h4
  · simp only [Except.ok.injEq] at h
    subst h
    simp only
    have ht := hs.totalSupply_lt
    refine Inv.mk' ((hs.toWF.unregister _).withTotalSupply (by omega)) ?_ hs.usage
    have := supply_unregister_of_mem h2
    have := hs.supply
    simp only [supply_withTotalSupply]
    omega
  · simp only [Except.ok.injEq] at h; subst h; exact hs

/-- A successful `dispatch` preserves the invariant. -/
theorem Inv.dispatch {cfg : Config} {s : State} {env : Env} {call : Call} {o : Outcome}
    (hs : Inv cfg s) (h : dispatch s env call = .ok o) : Inv cfg o.state := by
  cases call <;> simp only [WNear.dispatch] at h
  · simp at h
  · exact hs.nearDeposit h
  · exact hs.nearWithdraw h
  · exact hs.ftTransfer h
  · exact hs.ftTransferCall h
  · exact hs.ftResolveTransfer h
  all_goals first
    | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h; exact hs)
    | exact hs.storageDeposit h
    | exact hs.storageWithdraw h
    | exact hs.storageUnregister h

@[blueprint "thm:inv-preserved"
  (statement := /-- \cref{spec:inv-preserved} holds. -/)]
theorem inv_preserved : InvPreserved := by
  intro cfg st env call o hcfg hinv hstep
  cases st with
  | none =>
    obtain ⟨rfl, rfl⟩ := step_none_ok hstep
    exact Inv.new hcfg
  | some s =>
    exact (hinv s rfl).dispatch (step_some_ok hstep)

end WNear
