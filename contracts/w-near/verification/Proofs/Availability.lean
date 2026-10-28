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
  simp only [bind, bind_require, bind_ok', pure_eq_ok, hpos, ite_true]
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

@[blueprint "thm:withdraw-available-boundary"
  (statement := /-- \cref{spec:withdraw-available-boundary} holds. -/)]
theorem withdraw_available_at_boundary : WithdrawAvailableAtBoundary := by
  intro cfg s ctx amount a s' hs hreg hamt hdep hbound hbal hrent hlog hreceipts
  have h := withdraw_available cfg s (Env.ofContext ctx) amount hs hreg hamt hdep hbound
  rw [step_nearWithdraw] at h
  unfold contractStep
  rw [step_nearWithdraw, h]
  dsimp only [stepLogs]
  split
  · rename_i hsome
    exact absurd (hsome.symm.trans hlog) (by simp)
  split
  · rename_i hlt
    change ctx.balance + ctx.attached < amount + 1 at hlt
    rw [hdep] at hlt
    exact absurd hlt (Nat.not_lt.mpr (Nat.add_le_add_right hbal 1))
  · split
    · rename_i hsome
      exact absurd (hsome.symm.trans hreceipts) (by simp)
    split
    · rename_i hpos
      change 0 < NearInterface.stakeDeficit ctx.protocol (usageAfter ctx (some s) s')
        (ctx.balance + ctx.attached - (amount + 1)) ctx.locked at hpos
      rw [hdep, Nat.add_sub_add_right, hrent] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    · rfl

@[blueprint "thm:deposit-available-boundary"
  (statement := /-- \cref{spec:deposit-available-boundary} holds. -/)]
theorem deposit_available_at_boundary : DepositAvailableAtBoundary := by
  intro cfg s ctx env hs hpos hbound hcond
  obtain ⟨o, h, hmem, hbal, hprom⟩ := deposit_available cfg s env hs hpos hbound hcond
  rw [step_nearDeposit] at h
  refine ⟨o, by rw [step_nearDeposit]; exact h, hmem, hbal, hprom, ?_⟩
  intro deficit hlog
  unfold contractStep
  rw [step_nearDeposit, h]
  have hout : Outcome.nearOut o = 0 := by simp [Outcome.nearOut, hprom]
  dsimp only [stepLogs]
  split
  · rename_i hsome
    exact absurd (hsome.symm.trans hlog) (by simp)
  simp only [hout, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, hprom]
  rfl

open NearInterface in
/-- What `Refines` buys: on a runtime and protocol configuration the binary
refines the model in, a withdrawal attached with at least the model's gas bound, and with room for
the model's storage-proof bound, succeeds on the binary,
returns the payout receipt and stores the model's new state. -/
@[blueprint "thm:withdraw-available-binary"
  (statement := /-- If a binary refines \cref{def:contract-model}, then under the hypotheses of \cref{spec:withdraw-available-boundary}, for arguments that are the call \texttt{near\_withdraw}$(a)$ and at least the model's gas bound attached, the binary's execution returns receipt index 0 and its storage encodes the resulting state. -/)]
theorem withdraw_available_binary {R : RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
    {code : R.Code} {cfg : Config}
    (href : Refines R protocol code (wnear cfg)) {s : State} {ctx : Context} {amount : Nat}
    (hs : Inv cfg s) (hwf : ctx.WF (encode s)) (hprot : ctx.protocol = protocol)
    (hparse : Parses ctx.method ctx.args (.nearWithdraw amount))
    (hreg : AccountId.ofNear ctx.predecessor ∈ s.registered)
    (hamt : amount ≤ s.balance (AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
    (hbound : amount + 1 < u128Bound) (hbal : amount ≤ ctx.balance)
    (hrent : stakeDeficit ctx.protocol (usageAfter ctx (some s)
      { s.setBalance (AccountId.ofNear ctx.predecessor)
          (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
        totalSupply := s.totalSupply - amount }) (ctx.balance - amount) ctx.locked = 0)
    (hlog : logLimitError ctx.protocol
      [s!"Withdraw {amount} NEAR from {AccountId.ofNear ctx.predecessor}"] = none)
    (hreceipts : ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
      (encodeReceipts [.transfer (AccountId.ofNear ctx.predecessor) (amount + 1)]) = none)
    (hgas : gasBound ctx (.nearWithdraw amount) ≤ ctx.gasLimit)
    (hproof : ctx.ProofRoom (proofBound ctx)) :
    (R.exec code (encode s) ctx).outcome = .ok (.receiptIndex 0) ∧
      (R.exec code (encode s) ctx).storage =
        encode { s.setBalance (AccountId.ofNear ctx.predecessor)
            (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
          totalSupply := s.totalSupply - amount } := by
  have hrep : (wnear cfg).Represents (encode s) (some s) := ⟨hs, rfl⟩
  have hm := href.transfer (c := (Call.nearWithdraw amount : Call)) hrep hwf hprot hparse hgas hproof
  change Matches (wnear cfg) ctx (encode s) _ (contractStep ctx (some s) (.nearWithdraw amount)) at hm
  rw [withdraw_available_at_boundary cfg s ctx amount hs hreg hamt hdep hbound hbal hrent hlog hreceipts] at hm
  exact ⟨hm.1, hm.2.1⟩

end WNear
