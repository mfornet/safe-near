import Bridge.Methods.FtTotalSupplyModel

/-!
# `new` (290): the model's side

The model's step for `new` in its three cases, as the binary takes them (deposit check first,
then `state_exists`):

* `step_new_deposit`: a deposit fails with `depositNotAccepted "new"` ("Method new doesn't accept
  deposit"), whatever the state;
* `step_new_some`: no deposit and a state: `alreadyInitialized` ("The contract has already been
  initialized");
* `step_new_none`: no deposit and no state: the state `new cfg` (no accounts, supply 0, the
  measured account usage), unit, no logs, no promises, unless the account cannot pay for its
  storage.

`encode_new`: the storage of `new cfg` is the one `STATE` record; `newHeader`: its bytes;
`usageOf_new`: its usage, `5 + 29 + extra`.
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near NearInterface ContractModel

/-- The model's `new` state under the protocol `p`. -/
def newState (p : Wasm.Near.RuntimeConfig) : WNear.State := (WNear.new (WNear.Config.ofRuntime p)).state

/-- What the stake check sees after `new`. -/
def deficitNew (ctx : Context) : Nat :=
  stakeDeficit ctx.protocol (WNear.usageAfter ctx none (newState ctx.protocol)) (ctx.balance + ctx.attached)
    ctx.locked

theorem step_new_deposit (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) (hd : ctx.attached ≠ 0) :
    (WNear.wnear cfg).step ctx st .new =
      .error { failure := .panic (.depositNotAccepted "new"), logs := [] } := by
  show WNear.contractStep ctx st .new = _
  have h : ¬ (ctx.attached = 0) := hd
  cases st <;>
  simp [WNear.contractStep, WNear.step, WNear.Env.ofContext, WNear.Call.isPrivate, WNear.Call.isPayable,
    WNear.Call.isView, WNear.Call.methodName, WNear.require, h, WNear.stepLogs, NearInterface.logLimitError] <;> rfl

theorem step_new_some (cfg : WNear.Config) (ctx : Context) (S : WNear.State) (hd : ctx.attached = 0) :
    (WNear.wnear cfg).step ctx (some S) .new =
      .error { failure := .panic .alreadyInitialized, logs := [] } := by
  show WNear.contractStep ctx (some S) .new = _
  simp [WNear.contractStep, WNear.step, WNear.Env.ofContext, WNear.Call.isPrivate, WNear.Call.isPayable,
    WNear.Call.isView, WNear.require, hd, WNear.stepLogs, NearInterface.logLimitError]
  rfl

theorem step_new_none (cfg : WNear.Config) (ctx : Context) (hd : ctx.attached = 0) :
    (WNear.wnear cfg).step ctx none .new =
      if 0 < deficitNew ctx then .error { failure := .lackBalanceForState (deficitNew ctx), logs := [] }
      else .ok { state := newState ctx.protocol, ret := .unit, logs := [], promises := [] } := by
  show WNear.contractStep ctx none .new = _
  simp [WNear.contractStep, WNear.step, WNear.Env.ofContext, WNear.Call.isPrivate, WNear.Call.isPayable,
    WNear.Call.isView, WNear.require, hd, WNear.stepLogs, NearInterface.logLimitError, WNear.Outcome.nearOut, WNear.encodeReceipts, deficitNew, newState]
  rfl

/-! ## The storage of `new` -/

theorem encode_new (p : Wasm.Near.RuntimeConfig) :
    WNear.encode (newState p) = {(WNear.stateKey, WNear.header (newState p))} := by
  simp [WNear.encode, newState, WNear.new]

theorem stateKey_length : WNear.stateKey.length = 5 := by rw [← StateRead.stateKey_eq]; rfl

theorem usageOf_new (p : Wasm.Near.RuntimeConfig) :
    storageUsageOf p (WNear.encode (newState p)) = 34 + p.fees.numExtraBytesRecord := by
  rw [encode_new]
  simp [storageUsageOf, recordBytes, stateKey_length, StateReadModel.header_length]

/-- **`AgreesWith` for `new`** on no state, no deposit, from a final host with the storage of
`new`, the usage grown by its one record, the balance unchanged, no logs and no return value. -/
theorem agrees_new (cfg : WNear.Config) (ctx : Context) (e : NearState) (hd : ctx.attached = 0)
    (hsto : (finalStorage e).toFinset = WNear.encode (newState ctx.protocol))
    (hus : e.context.storageUsage.toNat = ctx.storageUsage + (34 + ctx.protocol.fees.numExtraBytesRecord))
    (hbal : e.context.accountBalance = ctx.balance + ctx.attached)
    (hlogs : e.logs = []) (hret : e.returnData = none) :
    AgreesWith (WNear.wnear cfg) ctx ∅ e ((WNear.wnear cfg).step ctx none .new) := by
  have hafter : WNear.usageAfter ctx none (newState ctx.protocol) = e.context.storageUsage.toNat := by
    simp only [WNear.usageAfter, WNear.storageOf, storageUsageOf, Finset.sum_empty, Nat.sub_zero]
    rw [show (∑ record ∈ WNear.encode (newState ctx.protocol), recordBytes ctx.protocol record) =
      storageUsageOf ctx.protocol (WNear.encode (newState ctx.protocol)) from rfl, usageOf_new, hus]
  have hdef : deficitNew ctx =
      stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked := by
    rw [deficitNew, hafter, hbal]
  rw [step_new_none cfg ctx hd]
  split
  · rename_i hpos
    refine ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, ?_⟩
    show [] = logsOf e
    simp [logsOf, hlogs]
  · rename_i hpos
    refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, hsto, hbal, ?_, ?_⟩
    · show returnOf e = .none
      simp [returnOf, hret]
    · show e.context.storageUsage.toNat = ctx.storageUsage - storageUsageOf ctx.protocol ∅ +
        storageUsageOf ctx.protocol (WNear.encode (newState ctx.protocol))
      rw [usageOf_new, hus]
      simp [storageUsageOf]
    · show logsOf e = []
      simp [logsOf, hlogs]

end WNear.Binary.NewMethod
