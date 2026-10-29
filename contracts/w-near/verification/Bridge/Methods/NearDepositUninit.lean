import Bridge.Methods.NearDepositRuns
import Bridge.Methods.StorageBalanceBoundsUninit

/-!
# `near_deposit` (234) on an uninitialized contract refines the model

With no `STATE`, 234 panics as `ft_total_supply` does ("The contract is not initialized",
`dep_panics_none`); the model's step is that panic (`step_none`), and the gas bound covers the path
(`hbound_none`).
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near NearLogic NearInterface ContractModel
open WNear.Binary.FtTotalSupplyMethod (preNone postNone notInitMsg preNone_of_ctx postNone_panicHost postNone_logs
  hostOf_storage_empty CostsV86 LimitsV86 trie_le)
open WNear.Binary.FtTotalSupply (ReadNone)
open WNear.Binary.DepositBody234 (cost234None)

theorem step_none (cfg : WNear.Config) (ctx : Context) :
    (WNear.wnear cfg).step ctx none .nearDeposit = .error { failure := .panic .notInitialized, logs := [] } := by
  rfl

theorem agreesPanic_none (cfg : WNear.Config) (ctx : Context) (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none .nearDeposit) :=
  ⟨_, step_none cfg ctx, rfl, hl.symm⟩

/-- The model's gas bound for `near_deposit`: compute, the trie nodes, no return data. -/
theorem gas_234 (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) :
    (WNear.wnear cfg).gas ctx st .nearDeposit = WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 0 := by
  show WNear.gasBound ctx .nearDeposit = _
  simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
    WNear.Call.resultBytes, WNear.Call.returnBytes]
  simp

/-- **The model's gas bound covers loading and the uninitialized path.** -/
theorem hbound_none (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hval : (hostOf ctx raw).storage WNear.stateKey = none) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costNoneDep ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .nearDeposit := by
  have htrie := trie_le ctx raw
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hv : (erase (hostOf ctx raw)).storage StateRead.stateKey = none := by
    rw [StateRead.stateKey_eq]; exact hval
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [gas_234, hl]
  have hrn := readNodes_of_false (h := erase (hostOf ctx raw)) rfl
  simp only [costNoneDep, cost234None, storageReadUse, storageReadPhaseUse, hv, hrn, Nat.zero_mul, Nat.zero_add,
    Option.map_none, Option.getD_none, panicUtf8Use, panicUtf8Charges, storageReadBeforeCharges, chargesUse,
    chargeUse, List.map, List.sum_cons, List.sum_nil, hx'] at htrie ⊢
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.storageReadBase; have := hc.storageReadKeyByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  omega

/-- **`near_deposit` refines the model on an uninitialized contract.** -/
theorem nearDeposit_refines_uninit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "near_deposit")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .nearDeposit
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .nearDeposit ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .nearDeposit) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none .nearDeposit) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hval : (hostOf ctx ∅).storage WNear.stateKey = none := hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := preNone_of_ctx cfg ctx ∅ none hwf hl hc hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf ∅ none ctx .nearDeposit preNone
    (costNoneDep ctx.protocol) postNone notInitMsg hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_234)
    funcType_234 (by decide) (by decide) (dep_panics_none ctx.protocol) hpre hpreP
    (fun e he => postNone_panicHost rfl he) (fun e he => postNone_panicHost rfl he)
    (fun e he => agreesPanic_none cfg ctx e (postNone_logs rfl he))
    (fun e he => agreesPanic_none cfg ctx e (postNone_logs rfl he))
    (hbound_none cfg ctx ∅ none size hval hc hsize)

end WNear.Binary.NearDepositMethod
