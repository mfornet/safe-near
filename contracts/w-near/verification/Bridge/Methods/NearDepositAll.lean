import Bridge.Methods.NearDepositBound

/-!
# `near_deposit` refines the model on every represented state

The initialized case now has its gas bound discharged. The uninitialized case
uses the previously proved not-initialized panic. Only the protocol parameters
and binary-size premises remain for the final configuration pinning step.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near NearLogic NearInterface
open WNear.Binary.FtTotalSupplyMethod (CostsV86 LimitsV86)
open WNear.Binary.NearDepositGas (CostsDepositV86)

theorem nearDeposit_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (s : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hrep : (WNear.wnear cfg).Represents raw (some s)) (hm : ctx.method = "near_deposit")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hd : CostsDepositV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some s) .nearDeposit
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some s) .nearDeposit ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some s) .nearDeposit) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some s) .nearDeposit) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨_, hraw⟩ := (show WNear.Inv cfg s ∧ raw = WNear.encode s from hrep)
  exact nearDeposit_refines_init_of_bound cfg size codeOf raw ctx s hp hwf hrep hm hc hl
    hd.storageValue hd.logCount hd.usageRoom
    (NearDepositGas.hbound_initialized cfg ctx raw s hwf hraw size hc hd hsize)

/-- Every per-call refinement clause of initialized and uninitialized `near_deposit`. -/
theorem nearDeposit_refines_all (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "near_deposit") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hd : CostsDepositV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .nearDeposit
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .nearDeposit ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .nearDeposit) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .nearDeposit) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  cases st with
  | none => exact nearDeposit_refines_uninit cfg size codeOf raw ctx hp hwf hrep hm hc hl hsize
  | some s => exact nearDeposit_refines_init cfg size codeOf raw ctx s hp hwf hrep hm hc hl hd hsize

end WNear.Binary.NearDepositMethod
