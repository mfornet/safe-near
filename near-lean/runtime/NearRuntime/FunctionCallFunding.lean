import NearRuntime.PromiseGasInvariants

namespace Near
open Wasm Wasm.Near

/-- Commit funding with the outgoing gas obligation derived from concrete
strict-policy execution, rather than supplied as an outcome equation. -/
theorem commitFunctionCall_funded_gas (exec : Exec) (c : ReceiptCtx) (account : Account)
    (code : ContractCode) (method : String) (args : Bytes) (gas deposit : Nat) (isLast : Bool) (effects : FunctionCallEffects)
    (hwf : exec.state.AccountsUnique) (haccount : exec.state.account? c.receipt.receiverId = some account)
    (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hsuccess : (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast exec.storageAccounting)
      (exec.state.contractStorage c.receipt.receiverId)).aborted = none)
    (heffects : functionCallEffects c account
      (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast exec.storageAccounting)
        (exec.state.contractStorage c.receipt.receiverId)) isLast exec.state = .ok effects) :
    let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast exec.storageAccounting)
      (exec.state.contractStorage c.receipt.receiverId)
    (exec.commitFunctionCall outcome effects).totalFunds c.cfg =
      exec.totalFunds c.cfg + deposit + outcome.subsidizedAmount +
        (outcome.usedGas - outcome.burntGas) * c.action.gasPrice := by
  have hf := commitFunctionCall_funded exec c account code method args gas deposit isLast effects exec.storageAccounting hwf haccount hsuccess heffects
  have hg := run_functionCallGasFunds c code.module code.size method
    (functionCallContext c account args gas deposit isLast exec.storageAccounting) (exec.state.contractStorage c.receipt.receiverId)
    defaultFuel hreceiver hsuccess rfl
  dsimp only at hf ⊢
  rw [hg] at hf
  exact hf

/-- Additive conservation at an action boundary. Gas used purchases both burn
and onward receipt obligations; subsidy is an explicit external source. The
cross terms let consecutive steps compose without truncated subtraction. -/
def Exec.FundingStep (cfg : RuntimeConfig) (price deposit : Nat) (before after : Exec) : Prop :=
  after.totalFunds cfg + before.subsidizedAmount + after.gasBurnt * price + before.gasUsed * price =
    before.totalFunds cfg + deposit + after.subsidizedAmount + before.gasBurnt * price + after.gasUsed * price

/-- Consecutive funded actions telescope without assuming either intermediate
state has zero gas, no prior receipts, or zero subsidy. -/
theorem Exec.FundingStep.trans {cfg : RuntimeConfig} {price firstDeposit secondDeposit : Nat}
    {before middle after : Exec}
    (hfirst : Exec.FundingStep cfg price firstDeposit before middle)
    (hsecond : Exec.FundingStep cfg price secondDeposit middle after) :
    Exec.FundingStep cfg price (firstDeposit + secondDeposit) before after := by
  unfold Exec.FundingStep at *
  omega

/-- Actual successful function-call execution conserves deposits, explicit
subsidy and gas-purchased outgoing funds at the compositional action boundary.
Account uniqueness and the ordinary-receiver condition are structural premises;
no VM result, gas equality or financial equation is assumed. -/
theorem applyFunctionCall_success_funding_step (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (before after : Exec)
    (hwf : before.state.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hrun : (applyFunctionCall c method args gas deposit isLast).run.run before = (.ok (), after)) :
    Exec.FundingStep c.cfg c.action.gasPrice deposit before after := by
  obtain ⟨account, code, effects, _, _, hsuccess, _, heq, hf⟩ :=
    applyFunctionCall_success_funded c method args gas deposit isLast before after hwf hrun
  let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast before.storageAccounting)
    (before.state.contractStorage c.receipt.receiverId)
  have hg := run_functionCallGasFunds c code.module code.size method
    (functionCallContext c account args gas deposit isLast before.storageAccounting) (before.state.contractStorage c.receipt.receiverId)
    defaultFuel hreceiver hsuccess rfl
  change functionCallGasFunds c outcome = (outcome.usedGas - outcome.burntGas) * c.action.gasPrice at hg
  change after.totalFunds c.cfg + before.subsidizedAmount = before.totalFunds c.cfg + deposit +
    after.subsidizedAmount + functionCallGasFunds c outcome at hf
  rw [hg] at hf
  have hburn : after.gasBurnt = before.gasBurnt + outcome.burntGas := by rw [heq]; rfl
  have hused : after.gasUsed = before.gasUsed + outcome.burntGas + (outcome.usedGas - outcome.burntGas) := by rw [heq]; rfl
  unfold Exec.FundingStep
  rw [hburn, hused]
  simp only [Nat.add_mul]
  omega

end Near
