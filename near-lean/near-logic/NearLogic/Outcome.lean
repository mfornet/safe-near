import NearVM.Run

/-!
# The outcome of a run that creates no promises

`outcomeOfExecution` for a run that finished with values, created no
promises and selected no promise as its result: no receipts, the selected
bytes (or nothing) as return data, and `used` gas as the counter has it.
`checkReceipts` leaves such an outcome alone.
-/

namespace NearLogic

open Wasm Wasm.Near

theorem outcomeOfExecution_noPromises (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (vs : List Value) (s : Store NearState) (hp : s.host.promises = [])
    (hr : s.host.returnedPromise = none) (hw : s.host.gasWeights = []) :
    let o := outcomeOfExecution ctx storage (.done vs s) none
    o.aborted = none ∧ o.receipts = [] ∧
      o.returnData = (match s.host.returnData with | some b => .value b | none => .none) ∧
      o.usedGas = s.host.gas.used ∧ o.burntGas = s.host.gas.burnt ∧ o.distributedGas = 0 ∧
      o.balance = s.host.context.accountBalance ∧ o.storageUsage = s.host.context.storageUsage.toNat ∧
      o.logs = logsOf s.host ∧ o.storage = finalStorage s.host := by
  simp [outcomeOfExecution, StepResult.host, hp, hr, hw, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?]
  split <;> rename_i heq <;> simp [heq]

theorem checkReceipts_noReceipts (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) (h : o.receipts = [])
    (hr : ∀ i, o.returnData ≠ .receiptIndex i) : o.checkReceipts balance usage storage = o := by
  unfold VMOutcome.checkReceipts VMOutcome.receiptsValid
  rw [h]
  cases hd : o.returnData with
  | receiptIndex i => exact absurd hd (hr i)
  | _ => simp [receiptsValidFrom]

end NearLogic
