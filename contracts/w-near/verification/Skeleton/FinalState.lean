import Skeleton.Execution
import NearVM.StorageRepresentation

/-!
# Functional state after logging and returning

The method's output suffix preserves the storage call's functional effects.
Only billing, synchronized used gas, the log append and return selection change.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

private def outputView (host : NearState) :=
  (host.storage, host.storageKeys, host.context.storageUsage, host.context.accountBalance,
    host.lastError, host.lastExecutionIssue)

private theorem chargedStore_view (store : Store NearState) (cost : Nat) :
    outputView (chargedStore store cost).host = outputView store.host := rfl

private theorem chargedMany_view (store : Store NearState) (cost count : Nat) :
    outputView (chargedMany store cost count).host = outputView store.host := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih => simpa only [chargedMany, chargedStore_view] using
      (ih (chargedStore store cost))

private theorem inputBefore_view (cfg : WasmConfig) (store : Store NearState) :
    outputView (inputBefore cfg store moduleInstance).host = outputView store.host := rfl

private theorem saved_burnsOnly : ∀ c ∈ savedCharges, MeteredHosts.BurnsOnly c := by
  simp only [savedCharges, extCharges, List.mem_map]
  rintro _ ⟨_, _, rfl⟩
  trivial

private theorem saved_view (before : HostStore NearState) :
    outputView (savedAfter before).host = outputView before.host := by
  have h := congrArg outputView (MeteredHosts.applyCharges_frame before.host savedCharges saved_burnsOnly)
  exact h

private theorem returned_view (cfg : WasmConfig) (store : Store NearState) (bytes : List UInt8) :
    outputView (returnedAfter cfg store bytes).host = outputView store.host := by
  have h := congrArg outputView (MeteredHosts.applyCharges_frame
    (inputBefore cfg store moduleInstance).host (returnCharges cfg store)
    (MeteredHosts.Output.valueReturn_burnsOnly (inputBefore cfg store moduleInstance) u64Max 0))
  exact h

/-- Every functional field outside the output suffix's stated effects is
retained from storage's local post-state. No whole-method execution is assumed. -/
private theorem executionFinal_view (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    outputView (executionFinal cfg ctx raw storage).host = outputView storage.host := by
  simp only [executionFinal, HostResults.finalStore, commitCall_host,
    successResults_returned, successResults_beforeReturn, returned_view,
    successReturnBefore, chargedMany_view, successLogAfter, saved_view, inputBefore_view,
    successLogBefore, chargedStore_view]

theorem executionFinal_storage (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.storage = storage.host.storage := by
  have h := congrArg (fun fields => fields.1) (executionFinal_view cfg ctx raw storage)
  exact h

theorem executionFinal_storageKeys (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.storageKeys = storage.host.storageKeys := by
  have h := congrArg (fun fields => fields.2.1) (executionFinal_view cfg ctx raw storage)
  exact h

theorem executionFinal_usage (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.context.storageUsage = storage.host.context.storageUsage := by
  have h := congrArg (fun fields => fields.2.2.1) (executionFinal_view cfg ctx raw storage)
  exact h

theorem executionFinal_balance (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.context.accountBalance = storage.host.context.accountBalance := by
  have h := congrArg (fun fields => fields.2.2.2.1) (executionFinal_view cfg ctx raw storage)
  exact h

/-- The output suffix preserves the storage call's structured issue markers. -/
theorem executionFinal_issues (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.lastError = storage.host.lastError ∧
    (executionFinal cfg ctx raw storage).host.lastExecutionIssue = storage.host.lastExecutionIssue := by
  have h := congrArg (fun fields => fields.2.2.2.2) (executionFinal_view cfg ctx raw storage)
  exact Prod.mk.inj h

theorem executionFinal_returnData (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.returnData = some ctx.input := by
  simp only [executionFinal, HostResults.finalStore, commitCall_host,
    successResults_returned, successResults_beforeReturn]
  change some (executionActive cfg ctx raw).context.input = some ctx.input
  rw [executionActive_input]

/-- Storage representation survives the complete output suffix. -/
theorem executionFinal_represents (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState)
    (updated : NearInterface.RawStorage) (h : StorageRepresentation.Represents storage.host updated) :
    StorageRepresentation.Represents (executionFinal cfg ctx raw storage).host updated := by
  constructor
  · intro key value
    rw [executionFinal_storage]
    exact h.lookup key value
  · intro key value hv
    rw [executionFinal_storageKeys]
    exact h.coverage key value hv

private theorem chargedMany_logs (store : Store NearState) (cost count : Nat) :
    (chargedMany store cost count).host.logs = store.host.logs := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih => exact ih (chargedStore store cost)

private theorem saved_logs (before : HostStore NearState) :
    (savedAfter before).host.logs = before.host.logs ++ ["saved".toUTF8.toList] := by
  have h := congrArg NearState.logs
    (MeteredHosts.applyCharges_frame before.host savedCharges saved_burnsOnly)
  exact congrArg (fun logs => logs ++ ["saved".toUTF8.toList]) h

private theorem returned_logs (cfg : WasmConfig) (store : Store NearState) (bytes : List UInt8) :
    (returnedAfter cfg store bytes).host.logs = store.host.logs := by
  have h := congrArg NearState.logs (MeteredHosts.applyCharges_frame
    (inputBefore cfg store moduleInstance).host (returnCharges cfg store)
    (MeteredHosts.Output.valueReturn_burnsOnly (inputBefore cfg store moduleInstance) u64Max 0))
  exact h

/-- The output suffix appends exactly its fixed log to storage's earlier logs. -/
theorem executionFinal_logs (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState) :
    (executionFinal cfg ctx raw storage).host.logs = storage.host.logs ++ ["saved".toUTF8.toList] := by
  simp only [executionFinal, HostResults.finalStore, commitCall_host,
    successResults_returned, successResults_beforeReturn, returned_logs,
    successReturnBefore, chargedMany_logs, successLogAfter, saved_logs,
    inputBefore, chargedStore, chargeHost, successLogBefore]

theorem distributeGas_no_handles (unused : Nat) (weights : List (Nat × Nat × Nat))
    (receipts : List ReceiptSpec) : distributeGas unused [] weights receipts = (receipts, 0) := by
  unfold distributeGas
  dsimp only
  split
  · rfl
  · have step : distributeStep unused (gasWeightTotal weights) weights [] =
        (fun acc _ => acc) := by
      funext acc entry
      simp [distributeStep]
    rw [step]
    have fold (entries : List ((Nat × Nat × Nat) × Nat)) :
        entries.foldl (fun acc _ => acc) (receipts, 0) = (receipts, 0) := by
      induction entries with
      | nil => rfl
      | cons entry rest ih => exact ih
    exact fold _

/-- The normal VM result has exactly the storage effects, the returned input
and the appended log. Its promise conversion and gas distribution are empty. -/
theorem executionOutcome_fields (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (storage : HostStore NearState)
    (updated : NearInterface.RawStorage)
    (hrep : StorageRepresentation.Represents storage.host updated)
    (hpromises : storage.host.promises = []) (hlogs : storage.host.logs = []) :
    let outcome := outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none
    outcome.aborted = none ∧ outcome.returnData = .value ctx.input ∧
    outcome.storage.toFinset = updated ∧
    outcome.storageUsage = storage.host.context.storageUsage.toNat ∧
    outcome.balance = storage.host.context.accountBalance ∧ outcome.logs = ["saved"] ∧
    outcome.receipts = [] ∧ outcome.distributedGas = 0 := by
  have hp := (executionFinal_promises cfg ctx raw storage).trans hpromises
  have hs := (executionFinal_represents cfg ctx raw storage updated hrep).finalStorage
  have hl := executionFinal_logs cfg ctx raw storage
  rw [hlogs] at hl
  simp only [List.nil_append] at hl
  have hlo : logsOf (executionFinal cfg ctx raw storage).host = ["saved"] := by
    rw [logsOf, hl]
    decide +kernel
  simp only [outcomeOfExecution, StepResult.host, hp, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?, executionFinal_returnedPromise, executionFinal_returnData,
    distributeGas_no_handles, hs, executionFinal_usage, executionFinal_balance, hlo, and_self]

end WNear.Skeleton
