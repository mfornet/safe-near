import Skeleton.SuccessCost
import Skeleton.StorageValueFailure

/-!
# One original-data budget for all pre-storage validation failures

The same context-only cost used for empty-base success bounds each earlier
rejection. These paths do not need empty storage, WF or proof-size assumptions.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts

private theorem initial_input_cost (ctx : Context) (raw : Storage) :
    Input.cost (successInputBefore ctx.protocol
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host =
      ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base" := by
  have hf := congrArg NearState.extCosts (applyCharges_frame
    ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw) (loadingCharges 0)
    (by simp [loadingCharges, BurnsOnly]))
  have hext : (executionActive ctx.protocol (Near.Boundary.toVMContext ctx) raw).extCosts =
      ctx.protocol.wasm.extCosts := by
    simpa only [executionActive, executionLoaded, chargeHost, VMContext.toNearState] using hf
  change Input.cost (executionActive ctx.protocol (Near.Boundary.toVMContext ctx) raw) = _
  simp only [Input.cost, hext]

/-- Input rejection consumes a shorter prefix of the same original budget. -/
theorem inputFailureCost_le_saveEmptyCost (ctx : Context) :
    inputFailureCost ctx.protocol ≤ saveEmptyCost ctx := by
  simp only [inputFailureCost, saveEmptyCost, loadingCharges, burnSum, burnCost,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.mul_zero, Nat.mul_one,
    Nat.zero_add, Nat.add_zero]
  omega

/-- Key rejection precedes both register-value reads and per-byte write fees. -/
theorem keyFailureAttemptBudget_le_saveEmptyCost (ctx : Context) (raw : Storage) (rest : Nat) :
    keyFailureAttemptBudget ctx raw rest ≤ saveEmptyCost ctx + rest := by
  have hext := storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw
  change (keyFailureBefore ctx.protocol
    (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host.extCosts =
      ctx.protocol.wasm.extCosts at hext
  rw [keyFailureAttemptBudget_eq, initial_input_cost, keyFailureCost_eq, hext]
  unfold saveEmptyCost emptyStorageCost
  dsimp only [VMContext.toNearState]
  omega

/-- Value rejection includes register-byte reads, but precedes write-byte fees. -/
theorem valueFailureAttemptBudget_le_saveEmptyCost (ctx : Context) (raw : Storage) (rest : Nat) :
    valueFailureAttemptBudget ctx raw rest ≤ saveEmptyCost ctx + rest := by
  have hext := storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw
  change (valueFailureBefore ctx.protocol
    (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host.extCosts =
      ctx.protocol.wasm.extCosts at hext
  have hreg := storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw
  rw [valueFailureAttemptBudget_eq, initial_input_cost,
    valueFailureCost_eq _ _ ctx.args hreg, hext]
  unfold saveEmptyCost emptyStorageCost
  dsimp only [VMContext.toNearState]
  omega

/-- All three pre-storage failures match the independent model under the
same context-only gas bound, for arbitrary raw and model storage. -/
theorem execOn_matches_preStorageFailure
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hfailed : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length ∨
      ctx.protocol.wasm.limits.maxLengthStorageKey < 1 ∨
      ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  by_cases hi : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length
  · exact execOn_matches_input_too_long_of_gasLimit gasBound ctx raw st hmethod hp hi
      ((inputFailureCost_le_saveEmptyCost ctx).trans hgas)
  by_cases hk : ctx.protocol.wasm.limits.maxLengthStorageKey < 1
  · apply execOn_matches_key_too_long gasBound ctx raw st 0 hmethod hp (Nat.le_of_not_gt hi) hk
    apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
    exact (keyFailureAttemptBudget_le_saveEmptyCost ctx raw 0).trans (by simpa using hgas)
  · have hv : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length := by
      rcases hfailed with h | h | h
      · exact False.elim (hi h)
      · exact False.elim (hk h)
      · exact h
    apply execOn_matches_value_too_long gasBound ctx raw st 0 hmethod hp
      (Nat.le_of_not_gt hi) (Nat.le_of_not_gt hk) hv
    apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
    exact (valueFailureAttemptBudget_le_saveEmptyCost ctx raw 0).trans (by simpa using hgas)

end WNear.Skeleton
