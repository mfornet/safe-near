import Skeleton.SuccessObservation
import Skeleton.FailureExecution

/-!
# Successful body contracts through the public VM and receipt boundary

Preparation, host resources and budget credits are local premises. The runtime
outcome is derived from the fifteen-instruction proof, never assumed.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface

set_option maxHeartbeats 600000

/-- Local success resources after loading/activation and at storage's output.
The loading, activation and body budget remain explicit in executionBudget. -/
structure SaveResources (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64) : Prop where
  inputLimit : withinLimit (ctx.toNearState cfg raw).config.maxRegisterLen ctx.input.length = true
  memory : storage.mem = preparedData cfg
  register : storage.host.registers 0 = some ctx.input
  returnLimit : withinLimit storage.host.config.maxReturnLen ctx.input.length = true
  logCount : logCountError storage = none
  logSpace : 5 ≤ Wasm.Near.logSpace storage
  readCost : storage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64
  logPush : ∀ limit, storage.host.config.maxLogLen = some limit → totalLogLength storage + 5 ≤ limit
  credits : (ctx.toNearState cfg raw).gas.Credits
    (executionBudget cfg ctx raw storage storageCost rest)
  storageCall : StorageFrontier cfg (executionStore cfg ctx raw) storage storageCost rest written

/-- No finite-fuel premise survives at the actual default-fuel VM entry. -/
theorem runAttempt_save_default (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hprepare : PreparationLimits cfg)
    (h : SaveResources cfg ctx raw storage storageCost rest written) :
    runAttempt cfg module 0 "save" ctx raw (fuelFor cfg module ctx) =
      outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none :=
  runAttempt_save_success cfg ctx raw storage storageCost rest written _
    hprepare.positive hprepare.minmax hprepare.maximum hprepare.types hprepare.functions
    (fuelFor_save cfg ctx) h.inputLimit h.memory h.register h.returnLimit h.logCount
    h.logSpace h.readCost h.logPush h.credits h.storageCall

/-- Empty promise conversion yields a valid receipt graph at normal return. -/
theorem executionOutcome_receiptsValid (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (hpromises : storage.host.promises = []) :
    (outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none).receiptsValid = true := by
  have hp := (executionFinal_promises cfg ctx raw storage).trans hpromises
  simp only [outcomeOfExecution, StepResult.host, hp, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?, executionFinal_returnedPromise, executionFinal_returnData,
    distributeGas_no_handles, VMOutcome.receiptsValid, receiptsValidFrom]
  rfl

/-- The public runner's receipt validation retains the derived normal outcome. -/
theorem run_save_success_public (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hprepare : PreparationLimits cfg)
    (h : SaveResources cfg ctx raw storage storageCost rest written)
    (hpromises : storage.host.promises = []) :
    run cfg module 0 "save" ctx raw =
      outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none := by
  simp only [run, runAttempt_save_default cfg ctx raw storage storageCost rest written hprepare h,
    VMOutcome.checkReceipts, executionOutcome_receiptsValid cfg ctx raw storage hpromises, ↓reduceIte]

/-- The actual public execution matches the successful model-shaped result.
The local storage state is explicitly related to the chosen represented state;
modelStep's resource decisions are handled separately below. -/
theorem execOn_matches_save_success
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw state : Storage) (storage : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (h : SaveResources ctx.protocol (Near.Boundary.toVMContext ctx) raw storage storageCost rest written)
    (hrep : StorageRepresentation.Represents storage.host (savedStorage state ctx.args).toFinset)
    (hpromises : storage.host.promises = []) (hlogs : storage.host.logs = [])
    (hbalance : storage.host.context.accountBalance = ctx.balance + ctx.attached)
    (husage : storage.host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage state ctx.args).toFinset)
    (hstake : stakeDeficit ctx.protocol storage.host.context.storageUsage.toNat
      storage.host.context.accountBalance ctx.locked = 0) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      (.ok { state := savedStorage state ctx.args, ret := ctx.args, logs := ["saved"], promises := [] }) := by
  have hr := run_save_success_public ctx.protocol (Near.Boundary.toVMContext ctx) raw storage
    storageCost rest written hprepare h hpromises
  have hf := executionOutcome_fields ctx.protocol (Near.Boundary.toVMContext ctx) raw storage
    _ hrep hpromises hlogs
  have hreceipts := hf.2.2.2.2.2.2.1
  unfold Near.Boundary.execOn
  simp only [code]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw
      (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  simp only [hreceipts, Near.Boundary.actionsIssue?, List.findSome?_nil]
  simp only [Near.checkVMReceipts, List.zipIdx_nil, List.forIn_nil, pure, Except.pure]
  exact executionOutcome_matches_success gasBound ctx raw state storage hrep hpromises hlogs hbalance husage hstake

/-- Original protocol bounds checked by the independent model's success path. -/
structure ModelSaveLimits (ctx : Context) : Prop where
  input : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize
  key : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey
  value : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue
  logs : 0 < ctx.protocol.wasm.limits.maxNumberLogs
  logBytes : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength
  returned : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData

/-- Model success is proved from its own checks, without executing any Wasm. -/
theorem modelStep_save_success (ctx : Context) (st : Option Storage)
    (h : ModelSaveLimits ctx)
    (hstake : stakeDeficit ctx.protocol
      (ctx.storageUsage - storageUsageOf ctx.protocol (st.getD []).toFinset +
        storageUsageOf ctx.protocol (savedStorage (st.getD []) ctx.args).toFinset)
      (ctx.balance + ctx.attached) ctx.locked = 0) :
    modelStep ctx st () = .ok {
      state := savedStorage (st.getD []) ctx.args
      ret := ctx.args
      logs := ["saved"]
      promises := [] } := by
  have hz : ctx.protocol.wasm.limits.maxNumberLogs ≠ 0 := Nat.ne_of_gt h.logs
  simp [modelStep, Nat.not_lt.mpr h.input, Nat.not_lt.mpr h.key,
    Nat.not_lt.mpr h.value, hz, Nat.not_lt.mpr h.logBytes, Nat.not_lt.mpr h.returned, hstake]

/-- Representation fixes the original finite records used in the model's
usage calculation, including the absent-state case. -/
theorem represented_storage_getD
    (gasBound : Context → Option Storage → Unit → Nat) (raw : Storage) (st : Option Storage)
    (h : (model gasBound).Represents raw.toFinset st) :
    (st.getD []).toFinset = raw.toFinset := by
  cases st with
  | none => exact h.symm
  | some state => exact h.2.symm

/-- One actual success branch of refinement: the executed receipt matches the
independent modelStep for the explicitly represented original state. Arbitrary
recorded-proof, storage and gas behavior is not assumed away: the local storage
frontier must still establish that this particular write succeeds. -/
theorem execOn_matches_save_modelStep
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (storage : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (h : SaveResources ctx.protocol (Near.Boundary.toVMContext ctx) raw storage storageCost rest written)
    (hmodel : ModelSaveLimits ctx)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hrep : StorageRepresentation.Represents storage.host (savedStorage (st.getD []) ctx.args).toFinset)
    (hpromises : storage.host.promises = []) (hlogs : storage.host.logs = [])
    (hbalance : storage.host.context.accountBalance = ctx.balance + ctx.attached)
    (husage : storage.host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage (st.getD []) ctx.args).toFinset)
    (hstake : stakeDeficit ctx.protocol storage.host.context.storageUsage.toNat
      storage.host.context.accountBalance ctx.locked = 0) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hraw := represented_storage_getD gasBound raw st hrepresented
  have hmstake : stakeDeficit ctx.protocol
      (ctx.storageUsage - storageUsageOf ctx.protocol (st.getD []).toFinset +
        storageUsageOf ctx.protocol (savedStorage (st.getD []) ctx.args).toFinset)
      (ctx.balance + ctx.attached) ctx.locked = 0 := by
    rw [hraw, ← husage, ← hbalance]
    exact hstake
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
    (modelStep ctx st ())
  rw [modelStep_save_success ctx st hmodel hmstake]
  exact execOn_matches_save_success gasBound ctx raw (st.getD []) storage storageCost rest written
    hmethod hprepare h hrep hpromises hlogs hbalance husage hstake

end WNear.Skeleton
