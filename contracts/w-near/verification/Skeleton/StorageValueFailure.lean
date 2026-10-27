import Skeleton.StorageFailure
import Skeleton.FailureExecution
import NearVM.MeteredHosts.StorageFailure

/-!
# Storage-value rejection through the real method prefix

Length rejection precedes all trie/proof operations. This file composes the
successful input call and the five storage arguments with the actual trap.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts MeteredHosts.StorageMetered

set_option maxHeartbeats 800000

/-- Storage sees the call opcode's charge before validating its value. -/
def valueFailureBefore (cfg : RuntimeConfig) (store : Store NearState) :=
  inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance

def valueFailureCost (cfg : RuntimeConfig) (store : Store NearState) : Nat :=
  burnSum (valueFailureBefore cfg store).host.extCosts
    (StorageFailure.valueCharges (valueFailureBefore cfg store) 1 0 u64Max 0)

@[irreducible] def valueFailureAfter (cfg : RuntimeConfig) (store : Store NearState) (length limit : Nat) :=
  StorageFailure.rejected (valueFailureBefore cfg store)
    (StorageFailure.valueCharges (valueFailureBefore cfg store) 1 0 u64Max 0) (.valueLengthExceeded length limit)

def valueFailureStore (cfg : RuntimeConfig) (store : Store NearState) (length limit : Nat) :=
  commitCall cfg.wasm (successStorageBefore cfg store) (valueFailureAfter cfg store length limit)

def valueFailureBudget (cfg : RuntimeConfig) (store : Store NearState) (rest : Nat) : Nat :=
  cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
    (MeteredHosts.Input.cost (successInputBefore cfg store).host +
      (5 * cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost + (valueFailureCost cfg store + rest)))))

theorem valueFailureBudget_eq (cfg : RuntimeConfig) (store : Store NearState) (rest : Nat) :
    valueFailureBudget cfg store rest = 8 * cfg.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore cfg store).host + valueFailureCost cfg store + rest := by
  unfold valueFailureBudget
  omega

/-- Exactly the first eight body instructions execute; none of the suffix's
storage/drop/output behavior is assumed. -/
theorem wp_save_value_too_long (cfg : RuntimeConfig) (store : Store NearState)
    (limits : ExecLimits) (value : Near.Bytes) (limit rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hinputFn : store.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hstorageFn : store.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn))
    (hinputLimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hview : (valueFailureBefore cfg store).host.context.isView = false)
    (hkey : getMemOrReg (valueFailureBefore cfg store) 0 1 = some "k".toUTF8.toList)
    (hkeyLimit : ∀ n, (valueFailureBefore cfg store).host.config.maxStorageKeyLen = some n → 1 ≤ n)
    (hvalue : getMemOrReg (valueFailureBefore cfg store) 0 u64Max = some value)
    (hlimit : (valueFailureBefore cfg store).host.config.maxStorageValueLen = some limit)
    (hlong : limit < value.length)
    (hcredits : store.host.gas.Credits (valueFailureBudget cfg store rest)) :
    WP cfg.wasm 8 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (valueFailureBudget cfg store rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.valueLengthExceeded value.length limit).message) (valueFailureStore cfg store value.length limit) ∧ error = none) := by
  let op := cfg.wasm.regularOpCost
  let cost := valueFailureCost cfg store
  let inputRest := 5 * op + (op + (cost + rest))
  have hfirst : store.host.gas.Credits
      (op + (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest))) := by
    simpa only [valueFailureBudget, op, cost, inputRest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_mul, Nat.one_mul] using hcredits
  have hiCredits : (successInputBefore cfg store).host.gas.Credits
      (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest)) := by
    exact StorageCredits.charged store op _ hfirst
  have hi := input_evidence cfg (successInputBefore cfg store) inputRest hmodule hinputFn hinputLimit hiCredits
  have hsCredits : (successStorageBefore cfg store).host.gas.Credits (op + (cost + rest)) := by
    apply StorageCredits.chargedMany _ op _ 5
    exact hi.credits
  have hc : (valueFailureBefore cfg store).host.gas.Credits (cost + rest) :=
    StorageCredits.charged (successStorageBefore cfg store) op _ hsCredits
  have hgas := StorageFailure.rejected_gas (valueFailureBefore cfg store)
    (StorageFailure.valueCharges (valueFailureBefore cfg store) 1 0 u64Max 0) (.valueLengthExceeded value.length limit) rest
    (StorageFailure.valueCharges_burns _ _ _ _ _) hc
  have hinvoke := StorageFailure.metered_value_too_long cfg.fees.numExtraBytesRecord
    (valueFailureBefore cfg store) 1 0 u64Max 0 "k".toUTF8.toList value limit rest hview hkey
    (by intro n hn; simpa only [show "k".toUTF8.toList.length = 1 by decide +kernel] using hkeyLimit n hn)
    hvalue hlimit hlong hc
  have hinvoke' : (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
      (valueFailureBefore cfg store) (args 1 0 u64Max 0) =
      .Trap (valueFailureAfter cfg store value.length limit) (HostError.valueLengthExceeded value.length limit).message := by
    simpa only [valueFailureAfter] using hinvoke
  have hburn : (valueFailureAfter cfg store value.length limit).host.gas.burnt =
      (valueFailureBefore cfg store).host.gas.burnt + cost := by simpa only [valueFailureAfter, cost, valueFailureCost] using hgas.1
  have hpromises : (valueFailureAfter cfg store value.length limit).host.gas.promises =
      (valueFailureBefore cfg store).host.gas.promises := by simpa only [valueFailureAfter] using hgas.2.1
  have hrest : (valueFailureAfter cfg store value.length limit).host.gas.Credits rest := by
    simpa only [valueFailureAfter] using hgas.2.2
  let suffix := module.funcs[0]!.body.drop 8
  let post : Post := fun remaining final error => remaining = rest ∧ final =
    .trap (.host (HostError.valueLengthExceeded value.length limit).message) (valueFailureStore cfg store value.length limit) ∧ error = none
  have htrap : WP cfg.wasm 1
      (.next (atCode (successStorageBefore cfg store) limits (args 1 0 u64Max 0).toArray saveFrame []
        (.call 1 :: suffix))) (op + (cost + rest)) post := by
    apply wp_call_host_trap cfg.wasm 0 cost rest (successStorageBefore cfg store) limits []
      (args 1 0 u64Max 0) saveFrame [] suffix 1 1 moduleInstance
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) (valueFailureAfter cfg store value.length limit)
      (HostError.valueLengthExceeded value.length limit).message
      (by simpa only [saveFrame, successStorageBefore, chargedMany_modules, commitCall_modules] using hi.module)
      rfl (by simpa only [successStorageBefore, chargedMany_funcs, commitCall_funcs,
        successInputBefore, chargedMany_funcs] using hstorageFn) rfl hsCredits hinvoke'
      (Nat.le_of_eq hburn) _ hrest
    change (valueFailureAfter cfg store value.length limit).host.gas.burnt + (valueFailureAfter cfg store value.length limit).host.gas.promises ≤
      (valueFailureBefore cfg store).host.gas.burnt + (valueFailureBefore cfg store).host.gas.promises + cost
    rw [hburn, hpromises]; omega
  have hconst := wp_i64_consts cfg.wasm 1 (op + (cost + rest))
    (commitCall cfg.wasm (successInputBefore cfg store) (successInputAfter cfg store)) limits [] saveFrame []
    (.call 1 :: suffix) [1, 0, u64Max, 0, u64Max] post hi.credits htrap
  have hinput := wp_call_input cfg.wasm cfg.fees.numExtraBytesRecord 6 inputRest
    (successInputBefore cfg store) limits [] saveFrame []
    (.i64_const 1 :: .i64_const 0 :: .i64_const u64Max :: .i64_const 0 :: .i64_const u64Max :: .call 1 :: suffix)
    0 0 moduleInstance 0 hmodule rfl hinputFn (by decide) hinputLimit hiCredits post hconst
  have hbody := wp_i64_consts cfg.wasm 7
    (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest)) store limits [] saveFrame []
    (.call 0 :: .i64_const 1 :: .i64_const 0 :: .i64_const u64Max :: .i64_const 0 :: .i64_const u64Max :: .call 1 :: suffix)
    [0] post (by simpa only [List.length_cons, List.length_nil, Nat.one_mul, Nat.zero_add, op] using hfirst) hinput
  simpa [valueFailureBudget, post, suffix, module, u64Max, op, cost, inputRest, Nat.add_mul, Nat.one_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody


/-- Complete failure budget: loading and eight activation operations precede
the eight body operations and the input/storage-validation host costs. -/
def valueFailureAttemptBudget (ctx : Context) (raw : Storage) (rest : Nat) :=
  burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost +
      valueFailureBudget ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) rest)

theorem runAttempt_save_value_too_long (ctx : Context) (raw : Storage) (fuel rest : Nat)
    (hp : PreparationLimits ctx.protocol) (hfuel : 8 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw rest)) :
    runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel =
      outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.trap (.host (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue).message)
          (valueFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
            ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)) none := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := valueFailureBudget cfg (executionStore cfg vm raw) rest
  have hs : runAttempt cfg module 0 "save" vm raw fuel =
      (let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg (executionLoaded cfg vm raw)))
       outcomeOfExecution vm raw result.1 result.2) ∧
      (executionLoaded cfg vm raw).gas.Credits (8 * cfg.wasm.regularOpCost + budget) := by
    simpa only [executionLoaded] using runAttempt_save_credits cfg vm raw fuel
      (8 * cfg.wasm.regularOpCost + budget) hp.positive hp.minmax hp.maximum hp.types hp.functions hcredits
  have ha : (executionActive cfg vm raw).gas.Credits budget := by
    have hc := GasCounter.burn_credits (executionLoaded cfg vm raw).gas (8 * cfg.wasm.regularOpCost) budget hs.2
    simpa only [executionActive, chargeHost] using hc.2.2.2
  have hi : withinLimit (executionStore cfg vm raw).host.config.maxRegisterLen
      (executionStore cfg vm raw).host.context.input.length = true := by
    simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
    change withinLimit (some cfg.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hinput
  have hk := emptyPaid_key ctx raw hp.positive
  rw [StorageFrame.Frame.getMemOrReg (emptyPaid_frame ctx raw)] at hk
  have hv : (valueFailureBefore cfg (executionStore cfg vm raw)).host.context.isView = false :=
    storageInput_isView cfg vm raw
  have hlimit : (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageValueLen =
      some cfg.wasm.limits.maxLengthStorageValue := by
    have hc := congrArg NearConfig.maxStorageValueLen (storageInput_config cfg vm raw)
    exact hc
  have hvalue := emptyPaid_value ctx raw
  rw [StorageFrame.Frame.getMemOrReg (emptyPaid_frame ctx raw)] at hvalue
  have hkcfg : (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some cfg.wasm.limits.maxLengthStorageKey := by
    have hc := congrArg NearConfig.maxStorageKeyLen (storageInput_config cfg vm raw)
    exact hc
  have hkaccepted : ∀ n, (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some n → 1 ≤ n := by
    intro n hn
    rw [hkcfg] at hn
    cases Option.some.inj hn
    exact hkeyAccepted
  have hw := wp_save_value_too_long cfg (executionStore cfg vm raw) execLimits ctx.args
    cfg.wasm.limits.maxLengthStorageValue rest (by rfl) (by rfl) (by rfl)
    hi hv hk hkaccepted hvalue hlimit hlong ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hr : runMetered cfg.wasm 8 (.next (entryConfig cfg (executionActive cfg vm raw))) =
      (.trap (.host (HostError.valueLengthExceeded ctx.args.length cfg.wasm.limits.maxLengthStorageValue).message)
        (valueFailureStore cfg (executionStore cfg vm raw) ctx.args.length cfg.wasm.limits.maxLengthStorageValue), none) :=
    Prod.ext hpost.2.1 hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 8
    (.next (entryConfig cfg (executionActive cfg vm raw))) (by rw [hr]; simp) (fuel - 8)
  rw [show 8 + (fuel - 8) = fuel by omega] at hextra
  have hrun := hextra.trans hr
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg vm raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

def valueFailureOutcome (ctx : Context) (raw : Storage) : VMOutcome :=
  outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.trap (.host (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue).message)
      (valueFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
        ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)) none

/-- The trap marker is freshly installed, while no earlier execution issue or
log can survive initial-state construction and the successful input prefix. -/
theorem valueFailureOutcome_fields (ctx : Context) (raw : Storage) :
    (valueFailureOutcome ctx raw).aborted = some (.hostError
      (.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)) ∧
    (valueFailureOutcome ctx raw).logs = [] ∧ (valueFailureOutcome ctx raw).receiptsValid = true := by
  let store := executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw
  let before := valueFailureBefore ctx.protocol store
  let limit := ctx.protocol.wasm.limits.maxLengthStorageValue
  have hf := StorageFailure.rejected_fields before (StorageFailure.valueCharges before 1 0 u64Max 0)
    (.valueLengthExceeded ctx.args.length limit) (StorageFailure.valueCharges_burns _ _ _ _ _)
  have he : (valueFailureAfter ctx.protocol store ctx.args.length limit).host.lastError = some (.valueLengthExceeded ctx.args.length limit) := by
    simpa only [valueFailureAfter] using hf.2.2.2.2.1
  have hi : (valueFailureAfter ctx.protocol store ctx.args.length limit).host.lastExecutionIssue = none := by
    have hh : (valueFailureAfter ctx.protocol store ctx.args.length limit).host.lastExecutionIssue = before.host.lastExecutionIssue := by
      simpa only [valueFailureAfter] using hf.2.2.2.2.2
    exact hh.trans (storageInput_lastExecutionIssue ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hl : (valueFailureAfter ctx.protocol store ctx.args.length limit).host.logs = [] := by
    have hh : (valueFailureAfter ctx.protocol store ctx.args.length limit).host.logs = before.host.logs := by
      simpa only [valueFailureAfter] using hf.2.2.2.1
    exact hh.trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  dsimp only [store, before, limit] at he hi hl
  simp [valueFailureOutcome, outcomeOfExecution, StepResult.host, valueFailureStore, commitCall_host,
    trapError, hi, he, hl, logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- The default-fuel public runner retains the exact classified failure. -/
theorem run_save_value_too_long_public (ctx : Context) (raw : Storage) (rest : Nat)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw rest)) :
    run ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw = valueFailureOutcome ctx raw := by
  have hr := runAttempt_save_value_too_long ctx raw (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) rest
    hp (Nat.le_trans (by decide : 8 ≤ 16) (fuelFor_save _ _)) hinput hkeyAccepted hlong hcredits
  simp only [run, hr]
  change (valueFailureOutcome ctx raw).checkReceipts _ _ _ = _
  simp only [VMOutcome.checkReceipts, (valueFailureOutcome_fields ctx raw).2.2, ↓reduceIte]

/-- The independent model rejects the value after accepting both input and key. -/
theorem modelStep_value_too_long (ctx : Context) (st : Option Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length) :
    modelStep ctx st () = .error ⟨.panic (.other
      (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue).message), []⟩ := by
  simp [modelStep, Nat.not_lt.mpr hinput, Nat.not_lt.mpr hkeyAccepted, hlong]

/-- One complete actual model-matching failure branch. No trie, canonicality,
recorded-proof or storage-read premise is required for this early rejection. -/
theorem execOn_matches_value_too_long
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest : Nat)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw rest)) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) (modelStep ctx st ())
  rw [modelStep_value_too_long ctx st hinput hkeyAccepted hlong]
  have hr := run_save_value_too_long_public ctx raw rest hp hinput hkeyAccepted hlong hcredits
  have hf := valueFailureOutcome_fields ctx raw
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue), hf.1, rfl, hf.2.1⟩


/-- The rejection pays six ordered charges: two fixed host costs, the key's
two memory charges, then the value's two register charges. -/
theorem valueFailureCost_eq (cfg : RuntimeConfig) (store : Store NearState) (value : Near.Bytes)
    (hregister : (valueFailureBefore cfg store).host.registers 0 = some value) :
    valueFailureCost cfg store =
      (valueFailureBefore cfg store).host.extCosts.cost "base" +
      (valueFailureBefore cfg store).host.extCosts.cost "storage_write_base" +
      (valueFailureBefore cfg store).host.extCosts.cost "read_memory_base" +
      (valueFailureBefore cfg store).host.extCosts.cost "read_memory_byte" +
      (valueFailureBefore cfg store).host.extCosts.cost "read_register_base" +
      (valueFailureBefore cfg store).host.extCosts.cost "read_register_byte" * value.length := by
  simp [valueFailureCost, StorageFailure.valueCharges, StorageFailure.keyCharges, readSpan,
    show (1 : UInt64) ≠ u64Max by decide +kernel, hregister, burnSum, burnCost, Nat.add_assoc]

/-- Exact gas and residual credits on the computed value rejection. -/
theorem valueFailureAfter_gas (cfg : RuntimeConfig) (store : Store NearState) (length limit rest : Nat)
    (hcredits : (valueFailureBefore cfg store).host.gas.Credits (valueFailureCost cfg store + rest)) :
    (valueFailureAfter cfg store length limit).host.gas.burnt =
      (valueFailureBefore cfg store).host.gas.burnt + valueFailureCost cfg store ∧
    (valueFailureAfter cfg store length limit).host.gas.promises = (valueFailureBefore cfg store).host.gas.promises ∧
    (valueFailureAfter cfg store length limit).host.gas.Credits rest := by
  have h := StorageFailure.rejected_gas (valueFailureBefore cfg store)
    (StorageFailure.valueCharges (valueFailureBefore cfg store) 1 0 u64Max 0) (.valueLengthExceeded length limit) rest
    (StorageFailure.valueCharges_burns _ _ _ _ _) hcredits
  simpa only [valueFailureAfter, valueFailureCost] using h

theorem valueFailureAttemptBudget_eq (ctx : Context) (raw : Storage) (rest : Nat) :
    valueFailureAttemptBudget ctx raw rest =
      burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
      16 * ctx.protocol.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host +
      valueFailureCost ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) + rest := by
  unfold valueFailureAttemptBudget
  rw [valueFailureBudget_eq]
  omega

end WNear.Skeleton
