import Skeleton.EmptyStorage
import Skeleton.FailureExecution
import NearVM.MeteredHosts.StorageFailure

/-!
# Storage-key rejection through the real method prefix

Length rejection precedes all trie/proof operations. This file composes the
successful input call and the five storage arguments with the actual trap.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts MeteredHosts.StorageMetered

set_option maxHeartbeats 800000

/-- Storage sees the call opcode's charge before validating its key. -/
def keyFailureBefore (cfg : RuntimeConfig) (store : Store NearState) :=
  inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance

def keyFailureCost (cfg : RuntimeConfig) (store : Store NearState) : Nat :=
  burnSum (keyFailureBefore cfg store).host.extCosts
    (StorageFailure.keyCharges (keyFailureBefore cfg store) 1 0)

@[irreducible] def keyFailureAfter (cfg : RuntimeConfig) (store : Store NearState) (limit : Nat) :=
  StorageFailure.rejected (keyFailureBefore cfg store)
    (StorageFailure.keyCharges (keyFailureBefore cfg store) 1 0) (.keyLengthExceeded 1 limit)

def keyFailureStore (cfg : RuntimeConfig) (store : Store NearState) (limit : Nat) :=
  commitCall cfg.wasm (successStorageBefore cfg store) (keyFailureAfter cfg store limit)

def keyFailureBudget (cfg : RuntimeConfig) (store : Store NearState) (rest : Nat) : Nat :=
  cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
    (MeteredHosts.Input.cost (successInputBefore cfg store).host +
      (5 * cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost + (keyFailureCost cfg store + rest)))))

theorem keyFailureBudget_eq (cfg : RuntimeConfig) (store : Store NearState) (rest : Nat) :
    keyFailureBudget cfg store rest = 8 * cfg.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore cfg store).host + keyFailureCost cfg store + rest := by
  unfold keyFailureBudget
  omega

/-- Exactly the first eight body instructions execute; none of the suffix's
storage/drop/output behavior is assumed. -/
theorem wp_save_key_too_long (cfg : RuntimeConfig) (store : Store NearState)
    (limits : ExecLimits) (limit rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hinputFn : store.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hstorageFn : store.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn))
    (hinputLimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hview : (keyFailureBefore cfg store).host.context.isView = false)
    (hkey : getMemOrReg (keyFailureBefore cfg store) 0 1 = some "k".toUTF8.toList)
    (hlimit : (keyFailureBefore cfg store).host.config.maxStorageKeyLen = some limit)
    (hlong : limit < 1)
    (hcredits : store.host.gas.Credits (keyFailureBudget cfg store rest)) :
    WP cfg.wasm 8 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (keyFailureBudget cfg store rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.keyLengthExceeded 1 limit).message) (keyFailureStore cfg store limit) ∧ error = none) := by
  let op := cfg.wasm.regularOpCost
  let cost := keyFailureCost cfg store
  let inputRest := 5 * op + (op + (cost + rest))
  have hfirst : store.host.gas.Credits
      (op + (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest))) := by
    simpa only [keyFailureBudget, op, cost, inputRest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_mul, Nat.one_mul] using hcredits
  have hiCredits : (successInputBefore cfg store).host.gas.Credits
      (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest)) := by
    exact StorageCredits.charged store op _ hfirst
  have hi := input_evidence cfg (successInputBefore cfg store) inputRest hmodule hinputFn hinputLimit hiCredits
  have hsCredits : (successStorageBefore cfg store).host.gas.Credits (op + (cost + rest)) := by
    apply StorageCredits.chargedMany _ op _ 5
    exact hi.credits
  have hc : (keyFailureBefore cfg store).host.gas.Credits (cost + rest) :=
    StorageCredits.charged (successStorageBefore cfg store) op _ hsCredits
  have hgas := StorageFailure.rejected_gas (keyFailureBefore cfg store)
    (StorageFailure.keyCharges (keyFailureBefore cfg store) 1 0) (.keyLengthExceeded 1 limit) rest
    (StorageFailure.keyCharges_burns _ _ _) hc
  have hinvoke := StorageFailure.metered_key_too_long cfg.fees.numExtraBytesRecord
    (keyFailureBefore cfg store) 1 0 u64Max 0 "k".toUTF8.toList limit rest hview hkey hlimit
    (by simpa only [show "k".toUTF8.toList.length = 1 by decide +kernel] using hlong) hc
  have hinvoke' : (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
      (keyFailureBefore cfg store) (args 1 0 u64Max 0) =
      .Trap (keyFailureAfter cfg store limit) (HostError.keyLengthExceeded 1 limit).message := by
    simpa only [keyFailureAfter, show "k".toUTF8.toList.length = 1 by decide +kernel] using hinvoke
  have hburn : (keyFailureAfter cfg store limit).host.gas.burnt =
      (keyFailureBefore cfg store).host.gas.burnt + cost := by simpa only [keyFailureAfter, cost, keyFailureCost] using hgas.1
  have hpromises : (keyFailureAfter cfg store limit).host.gas.promises =
      (keyFailureBefore cfg store).host.gas.promises := by simpa only [keyFailureAfter] using hgas.2.1
  have hrest : (keyFailureAfter cfg store limit).host.gas.Credits rest := by
    simpa only [keyFailureAfter] using hgas.2.2
  let suffix := module.funcs[0]!.body.drop 8
  let post : Post := fun remaining final error => remaining = rest ∧ final =
    .trap (.host (HostError.keyLengthExceeded 1 limit).message) (keyFailureStore cfg store limit) ∧ error = none
  have htrap : WP cfg.wasm 1
      (.next (atCode (successStorageBefore cfg store) limits (args 1 0 u64Max 0).toArray saveFrame []
        (.call 1 :: suffix))) (op + (cost + rest)) post := by
    apply wp_call_host_trap cfg.wasm 0 cost rest (successStorageBefore cfg store) limits []
      (args 1 0 u64Max 0) saveFrame [] suffix 1 1 moduleInstance
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) (keyFailureAfter cfg store limit)
      (HostError.keyLengthExceeded 1 limit).message
      (by simpa only [saveFrame, successStorageBefore, chargedMany_modules, commitCall_modules] using hi.module)
      rfl (by simpa only [successStorageBefore, chargedMany_funcs, commitCall_funcs,
        successInputBefore, chargedMany_funcs] using hstorageFn) rfl hsCredits hinvoke'
      (Nat.le_of_eq hburn) _ hrest
    change (keyFailureAfter cfg store limit).host.gas.burnt + (keyFailureAfter cfg store limit).host.gas.promises ≤
      (keyFailureBefore cfg store).host.gas.burnt + (keyFailureBefore cfg store).host.gas.promises + cost
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
  simpa [keyFailureBudget, post, suffix, module, u64Max, op, cost, inputRest, Nat.add_mul, Nat.one_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody

/-- Complete failure budget: loading and eight activation operations precede
the eight body operations and the input/key-validation host costs. -/
def keyFailureAttemptBudget (ctx : Context) (raw : Storage) (rest : Nat) :=
  burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost +
      keyFailureBudget ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) rest)

theorem runAttempt_save_key_too_long (ctx : Context) (raw : Storage) (fuel rest : Nat)
    (hp : PreparationLimits ctx.protocol) (hfuel : 8 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw rest)) :
    runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel =
      outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.trap (.host (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey).message)
          (keyFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
            ctx.protocol.wasm.limits.maxLengthStorageKey)) none := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := keyFailureBudget cfg (executionStore cfg vm raw) rest
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
  have hv : (keyFailureBefore cfg (executionStore cfg vm raw)).host.context.isView = false :=
    storageInput_isView cfg vm raw
  have hlimit : (keyFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some cfg.wasm.limits.maxLengthStorageKey := by
    have hc := congrArg NearConfig.maxStorageKeyLen (storageInput_config cfg vm raw)
    exact hc
  have hw := wp_save_key_too_long cfg (executionStore cfg vm raw) execLimits
    cfg.wasm.limits.maxLengthStorageKey rest (by rfl) (by rfl) (by rfl) hi hv hk hlimit hlong ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hr : runMetered cfg.wasm 8 (.next (entryConfig cfg (executionActive cfg vm raw))) =
      (.trap (.host (HostError.keyLengthExceeded 1 cfg.wasm.limits.maxLengthStorageKey).message)
        (keyFailureStore cfg (executionStore cfg vm raw) cfg.wasm.limits.maxLengthStorageKey), none) :=
    Prod.ext hpost.2.1 hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 8
    (.next (entryConfig cfg (executionActive cfg vm raw))) (by rw [hr]; simp) (fuel - 8)
  rw [show 8 + (fuel - 8) = fuel by omega] at hextra
  have hrun := hextra.trans hr
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg vm raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

def keyFailureOutcome (ctx : Context) (raw : Storage) : VMOutcome :=
  outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.trap (.host (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey).message)
      (keyFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
        ctx.protocol.wasm.limits.maxLengthStorageKey)) none

/-- The trap marker is freshly installed, while no earlier execution issue or
log can survive initial-state construction and the successful input prefix. -/
theorem keyFailureOutcome_fields (ctx : Context) (raw : Storage) :
    (keyFailureOutcome ctx raw).aborted = some (.hostError
      (.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey)) ∧
    (keyFailureOutcome ctx raw).logs = [] ∧ (keyFailureOutcome ctx raw).receiptsValid = true := by
  let store := executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw
  let before := keyFailureBefore ctx.protocol store
  let limit := ctx.protocol.wasm.limits.maxLengthStorageKey
  have hf := StorageFailure.rejected_fields before (StorageFailure.keyCharges before 1 0)
    (.keyLengthExceeded 1 limit) (StorageFailure.keyCharges_burns _ _ _)
  have he : (keyFailureAfter ctx.protocol store limit).host.lastError = some (.keyLengthExceeded 1 limit) := by
    simpa only [keyFailureAfter] using hf.2.2.2.2.1
  have hi : (keyFailureAfter ctx.protocol store limit).host.lastExecutionIssue = none := by
    have hh : (keyFailureAfter ctx.protocol store limit).host.lastExecutionIssue = before.host.lastExecutionIssue := by
      simpa only [keyFailureAfter] using hf.2.2.2.2.2
    exact hh.trans (storageInput_lastExecutionIssue ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hl : (keyFailureAfter ctx.protocol store limit).host.logs = [] := by
    have hh : (keyFailureAfter ctx.protocol store limit).host.logs = before.host.logs := by
      simpa only [keyFailureAfter] using hf.2.2.2.1
    exact hh.trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  dsimp only [store, before, limit] at he hi hl
  simp [keyFailureOutcome, outcomeOfExecution, StepResult.host, keyFailureStore, commitCall_host,
    trapError, hi, he, hl, logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- The default-fuel public runner retains the exact classified failure. -/
theorem run_save_key_too_long_public (ctx : Context) (raw : Storage) (rest : Nat)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw rest)) :
    run ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw = keyFailureOutcome ctx raw := by
  have hr := runAttempt_save_key_too_long ctx raw (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) rest
    hp (Nat.le_trans (by decide : 8 ≤ 16) (fuelFor_save _ _)) hinput hlong hcredits
  simp only [run, hr]
  change (keyFailureOutcome ctx raw).checkReceipts _ _ _ = _
  simp only [VMOutcome.checkReceipts, (keyFailureOutcome_fields ctx raw).2.2, ↓reduceIte]

/-- The independent model rejects the key only after accepting the input. -/
theorem modelStep_key_too_long (ctx : Context) (st : Option Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1) :
    modelStep ctx st () = .error ⟨.panic (.other
      (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey).message), []⟩ := by
  simp [modelStep, Nat.not_lt.mpr hinput, hlong]

/-- One complete actual model-matching failure branch. No trie, canonicality,
recorded-proof or storage-read premise is required for this early rejection. -/
theorem execOn_matches_key_too_long
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest : Nat)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw rest)) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) (modelStep ctx st ())
  rw [modelStep_key_too_long ctx st hinput hlong]
  have hr := run_save_key_too_long_public ctx raw rest hp hinput hlong hcredits
  have hf := keyFailureOutcome_fields ctx raw
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey), hf.1, rfl, hf.2.1⟩

/-- The rejected one-byte key pays four exact fixed charges; the value span
is never part of this plan. -/
theorem keyFailureCost_eq (cfg : RuntimeConfig) (store : Store NearState) :
    keyFailureCost cfg store =
      (keyFailureBefore cfg store).host.extCosts.cost "base" +
      (keyFailureBefore cfg store).host.extCosts.cost "storage_write_base" +
      (keyFailureBefore cfg store).host.extCosts.cost "read_memory_base" +
      (keyFailureBefore cfg store).host.extCosts.cost "read_memory_byte" := by
  simp [keyFailureCost, StorageFailure.keyCharges, readSpan,
    show (1 : UInt64) ≠ u64Max by decide +kernel, burnSum, burnCost, Nat.add_assoc]

/-- Exact host gas and residual credits, without any complete-invocation
premise and including the rejected store's unchanged promise reservation. -/
theorem keyFailureAfter_gas (cfg : RuntimeConfig) (store : Store NearState) (limit rest : Nat)
    (hcredits : (keyFailureBefore cfg store).host.gas.Credits (keyFailureCost cfg store + rest)) :
    (keyFailureAfter cfg store limit).host.gas.burnt =
      (keyFailureBefore cfg store).host.gas.burnt + keyFailureCost cfg store ∧
    (keyFailureAfter cfg store limit).host.gas.promises = (keyFailureBefore cfg store).host.gas.promises ∧
    (keyFailureAfter cfg store limit).host.gas.Credits rest := by
  have h := StorageFailure.rejected_gas (keyFailureBefore cfg store)
    (StorageFailure.keyCharges (keyFailureBefore cfg store) 1 0) (.keyLengthExceeded 1 limit) rest
    (StorageFailure.keyCharges_burns _ _ _) hcredits
  simpa only [keyFailureAfter, keyFailureCost] using h

theorem keyFailureAttemptBudget_eq (ctx : Context) (raw : Storage) (rest : Nat) :
    keyFailureAttemptBudget ctx raw rest =
      burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
      16 * ctx.protocol.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host +
      keyFailureCost ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) + rest := by
  unfold keyFailureAttemptBudget
  rw [keyFailureBudget_eq]
  omega

end WNear.Skeleton
