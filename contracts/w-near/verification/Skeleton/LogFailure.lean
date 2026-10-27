import Skeleton.StorageFailure
import Skeleton.Success

/-!
# Zero log-count rejection after a successful storage write

The method's first twelve opcodes are composed from individual rules. Storage
retains its existing single-call frontier; no prefix or whole-method execution
is a premise. Count rejection reads no message memory.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts

set_option maxHeartbeats 800000

@[irreducible] def logZeroAfter (before : HostStore NearState) : HostStore NearState :=
  let paid := Output.paidStore before (applyCharges before.host [.ext "base"]).1
  { paid with host := { paid.host with lastError := some (.numberOfLogsExceeded 0) } }

/-- Zero-count failure pays only the initial base charge, before decoding. -/
theorem metered_log_zero (extra : Nat) (before : HostStore NearState) (rest : Nat)
    (hlimit : before.host.config.maxNumberLogs = some 0)
    (hcredits : before.host.gas.Credits (before.host.extCosts.cost "base" + rest)) :
    (metered extra "log_utf8" logUtf8Fn).invoke before [.i64 5, .i64 1] =
      .Trap (logZeroAfter before) (HostError.numberOfLogsExceeded 0).message ∧
    (logZeroAfter before).host.gas.burnt = before.host.gas.burnt + before.host.extCosts.cost "base" ∧
    (logZeroAfter before).host.gas.promises = before.host.gas.promises ∧
    (logZeroAfter before).host.gas.Credits rest := by
  have hc := applyCharges_credits before.host [.ext "base"] rest (by simp [BurnsOnly])
    (by simpa [burnSum, burnCost] using hcredits)
  have hf := applyCharges_frame before.host [.ext "base"] (by simp [BurnsOnly])
  have hcfg := congrArg NearState.config hf
  have hpaidLimit : (Output.paidStore before (applyCharges before.host [.ext "base"]).1).host.config.maxNumberLogs = some 0 :=
    (congrArg NearConfig.maxNumberLogs hcfg).trans hlimit
  have hplan : chargesBefore "log_utf8" before [.i64 5, .i64 1] = [.ext "base"] := by
    rw [Output.chargesBefore_logUtf8]
    simp only [logUtf8Read, logCountError, hlimit, Nat.zero_le, ↓reduceIte]
    rfl
  have hcharge : applyCharges before.host (chargesBefore "log_utf8" before [.i64 5, .i64 1]) =
      ((applyCharges before.host [.ext "base"]).1, none) := by
    rw [hplan]
    exact Prod.ext rfl hc.1
  have hi := Output.metered_logUtf8_error extra before 5 1 _ (.numberOfLogsExceeded 0) hcharge (by
    simp only [logUtf8Read, logCountError, hpaidLimit, Nat.zero_le, ↓reduceIte])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [logZeroAfter] using hi
  · simpa [logZeroAfter, Output.paidStore, burnSum, burnCost] using hc.2.1
  · simpa only [logZeroAfter, Output.paidStore] using hc.2.2.1
  · simpa only [logZeroAfter, Output.paidStore] using hc.2.2.2.2

/-- The actual zero-count host trap through the direct-call interpreter rule. -/
theorem wp_call_log_zero (cfg : RuntimeConfig) (store : Store NearState) (limits : ExecLimits)
    (code : List Instr) (fuel rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn))
    (hzero : store.host.config.maxNumberLogs = some 0)
    (hcredits : store.host.gas.Credits (cfg.wasm.regularOpCost + (store.host.extCosts.cost "base" + rest))) :
    WP cfg.wasm (fuel + 1)
      (.next (atCode store limits #[.i64 5, .i64 1] saveFrame [] (.call 2 :: code)))
      (cfg.wasm.regularOpCost + (store.host.extCosts.cost "base" + rest))
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.numberOfLogsExceeded 0).message)
          (commitCall cfg.wasm store (logZeroAfter (inputBefore cfg.wasm store moduleInstance))) ∧ error = none) := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := StorageCredits.charged store cfg.wasm.regularOpCost (store.host.extCosts.cost "base" + rest) hcredits
  have hm := metered_log_zero cfg.fees.numExtraBytesRecord before rest hzero hc
  apply wp_call_host_trap cfg.wasm fuel (store.host.extCosts.cost "base") rest store limits []
    [.i64 5, .i64 1] saveFrame [] code 2 2 moduleInstance
    (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) (logZeroAfter before)
    (HostError.numberOfLogsExceeded 0).message hmodule rfl hfn rfl hcredits hm.1
    (Nat.le_of_eq hm.2.1) _ hm.2.2.2
  change (logZeroAfter before).host.gas.burnt + (logZeroAfter before).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises + store.host.extCosts.cost "base"
  rw [hm.2.1, hm.2.2.1, show before.host.extCosts = store.host.extCosts from rfl]
  omega

def logFailureCost (post : HostStore NearState) : Nat := post.host.extCosts.cost "base"

def logFailureSuffix (cfg : RuntimeConfig) (post : HostStore NearState) (rest : Nat) :=
  cfg.wasm.regularOpCost + (2 * cfg.wasm.regularOpCost +
    (cfg.wasm.regularOpCost + (logFailureCost post + rest)))

def logFailureBudget (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) :=
  cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
    (MeteredHosts.Input.cost (successInputBefore cfg store).host +
      (5 * cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
        (storageCost + logFailureSuffix cfg post rest)))))

def logFailureStore (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState) :=
  commitCall cfg.wasm (successLogBefore cfg store post)
    (logZeroAfter (inputBefore cfg.wasm (successLogBefore cfg store post) moduleInstance))

private theorem saved_base_le (costs : ExtCosts) : costs.cost "base" ≤ burnSum costs savedCharges := by
  simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]

/-- The existing storage frontier retains enough credits for this earlier
failure, including drop, both constants, the log call and its base charge. -/
theorem logFailureSuffix_le_success (cfg : RuntimeConfig) (store : Store NearState)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logFailureSuffix cfg post rest ≤
      (successCosts cfg store post storageCost).storageSuffix cfg.wasm.regularOpCost rest := by
  have hb := saved_base_le (successLogBefore cfg store post).host.extCosts
  have hext : (successLogBefore cfg store post).host.extCosts = post.host.extCosts := rfl
  rw [hext] at hb
  simp only [HostCosts.storageSuffix, HostCosts.logBudget, HostCosts.logSuffix, HostCosts.returnBudget,
    successCosts_log, successCosts_returned, logFailureSuffix, logFailureCost, hext]
  omega

theorem logFailureBudget_eq (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) :
    logFailureBudget cfg store post storageCost rest = 12 * cfg.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore cfg store).host + storageCost + logFailureCost post + rest := by
  unfold logFailureBudget logFailureSuffix
  omega

/-- Exact twelve-opcode prefix, with only the existing local storage frontier
and log-count resource fact as semantic premises. -/
theorem wp_save_log_zero (cfg : RuntimeConfig) (store : Store NearState) (postStorage : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (limits : ExecLimits)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hinputFn : store.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hstorageFn : store.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn))
    (hlogFn : store.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn))
    (hinputLimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hzero : postStorage.host.config.maxNumberLogs = some 0)
    (hstorage : StorageFrontier cfg store postStorage storageCost rest written)
    (hcredits : store.host.gas.Credits (logFailureBudget cfg store postStorage storageCost rest)) :
    WP cfg.wasm 12 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (logFailureBudget cfg store postStorage storageCost rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.numberOfLogsExceeded 0).message) (logFailureStore cfg store postStorage) ∧ error = none) := by
  let op := cfg.wasm.regularOpCost
  let logCost := logFailureCost postStorage
  let suffixBudget := logFailureSuffix cfg postStorage rest
  let inputRest := 5 * op + (op + (storageCost + suffixBudget))
  let suffix := module.funcs[0]!.body.drop 12
  let finalPost : Post := fun remaining final error => remaining = rest ∧ final =
    .trap (.host (HostError.numberOfLogsExceeded 0).message) (logFailureStore cfg store postStorage) ∧ error = none
  have hfirst : store.host.gas.Credits
      (op + (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest))) := hcredits
  have hiCredits : (successInputBefore cfg store).host.gas.Credits
      (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest)) :=
    StorageCredits.charged store op _ hfirst
  have hi := input_evidence cfg (successInputBefore cfg store) inputRest hmodule hinputFn hinputLimit hiCredits
  have hsCredits : (successStorageBefore cfg store).host.gas.Credits (op + (storageCost + suffixBudget)) := by
    apply StorageCredits.chargedMany _ op _ 5
    exact hi.credits
  have hpost : postStorage.host.gas.Credits suffixBudget :=
    hstorage.credits.mono (logFailureSuffix_le_success cfg store postStorage storageCost rest)
  have hdrop : (chargedStore (commitCall cfg.wasm (successStorageBefore cfg store) postStorage) op).host.gas.Credits
      (2 * op + (op + (logCost + rest))) :=
    StorageCredits.charged _ op _ hpost
  have hlog : (successLogBefore cfg store postStorage).host.gas.Credits (op + (logCost + rest)) := by
    apply StorageCredits.chargedMany _ op _ 2
    exact hdrop
  have hlogenv : (successLogBefore cfg store postStorage).funcs = store.funcs ∧
      (successLogBefore cfg store postStorage).modules = store.modules := by
    simp only [successLogBefore, chargedMany_funcs, chargedMany_modules, chargedStore,
      commitCall_funcs, commitCall_modules, successStorageBefore, successInputBefore, and_self]
  have htrap : WP cfg.wasm 1
      (.next (atCode (successLogBefore cfg store postStorage) limits #[.i64 5, .i64 1] saveFrame []
        (.call 2 :: suffix))) (op + (logCost + rest)) finalPost := by
    have ht := wp_call_log_zero cfg (successLogBefore cfg store postStorage) limits suffix 0 rest
      (by rw [hlogenv.2]; exact hmodule) (by rw [hlogenv.1]; exact hlogFn) hzero hlog
    exact ht
  have hlogconst := wp_i64_consts cfg.wasm 1 (op + (logCost + rest))
    (chargedStore (commitCall cfg.wasm (successStorageBefore cfg store) postStorage) op) limits [] saveFrame []
    (.call 2 :: suffix) [5, 1] finalPost hdrop htrap
  have hd := wp_drop cfg.wasm 3 (2 * op + (op + (logCost + rest)))
    (commitCall cfg.wasm (successStorageBefore cfg store) postStorage) limits #[] saveFrame []
    (.i64_const 5 :: .i64_const 1 :: .call 2 :: suffix) (.i64 written) finalPost hpost hlogconst
  have hs := wp_call_host cfg.wasm 4 storageCost suffixBudget (successStorageBefore cfg store) limits []
    [.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max] [.i64 written] saveFrame []
    (.drop :: .i64_const 5 :: .i64_const 1 :: .call 2 :: suffix) 1 1 moduleInstance
    (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) postStorage
    (by simpa only [saveFrame, successStorageBefore, chargedMany_modules, commitCall_modules,
      successInputBefore] using hmodule) rfl
    (by simpa only [successStorageBefore, chargedMany_funcs, commitCall_funcs, successInputBefore] using hstorageFn)
    rfl hsCredits hstorage.invoke hstorage.burnt hstorage.used hpost finalPost hd
  have hstorageconst := wp_i64_consts cfg.wasm 5 (op + (storageCost + suffixBudget))
    (commitCall cfg.wasm (successInputBefore cfg store) (successInputAfter cfg store)) limits [] saveFrame []
    (.call 1 :: .drop :: .i64_const 5 :: .i64_const 1 :: .call 2 :: suffix)
    [1, 0, u64Max, 0, u64Max] finalPost hi.credits hs
  have hinput := wp_call_input cfg.wasm cfg.fees.numExtraBytesRecord 10 inputRest
    (successInputBefore cfg store) limits [] saveFrame []
    (.i64_const 1 :: .i64_const 0 :: .i64_const u64Max :: .i64_const 0 :: .i64_const u64Max ::
      .call 1 :: .drop :: .i64_const 5 :: .i64_const 1 :: .call 2 :: suffix)
    0 0 moduleInstance 0 hmodule rfl hinputFn (by decide) hinputLimit hiCredits finalPost hstorageconst
  have hbody := wp_i64_consts cfg.wasm 11
    (op + (MeteredHosts.Input.cost (successInputBefore cfg store).host + inputRest)) store limits [] saveFrame []
    (.call 0 :: .i64_const 1 :: .i64_const 0 :: .i64_const u64Max :: .i64_const 0 :: .i64_const u64Max ::
      .call 1 :: .drop :: .i64_const 5 :: .i64_const 1 :: .call 2 :: suffix)
    [0] finalPost (by simpa only [List.length_cons, List.length_nil, Nat.one_mul, Nat.zero_add, op] using hfirst) hinput
  simpa [logFailureBudget, logFailureSuffix, finalPost, suffix, module, u64Max, op, logCost, suffixBudget,
    inputRest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody

/-- The count failure installs its own marker and appends no logs. -/
theorem logZero_fields (before : HostStore NearState) :
    (logZeroAfter before).host.lastError = some (.numberOfLogsExceeded 0) ∧
    (logZeroAfter before).host.lastExecutionIssue = before.host.lastExecutionIssue ∧
    (logZeroAfter before).host.logs = before.host.logs := by
  have hf := applyCharges_frame before.host [.ext "base"] (by simp [BurnsOnly])
  have hi := congrArg NearState.lastExecutionIssue hf
  have hl := congrArg NearState.logs hf
  exact ⟨by unfold logZeroAfter; rfl, by simpa only [logZeroAfter, Output.paidStore] using hi,
    by simpa only [logZeroAfter, Output.paidStore] using hl⟩

/-- Only storage's local frame is needed to recover the original fresh issue
marker and empty logs at the failed log host. -/
theorem logFailureStore_fields (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState) :
    (logFailureStore cfg store post).host.lastError = some (.numberOfLogsExceeded 0) ∧
    (logFailureStore cfg store post).host.lastExecutionIssue = post.host.lastExecutionIssue ∧
    (logFailureStore cfg store post).host.logs = post.host.logs := by
  have hf := logZero_fields (inputBefore cfg.wasm (successLogBefore cfg store post) moduleInstance)
  simpa only [logFailureStore, commitCall_host, inputBefore, chargedStore, chargeHost, successLogBefore,
    chargedMany] using hf

def logFailureAttemptBudget (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) :=
  burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + logFailureBudget ctx.protocol
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post storageCost rest)

/-- Startup reaches the proved prefix; no execution equation is a premise. -/
theorem runAttempt_save_log_zero (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (fuel : Nat)
    (hp : PreparationLimits ctx.protocol) (hfuel : 12 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hzero : post.host.config.maxNumberLogs = some 0)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logFailureAttemptBudget ctx raw post storageCost rest)) :
    runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel =
      outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.trap (.host (HostError.numberOfLogsExceeded 0).message)
          (logFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)) none := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := logFailureBudget cfg (executionStore cfg vm raw) post storageCost rest
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
  have hw := wp_save_log_zero cfg (executionStore cfg vm raw) post storageCost rest written execLimits
    (by rfl) (by rfl) (by rfl) (by rfl) hi hzero hstorage ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hr : runMetered cfg.wasm 12 (.next (entryConfig cfg (executionActive cfg vm raw))) =
      (.trap (.host (HostError.numberOfLogsExceeded 0).message)
        (logFailureStore cfg (executionStore cfg vm raw) post), none) := Prod.ext hpost.2.1 hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 12
    (.next (entryConfig cfg (executionActive cfg vm raw))) (by rw [hr]; simp) (fuel - 12)
  rw [show 12 + (fuel - 12) = fuel by omega] at hextra
  have hrun := hextra.trans hr
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg vm raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

def logFailureOutcome (ctx : Context) (raw : Storage) (post : HostStore NearState) : VMOutcome :=
  outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.trap (.host (HostError.numberOfLogsExceeded 0).message)
      (logFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)) none

/-- The local storage frame propagates actual initial fresh markers and logs. -/
theorem logFailureOutcome_fields (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post) :
    (logFailureOutcome ctx raw post).aborted = some (.hostError (.numberOfLogsExceeded 0)) ∧
    (logFailureOutcome ctx raw post).logs = [] ∧ (logFailureOutcome ctx raw post).receiptsValid = true := by
  have hf := logFailureStore_fields ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post
  have hi := (StorageFrame.Frame.lastExecutionIssue hframe).trans
    (storageInput_lastExecutionIssue ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hl := (StorageFrame.Frame.logs hframe).trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have he : (logFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.lastError =
      some (.numberOfLogsExceeded 0) := hf.1
  have hissue := hf.2.1.trans hi
  have hlogs := hf.2.2.trans hl
  change (logFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.lastExecutionIssue = none at hissue
  change (logFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.logs = [] at hlogs
  simp [logFailureOutcome, outcomeOfExecution, StepResult.host, trapError, he, hissue, hlogs,
    logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- The public VM's receipt check preserves the classified log failure. -/
theorem run_save_log_zero_public (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hzero : post.host.config.maxNumberLogs = some 0)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logFailureAttemptBudget ctx raw post storageCost rest)) :
    run ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw = logFailureOutcome ctx raw post := by
  have hr := runAttempt_save_log_zero ctx raw post storageCost rest written
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hp
    (Nat.le_trans (by decide : 12 ≤ 16) (fuelFor_save _ _)) hinput hzero hstorage hcredits
  simp only [run, hr]
  change (logFailureOutcome ctx raw post).checkReceipts _ _ _ = _
  simp only [VMOutcome.checkReceipts, (logFailureOutcome_fields ctx raw post hframe).2.2, ↓reduceIte]

/-- The independent model reaches its log-count rejection after accepting
all three length checks. -/
theorem modelStep_log_zero (ctx : Context) (st : Option Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0) :
    modelStep ctx st () = .error ⟨.panic (.other (HostError.numberOfLogsExceeded 0).message), []⟩ := by
  simp [modelStep, Nat.not_lt.mpr hinput, Nat.not_lt.mpr hkey, Nat.not_lt.mpr hvalue, hzero]

/-- Actual receipt-level matching for count rejection after a completed write.
Storage is the existing local frontier; its frame supplies marker freshness,
original limits and logs. Boundary observation rolls the completed write back. -/
theorem execOn_matches_log_zero
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logFailureAttemptBudget ctx raw post storageCost rest)) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hc := congrArg NearConfig.maxNumberLogs (StorageFrame.Frame.config hframe)
  have hb := congrArg NearConfig.maxNumberLogs (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hz : post.host.config.maxNumberLogs = some 0 := by
    have hbefore : (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.config.maxNumberLogs =
        some ctx.protocol.wasm.limits.maxNumberLogs := hb
    rw [hzero] at hbefore
    exact hc.trans hbefore
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) (modelStep ctx st ())
  rw [modelStep_log_zero ctx st hinput hkey hvalue hzero]
  have hr := run_save_log_zero_public ctx raw post storageCost rest written hp hinput hz hstorage hframe hcredits
  have hf := logFailureOutcome_fields ctx raw post hframe
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.numberOfLogsExceeded 0), hf.1, rfl, hf.2.1⟩

theorem logFailureAttemptBudget_eq (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) :
    logFailureAttemptBudget ctx raw post storageCost rest =
      burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
      20 * ctx.protocol.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host +
      storageCost + logFailureCost post + rest := by
  unfold logFailureAttemptBudget
  rw [logFailureBudget_eq]
  omega

end WNear.Skeleton
