import Skeleton.LogFailure

/-! Total-log-length rejection after a successful storage write. The first log
passes its count check, then rejects length before reading message memory. -/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts
set_option maxHeartbeats 800000

def logLengthCharges : List Charge := [.ext "base", .ext "utf8_decoding_base"]
def logLengthCost (costs : ExtCosts) : Nat := costs.cost "base" + costs.cost "utf8_decoding_base"

theorem logLength_read (before : HostStore NearState) (limit : Nat)
    (hcount : logCountError before = none) (hlogs : before.host.logs = [])
    (hlimit : before.host.config.maxLogLen = some limit) (hshort : limit < 5) :
    logUtf8Read before 5 1 =
      ⟨[ext1 "base", ext1 "utf8_decoding_base"], .error (.totalLogLengthExceeded 5 limit)⟩ := by
  have hspace : 5 > logSpace before := by
    simpa [logSpace, totalLogLength, hlogs, hlimit] using hshort
  have herror : totalLogLengthExceeded before 5 = .totalLogLengthExceeded 5 limit := by
    simp only [totalLogLengthExceeded, totalLogLength, hlogs, List.map_nil, List.sum_nil,
      Nat.zero_add, hlimit, Option.getD_some]
    rfl
  simp only [logUtf8Read, hcount, readUtf8String, show ((5 : UInt64) != u64Max) = true by decide +kernel,
    ↓reduceIte, hspace, show (5 : UInt64).toNat = 5 by decide +kernel, herror]
  rfl

@[irreducible] def logLengthAfter (before : HostStore NearState) (limit : Nat) : HostStore NearState :=
  let paid := Output.paidStore before (applyCharges before.host logLengthCharges).1
  { paid with host := { paid.host with lastError := some (.totalLogLengthExceeded 5 limit) } }

/-- Exact billing and retained credits for the pre-memory length rejection. -/
theorem metered_log_length (extra : Nat) (before : HostStore NearState) (limit rest : Nat)
    (hcount : logCountError before = none) (hlogs : before.host.logs = [])
    (hlimit : before.host.config.maxLogLen = some limit) (hshort : limit < 5)
    (hcredits : before.host.gas.Credits (logLengthCost before.host.extCosts + rest)) :
    (metered extra "log_utf8" logUtf8Fn).invoke before [.i64 5, .i64 1] =
      .Trap (logLengthAfter before limit) (HostError.totalLogLengthExceeded 5 limit).message ∧
    (logLengthAfter before limit).host.gas.burnt = before.host.gas.burnt + logLengthCost before.host.extCosts ∧
    (logLengthAfter before limit).host.gas.promises = before.host.gas.promises ∧
    (logLengthAfter before limit).host.gas.Credits rest := by
  have hc := applyCharges_credits before.host logLengthCharges rest (by simp [logLengthCharges, BurnsOnly])
    (by simpa [logLengthCharges, logLengthCost, burnSum, burnCost] using hcredits)
  have hf := applyCharges_frame before.host logLengthCharges (by simp [logLengthCharges, BurnsOnly])
  have hcfg := congrArg NearState.config hf
  have hl := congrArg NearState.logs hf
  let paid := Output.paidStore before (applyCharges before.host logLengthCharges).1
  have hpaidCfg : paid.host.config = before.host.config := hcfg
  have hpaidLogs : paid.host.logs = [] := hl.trans hlogs
  have hpaidCount : logCountError paid = none := by
    simpa only [logCountError, hpaidCfg, show paid.host.logs = before.host.logs from hl] using hcount
  have hpaidLimit : paid.host.config.maxLogLen = some limit :=
    (congrArg NearConfig.maxLogLen hpaidCfg).trans hlimit
  have hplan : chargesBefore "log_utf8" before [.i64 5, .i64 1] = logLengthCharges := by
    rw [Output.chargesBefore_logUtf8, logLength_read before limit hcount hlogs hlimit hshort]
    rfl
  have hcharge : applyCharges before.host (chargesBefore "log_utf8" before [.i64 5, .i64 1]) =
      ((applyCharges before.host logLengthCharges).1, none) := by
    rw [hplan]
    exact Prod.ext rfl hc.1
  have hi := Output.metered_logUtf8_error extra before 5 1 _ (.totalLogLengthExceeded 5 limit) hcharge (by
    exact congrArg StringRead.result (logLength_read paid limit hpaidCount hpaidLogs hpaidLimit hshort))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [logLengthAfter] using hi
  · simpa [logLengthAfter, Output.paidStore, logLengthCharges, logLengthCost, burnSum, burnCost] using hc.2.1
  · simpa only [logLengthAfter, Output.paidStore] using hc.2.2.1
  · simpa only [logLengthAfter, Output.paidStore] using hc.2.2.2.2

/-- The length-rejecting host through the actual direct-call interpreter rule. -/
theorem wp_call_log_length (cfg : RuntimeConfig) (store : Store NearState) (limits : ExecLimits)
    (code : List Instr) (fuel limit rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn))
    (hcount : logCountError (hostView store) = none) (hlogs : store.host.logs = [])
    (hlimit : store.host.config.maxLogLen = some limit) (hshort : limit < 5)
    (hcredits : store.host.gas.Credits (cfg.wasm.regularOpCost + (logLengthCost store.host.extCosts + rest))) :
    WP cfg.wasm (fuel + 1)
      (.next (atCode store limits #[.i64 5, .i64 1] saveFrame [] (.call 2 :: code)))
      (cfg.wasm.regularOpCost + (logLengthCost store.host.extCosts + rest))
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.totalLogLengthExceeded 5 limit).message)
          (commitCall cfg.wasm store (logLengthAfter (inputBefore cfg.wasm store moduleInstance) limit)) ∧ error = none) := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := StorageCredits.charged store cfg.wasm.regularOpCost (logLengthCost store.host.extCosts + rest) hcredits
  have hm := metered_log_length cfg.fees.numExtraBytesRecord before limit rest hcount hlogs hlimit hshort hc
  apply wp_call_host_trap cfg.wasm fuel (logLengthCost store.host.extCosts) rest store limits []
    [.i64 5, .i64 1] saveFrame [] code 2 2 moduleInstance
    (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) (logLengthAfter before limit)
    (HostError.totalLogLengthExceeded 5 limit).message hmodule rfl hfn rfl hcredits hm.1
    (Nat.le_of_eq hm.2.1) _ hm.2.2.2
  change (logLengthAfter before limit).host.gas.burnt + (logLengthAfter before limit).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises + logLengthCost store.host.extCosts
  rw [hm.2.1, hm.2.2.1, show before.host.extCosts = store.host.extCosts from rfl]
  omega

def logLengthFailureCost (post : HostStore NearState) : Nat := logLengthCost post.host.extCosts

def logLengthFailureSuffix (cfg : RuntimeConfig) (post : HostStore NearState) (rest : Nat) :=
  cfg.wasm.regularOpCost + (2 * cfg.wasm.regularOpCost +
    (cfg.wasm.regularOpCost + (logLengthFailureCost post + rest)))

def logLengthFailureBudget (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) :=
  cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
    (MeteredHosts.Input.cost (successInputBefore cfg store).host +
      (5 * cfg.wasm.regularOpCost + (cfg.wasm.regularOpCost +
        (storageCost + logLengthFailureSuffix cfg post rest)))))

def logLengthFailureStore (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState) (limit : Nat) :=
  commitCall cfg.wasm (successLogBefore cfg store post)
    (logLengthAfter (inputBefore cfg.wasm (successLogBefore cfg store post) moduleInstance) limit)

private theorem saved_prefix_le (costs : ExtCosts) : logLengthCost costs ≤ burnSum costs savedCharges := by
  simp [logLengthCost, savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]

/-- The existing storage frontier retains enough credits for this earlier
failure, including drop, both constants, the log call and its base charge. -/
theorem logLengthFailureSuffix_le_success (cfg : RuntimeConfig) (store : Store NearState)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logLengthFailureSuffix cfg post rest ≤
      (successCosts cfg store post storageCost).storageSuffix cfg.wasm.regularOpCost rest := by
  have hb := saved_prefix_le (successLogBefore cfg store post).host.extCosts
  have hext : (successLogBefore cfg store post).host.extCosts = post.host.extCosts := rfl
  rw [hext] at hb
  simp only [HostCosts.storageSuffix, HostCosts.logBudget, HostCosts.logSuffix, HostCosts.returnBudget,
    successCosts_log, successCosts_returned, logLengthFailureSuffix, logLengthFailureCost, hext]
  omega

theorem logLengthFailureBudget_eq (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) :
    logLengthFailureBudget cfg store post storageCost rest = 12 * cfg.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore cfg store).host + storageCost + logLengthFailureCost post + rest := by
  unfold logLengthFailureBudget logLengthFailureSuffix
  omega

/-- Exact twelve-opcode prefix, with only the existing local storage frontier
and explicit log resource facts as semantic premises. -/
theorem wp_save_log_length (cfg : RuntimeConfig) (store : Store NearState) (postStorage : HostStore NearState)
    (storageCost rest limit : Nat) (written : UInt64) (limits : ExecLimits)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hinputFn : store.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hstorageFn : store.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn))
    (hlogFn : store.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn))
    (hinputLimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hcount : logCountError postStorage = none) (hlogs : postStorage.host.logs = [])
    (hlimit : postStorage.host.config.maxLogLen = some limit) (hshort : limit < 5)
    (hstorage : StorageFrontier cfg store postStorage storageCost rest written)
    (hcredits : store.host.gas.Credits (logLengthFailureBudget cfg store postStorage storageCost rest)) :
    WP cfg.wasm 12 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (logLengthFailureBudget cfg store postStorage storageCost rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host (HostError.totalLogLengthExceeded 5 limit).message) (logLengthFailureStore cfg store postStorage limit) ∧ error = none) := by
  let op := cfg.wasm.regularOpCost
  let logCost := logLengthFailureCost postStorage
  let suffixBudget := logLengthFailureSuffix cfg postStorage rest
  let inputRest := 5 * op + (op + (storageCost + suffixBudget))
  let suffix := module.funcs[0]!.body.drop 12
  let finalPost : Post := fun remaining final error => remaining = rest ∧ final =
    .trap (.host (HostError.totalLogLengthExceeded 5 limit).message) (logLengthFailureStore cfg store postStorage limit) ∧ error = none
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
    hstorage.credits.mono (logLengthFailureSuffix_le_success cfg store postStorage storageCost rest)
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
    have ht := wp_call_log_length cfg (successLogBefore cfg store postStorage) limits suffix 0 limit rest
      (by rw [hlogenv.2]; exact hmodule) (by rw [hlogenv.1]; exact hlogFn) hcount hlogs hlimit hshort hlog
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
  simpa [logLengthFailureBudget, logLengthFailureSuffix, finalPost, suffix, module, u64Max, op, logCost, suffixBudget,
    inputRest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody


/-- The length failure installs its own marker and appends no logs. -/
theorem logLength_fields (before : HostStore NearState) (limit : Nat) :
    (logLengthAfter before limit).host.lastError = some (.totalLogLengthExceeded 5 limit) ∧
    (logLengthAfter before limit).host.lastExecutionIssue = before.host.lastExecutionIssue ∧
    (logLengthAfter before limit).host.logs = before.host.logs := by
  have hf := applyCharges_frame before.host logLengthCharges (by simp [logLengthCharges, BurnsOnly])
  have hi := congrArg NearState.lastExecutionIssue hf
  have hl := congrArg NearState.logs hf
  exact ⟨by unfold logLengthAfter; rfl, by simpa only [logLengthAfter, Output.paidStore] using hi,
    by simpa only [logLengthAfter, Output.paidStore] using hl⟩

/-- Only storage's local frame is needed to recover the original fresh issue
marker and empty logs at the failed log host. -/
theorem logLengthFailureStore_fields (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState) (limit : Nat) :
    (logLengthFailureStore cfg store post limit).host.lastError = some (.totalLogLengthExceeded 5 limit) ∧
    (logLengthFailureStore cfg store post limit).host.lastExecutionIssue = post.host.lastExecutionIssue ∧
    (logLengthFailureStore cfg store post limit).host.logs = post.host.logs := by
  have hf := logLength_fields (inputBefore cfg.wasm (successLogBefore cfg store post) moduleInstance) limit
  simpa only [logLengthFailureStore, commitCall_host, inputBefore, chargedStore, chargeHost, successLogBefore,
    chargedMany] using hf

def logLengthFailureAttemptBudget (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) :=
  burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + logLengthFailureBudget ctx.protocol
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post storageCost rest)

/-- Startup reaches the proved prefix; no execution equation is a premise. -/
theorem runAttempt_save_log_length (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (fuel : Nat)
    (hp : PreparationLimits ctx.protocol) (hfuel : 12 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hcount : logCountError post = none) (hlogs : post.host.logs = [])
    (hlimit : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logLengthFailureAttemptBudget ctx raw post storageCost rest)) :
    runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel =
      outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.trap (.host (HostError.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength).message)
          (logLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength)) none := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := logLengthFailureBudget cfg (executionStore cfg vm raw) post storageCost rest
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
  have hw := wp_save_log_length cfg (executionStore cfg vm raw) post storageCost rest ctx.protocol.wasm.limits.maxTotalLogLength written execLimits
    (by rfl) (by rfl) (by rfl) (by rfl) hi hcount hlogs hlimit hshort hstorage ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hr : runMetered cfg.wasm 12 (.next (entryConfig cfg (executionActive cfg vm raw))) =
      (.trap (.host (HostError.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength).message)
        (logLengthFailureStore cfg (executionStore cfg vm raw) post ctx.protocol.wasm.limits.maxTotalLogLength), none) := Prod.ext hpost.2.1 hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 12
    (.next (entryConfig cfg (executionActive cfg vm raw))) (by rw [hr]; simp) (fuel - 12)
  rw [show 12 + (fuel - 12) = fuel by omega] at hextra
  have hrun := hextra.trans hr
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg vm raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

def logLengthFailureOutcome (ctx : Context) (raw : Storage) (post : HostStore NearState) : VMOutcome :=
  outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.trap (.host (HostError.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength).message)
      (logLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength)) none

/-- The local storage frame propagates actual initial fresh markers and logs. -/
theorem logLengthFailureOutcome_fields (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post) :
    (logLengthFailureOutcome ctx raw post).aborted = some (.hostError (.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength)) ∧
    (logLengthFailureOutcome ctx raw post).logs = [] ∧ (logLengthFailureOutcome ctx raw post).receiptsValid = true := by
  have hf := logLengthFailureStore_fields ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength
  have hi := (StorageFrame.Frame.lastExecutionIssue hframe).trans
    (storageInput_lastExecutionIssue ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hl := (StorageFrame.Frame.logs hframe).trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have he : (logLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength).host.lastError =
      some (.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength) := hf.1
  have hissue := hf.2.1.trans hi
  have hlogs := hf.2.2.trans hl
  change (logLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength).host.lastExecutionIssue = none at hissue
  change (logLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post ctx.protocol.wasm.limits.maxTotalLogLength).host.logs = [] at hlogs
  simp [logLengthFailureOutcome, outcomeOfExecution, StepResult.host, trapError, he, hissue, hlogs,
    logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- The public VM's receipt check preserves the classified log failure. -/
theorem run_save_log_length_public (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hcount : logCountError post = none) (hlogs : post.host.logs = [])
    (hlimit : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logLengthFailureAttemptBudget ctx raw post storageCost rest)) :
    run ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw = logLengthFailureOutcome ctx raw post := by
  have hr := runAttempt_save_log_length ctx raw post storageCost rest written
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hp
    (Nat.le_trans (by decide : 12 ≤ 16) (fuelFor_save _ _)) hinput hcount hlogs hlimit hshort hstorage hcredits
  simp only [run, hr]
  change (logLengthFailureOutcome ctx raw post).checkReceipts _ _ _ = _
  simp only [VMOutcome.checkReceipts, (logLengthFailureOutcome_fields ctx raw post hframe).2.2, ↓reduceIte]


/-- The independent model rejects the total log length after its earlier checks. -/
theorem modelStep_log_length (ctx : Context) (st : Option Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5) :
    modelStep ctx st () = .error ⟨.panic (.other
      (HostError.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength).message), []⟩ := by
  simp [modelStep, Nat.not_lt.mpr hinput, Nat.not_lt.mpr hkey,
    Nat.not_lt.mpr hvalue, Nat.ne_of_gt hcount, hshort]

/-- Actual public execution matches the independent log-length rejection.
The only execution frontier is the local storage call, with its frame and credits. -/
theorem execOn_matches_log_length
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcountpos : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logLengthFailureAttemptBudget ctx raw post storageCost rest)) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hc := (StorageFrame.Frame.config hframe).trans
    (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hn := congrArg NearConfig.maxNumberLogs hc
  have hlimit := congrArg NearConfig.maxLogLen hc
  have hnum : post.host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlen : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hlimit
  have hl := (StorageFrame.Frame.logs hframe).trans
    (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hlogs : post.host.logs = [] := hl
  have hcount : logCountError post = none := by
    simp [logCountError, hnum, hlogs, Nat.not_le.mpr hcountpos]
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) (modelStep ctx st ())
  rw [modelStep_log_length ctx st hinput hkey hvalue hcountpos hshort]
  have hr := run_save_log_length_public ctx raw post storageCost rest written hp hinput
    hcount hlogs hlen hshort hstorage hframe hcredits
  have hf := logLengthFailureOutcome_fields ctx raw post hframe
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength), hf.1, rfl, hf.2.1⟩

theorem logLengthFailureAttemptBudget_eq (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) :
    logLengthFailureAttemptBudget ctx raw post storageCost rest =
      burnSum ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts (loadingCharges 0) +
      20 * ctx.protocol.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host +
      storageCost + logLengthFailureCost post + rest := by
  unfold logLengthFailureAttemptBudget
  rw [logLengthFailureBudget_eq]
  omega

end WNear.Skeleton
