import Skeleton.LogLengthFailure

/-!
# Return-length rejection after the completed write and `saved` log

The actual host trap string is `value_return: return size exceeded`. Its
`returnedValueLengthExceeded` marker supplies the structured boundary error.
Input, logging and return are proved from host contracts; storage remains the
one explicit local frontier. The budget is `executionBudget`: loading plus
23 regular operations, input/write/log/return host charges and retained credits.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

@[irreducible] def returnLengthAfter (cfg : WasmConfig) (store : Store NearState)
    (bytes : List UInt8) (limit : Nat) : HostStore NearState :=
  let before := inputBefore cfg store moduleInstance
  let paid := Output.paidStore before (applyCharges before.host (returnCharges cfg store)).1
  { paid with host := { paid.host with lastError := some (.returnedValueLengthExceeded bytes.length limit) } }

/-- Exact actual return charges are paid even though the return is rejected. -/
theorem metered_return_length (cfg : RuntimeConfig) (store : Store NearState)
    (bytes : List UInt8) (limit rest : Nat)
    (hregister : store.host.registers 0 = some bytes)
    (hlimit : store.host.config.maxReturnLen = some limit) (hshort : limit < bytes.length)
    (hcredits : (inputBefore cfg.wasm store moduleInstance).host.gas.Credits
      (returnCost cfg.wasm store + rest)) :
    (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).invoke
      (inputBefore cfg.wasm store moduleInstance) [.i64 u64Max, .i64 0] =
      .Trap (returnLengthAfter cfg.wasm store bytes limit) "value_return: return size exceeded" ∧
    (returnLengthAfter cfg.wasm store bytes limit).host.gas.burnt =
      (inputBefore cfg.wasm store moduleInstance).host.gas.burnt + returnCost cfg.wasm store ∧
    (returnLengthAfter cfg.wasm store bytes limit).host.gas.promises =
      (inputBefore cfg.wasm store moduleInstance).host.gas.promises ∧
    (returnLengthAfter cfg.wasm store bytes limit).host.gas.Credits rest := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := applyCharges_credits before.host (returnCharges cfg.wasm store) rest
    (Output.valueReturn_burnsOnly before u64Max 0) hcredits
  have hf := applyCharges_frame before.host (returnCharges cfg.wasm store)
    (Output.valueReturn_burnsOnly before u64Max 0)
  have hr := congrArg (fun h : NearState => h.registers 0) hf
  have hl := congrArg (fun h : NearState => h.config.maxReturnLen) hf
  have hi := Output.metered_valueReturn_length_error cfg.fees.numExtraBytesRecord before u64Max 0
    (applyCharges before.host (returnCharges cfg.wasm store)).1 bytes limit
    (Prod.ext rfl hc.1) (by
      simp only [getMemOrReg, ↓reduceIte, Output.paidStore]
      exact hr.trans hregister) (hl.trans hlimit) hshort
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [returnLengthAfter] using hi
  · simpa only [returnLengthAfter, Output.paidStore, returnCost, before, inputBefore, chargedStore, chargeHost] using hc.2.1
  · simpa only [returnLengthAfter, Output.paidStore] using hc.2.2.1
  · simpa only [returnLengthAfter, Output.paidStore] using hc.2.2.2.2

theorem wp_call_return_length (cfg : RuntimeConfig) (store : Store NearState)
    (limits : ExecLimits) (bytes : List UInt8) (limit rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[3]? = some (.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn))
    (hregister : store.host.registers 0 = some bytes)
    (hlimit : store.host.config.maxReturnLen = some limit) (hshort : limit < bytes.length)
    (hcredits : store.host.gas.Credits (cfg.wasm.regularOpCost + (returnCost cfg.wasm store + rest))) :
    WP cfg.wasm 1 (.next (atCode store limits #[.i64 u64Max, .i64 0] saveFrame [] [.call 3]))
      (cfg.wasm.regularOpCost + (returnCost cfg.wasm store + rest))
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host "value_return: return size exceeded")
          (commitCall cfg.wasm store (returnLengthAfter cfg.wasm store bytes limit)) ∧ error = none) := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := StorageCredits.charged store cfg.wasm.regularOpCost _ hcredits
  have hm := metered_return_length cfg store bytes limit rest hregister hlimit hshort hc
  apply wp_call_host_trap cfg.wasm 0 (returnCost cfg.wasm store) rest store limits []
    [.i64 u64Max, .i64 0] saveFrame [] [] 3 3 moduleInstance
    (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn)
    (returnLengthAfter cfg.wasm store bytes limit) "value_return: return size exceeded"
    hmodule rfl hfn rfl hcredits hm.1 (Nat.le_of_eq hm.2.1) _ hm.2.2.2
  change (returnLengthAfter cfg.wasm store bytes limit).host.gas.burnt +
    (returnLengthAfter cfg.wasm store bytes limit).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises + returnCost cfg.wasm store
  rw [hm.2.1, hm.2.2.1]
  dsimp only [before]
  omega

private theorem returnLength_wp_evidence (cfg : WasmConfig) (fuel cost rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (args results : List Value)
    (code : List Instr) (index : Nat) (fn : NearHostFn NearState) (after : HostStore NearState)
    (e : CallEvidence cfg store index args results fn after cost rest)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (cost + rest))) (post : Post)
    (hnext : WP cfg fuel
      (.next (atCode (commitCall cfg store after) limits results.toArray saveFrame [] code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits args.toArray saveFrame [] (.call index :: code)))
      (cfg.regularOpCost + (cost + rest)) post := by
  exact wp_call_host cfg fuel cost rest store limits [] args results saveFrame [] code
    index index moduleInstance fn after e.module e.address e.function e.arity hcredits
    e.invoke e.burnt e.used e.credits post hnext

/-- Composition through the final direct call, whose local trap WP is explicit. -/
theorem wp_save_body_return_trap (cfg : RuntimeConfig) (rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (cost : HostCosts) (result : HostResults) (written : UInt64) (failed : Store NearState)
    (hcredits : store.host.gas.Credits (cost.bodyBudget cfg.wasm.regularOpCost rest))
    (hinput : CallEvidence cfg.wasm (result.beforeInput cfg.wasm store) 0 [.i64 0] []
      (metered cfg.fees.numExtraBytesRecord "input" inputFn) result.input
      cost.input (cost.inputSuffix cfg.wasm.regularOpCost rest))
    (hstorage : CallEvidence cfg.wasm (result.beforeStorage cfg.wasm store) 1
      [.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max] [.i64 written]
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) result.storage
      cost.storage (cost.storageSuffix cfg.wasm.regularOpCost rest))
    (hlog : CallEvidence cfg.wasm (result.beforeLog cfg.wasm store) 2 [.i64 5, .i64 1] []
      (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) result.log
      cost.log (cost.logSuffix cfg.wasm.regularOpCost rest))
    (hreturn : WP cfg.wasm 1
      (.next (atCode (result.beforeReturn cfg.wasm store) limits #[.i64 u64Max, .i64 0] saveFrame [] [.call 3]))
      (cost.returnBudget cfg.wasm.regularOpCost rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host "value_return: return size exceeded") failed ∧ error = none)) :
    WP cfg.wasm 15 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (cost.bodyBudget cfg.wasm.regularOpCost rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host "value_return: return size exceeded") failed ∧ error = none) := by
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .trap (.host "value_return: return size exceeded") failed ∧ error = none
  have hlogCredits : (result.beforeLog cfg.wasm store).host.gas.Credits
      (cost.logBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    apply StorageCredits.charged
    simpa [HostResults.afterStorage, HostCosts.storageSuffix] using hstorage.credits
  have hstorageCredits : (result.beforeStorage cfg.wasm store).host.gas.Credits
      (cost.storageBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    simpa [HostResults.afterInput, HostCosts.inputSuffix] using hinput.credits
  have hinputCredits : (result.beforeInput cfg.wasm store).host.gas.Credits
      (cost.inputBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    simpa [HostCosts.bodyBudget] using hcredits
  have hret := hreturn
  have hretConsts := wp_i64_consts cfg.wasm 1 (cost.returnBudget cfg.wasm.regularOpCost rest)
    (result.afterLog cfg.wasm store) limits [] saveFrame [] [.call 3] [u64Max, 0] post
    (by simpa [HostCosts.logSuffix, HostResults.afterLog] using hlog.credits) hret
  have hlogCall := returnLength_wp_evidence cfg.wasm 3 cost.log (cost.logSuffix cfg.wasm.regularOpCost rest)
    _ limits _ _ ([.i64_const u64Max, .i64_const 0, .call 3]) 2 _ _ hlog
    hlogCredits post hretConsts
  have hlogConsts := wp_i64_consts cfg.wasm 4 (cost.logBudget cfg.wasm.regularOpCost rest)
    (result.afterDrop cfg.wasm store) limits [] saveFrame []
    [.call 2, .i64_const u64Max, .i64_const 0, .call 3] [5, 1] post
    (by
      apply StorageCredits.charged
      simpa [HostCosts.storageSuffix, HostResults.afterStorage] using hstorage.credits) hlogCall
  have hdrop := wp_drop cfg.wasm 6 (2 * cfg.wasm.regularOpCost +
      cost.logBudget cfg.wasm.regularOpCost rest) (result.afterStorage cfg.wasm store) limits
    #[] saveFrame [] [.i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    (.i64 written) post
    (by simpa [HostCosts.storageSuffix, HostResults.afterStorage] using hstorage.credits) hlogConsts
  have hstorageCall := returnLength_wp_evidence cfg.wasm 7 cost.storage
    (cost.storageSuffix cfg.wasm.regularOpCost rest) _ limits _ _
    [.drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    1 _ _ hstorage hstorageCredits post hdrop
  have hstorageConsts := wp_i64_consts cfg.wasm 8
    (cost.storageBudget cfg.wasm.regularOpCost rest) (result.afterInput cfg.wasm store)
    limits [] saveFrame []
    [.call 1, .drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    [1, 0, u64Max, 0, u64Max] post
    (by simpa [HostCosts.inputSuffix, HostResults.afterInput] using hinput.credits) hstorageCall
  have hinputCall := returnLength_wp_evidence cfg.wasm 13 cost.input
    (cost.inputSuffix cfg.wasm.regularOpCost rest) _ limits _ _
    [.i64_const 1, .i64_const 0, .i64_const u64Max, .i64_const 0, .i64_const u64Max, .call 1, .drop,
      .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    0 _ _ hinput hinputCredits post hstorageConsts
  have hbody := wp_i64_consts cfg.wasm 14 (cost.inputBudget cfg.wasm.regularOpCost rest)
    store limits [] saveFrame []
    [.call 0, .i64_const 1, .i64_const 0, .i64_const u64Max, .i64_const 0, .i64_const u64Max,
      .call 1, .drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    [0] post (by simpa [HostCosts.bodyBudget] using hcredits) hinputCall
  simpa [HostCosts.bodyBudget, post, module, u64Max] using hbody


@[irreducible] def returnLengthFailureStore (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (limit : Nat) :=
  commitCall cfg.wasm (successReturnBefore cfg store storage)
    (returnLengthAfter cfg.wasm (successReturnBefore cfg store storage) store.host.context.input limit)

theorem wp_save_return_length (cfg : RuntimeConfig) (host : NearState) (pages : Nat) (max : Option Nat)
    (storage : HostStore NearState) (storageCost rest limit : Nat) (written : UInt64) (limits : ExecLimits)
    (hpages : 0 < pages)
    (hinputLimit : withinLimit host.config.maxRegisterLen host.context.input.length = true)
    (hmemory : storage.mem = dataMemory pages max)
    (hregister : storage.host.registers 0 = some host.context.input)
    (hreturnLimit : storage.host.config.maxReturnLen = some limit)
    (hshort : limit < host.context.input.length)
    (hcount : logCountError storage = none)
    (hspace : 5 ≤ logSpace storage)
    (hreadCost : storage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, storage.host.config.maxLogLen = some limit → totalLogLength storage + 5 ≤ limit)
    (hcredits : host.gas.Credits
      (successBudget cfg (initializedStore cfg host (dataMemory pages max)) storage storageCost rest))
    (hstorage : StorageFrontier cfg (initializedStore cfg host (dataMemory pages max))
      storage storageCost rest written) :
    WP cfg.wasm 15
      (.next (atCode (initializedStore cfg host (dataMemory pages max)) limits #[]
        saveFrame [] module.funcs[0]!.body))
      (successBudget cfg (initializedStore cfg host (dataMemory pages max)) storage storageCost rest)
      (fun remaining final error => remaining = rest ∧ final = .trap (.host "value_return: return size exceeded")
        (returnLengthFailureStore cfg (initializedStore cfg host (dataMemory pages max)) storage limit) ∧ error = none) := by
  let store := initializedStore cfg host (dataMemory pages max)
  let result := successResults cfg store storage
  let cost := successCosts cfg store storage storageCost
  have hhost : store.host = host := rfl
  have hc : store.host.gas.Credits (cost.bodyBudget cfg.wasm.regularOpCost rest) := by
    rw [successBudget_eq]
    exact hcredits
  have hlookup (stage : Store NearState) (hstage : stage ∈ bodyStages result cfg.wasm store) :=
    body_initialized_lookups cfg host (dataMemory pages max) result stage hstage
  have hinputLookup := hlookup (result.beforeInput cfg.wasm store) (by simp [bodyStages])
  have hstorageLookup := hlookup (result.beforeStorage cfg.wasm store) (by simp [bodyStages])
  have hlogLookup := hlookup (result.beforeLog cfg.wasm store) (by simp [bodyStages])
  have hreturnLookup := hlookup (result.beforeReturn cfg.wasm store) (by simp [bodyStages])
  simp only [result, successResults_beforeInput] at hinputLookup
  simp only [result, successResults_beforeStorage] at hstorageLookup
  simp only [result, successResults_beforeLog] at hlogLookup
  simp only [result, successResults_beforeReturn] at hreturnLookup
  have hic : (successInputBefore cfg store).host.gas.Credits
      (cost.inputBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    simpa [HostCosts.bodyBudget] using hc
  have hi := input_evidence cfg (successInputBefore cfg store)
    (cost.inputSuffix cfg.wasm.regularOpCost rest) hinputLookup.1 hinputLookup.2.1 hinputLimit
    (by simpa only [HostCosts.inputBudget, cost, successCosts_input, successInputAfter] using hic)
  have hs := storage_evidence cfg store storage storageCost rest written
    hstorageLookup.1 hstorageLookup.2.2.1 hstorage
  have hlc : (successLogBefore cfg store storage).host.gas.Credits
      (cost.logBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    apply StorageCredits.charged
    simpa [HostCosts.storageSuffix] using hstorage.credits
  have hl := log_evidence cfg (successLogBefore cfg store storage) pages max
    (cost.logSuffix cfg.wasm.regularOpCost rest) hlogLookup.1 hlogLookup.2.2.2.1 hpages
    (by rw [successLog_memory]; exact congrArg some hmemory) hcount hspace hreadCost hpush
    (by simpa only [HostCosts.logBudget, cost, successCosts_log] using hlc)
  have hrc : (successReturnBefore cfg store storage).host.gas.Credits
      (cost.returnBudget cfg.wasm.regularOpCost rest) := by
    apply StorageCredits.chargedMany
    simpa [HostCosts.logSuffix, HostResults.afterLog, result, successResults,
      successLogAfter, cost, successCosts_log] using hl.credits
  have hr := wp_call_return_length cfg (successReturnBefore cfg store storage) limits host.context.input limit rest
    hreturnLookup.1 hreturnLookup.2.2.2.2
    (by rw [successReturn_register]; exact hregister)
    (by rw [successReturn_config]; exact hreturnLimit) hshort
    (by simpa only [HostCosts.returnBudget, cost, successCosts_returned, hhost] using hrc)
  have hbody : WP cfg.wasm 15 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (cost.bodyBudget cfg.wasm.regularOpCost rest)
      (fun remaining final error => remaining = rest ∧
        final = .trap (.host "value_return: return size exceeded")
          (returnLengthFailureStore cfg store storage limit) ∧ error = none) := by
    apply wp_save_body_return_trap cfg rest store limits cost result written _ hc
    · simpa only [result, successResults_beforeInput, successResults_input, cost, successCosts_input, successInputAfter] using hi
    · simpa only [result, successResults_beforeStorage, successResults_storage] using hs
    · simpa only [result, successResults_beforeLog, successResults_log, successLogAfter, cost, successCosts_log] using hl
    · simpa only [result, successResults_beforeReturn, cost, successCosts_returned, HostCosts.returnBudget, hhost, returnLengthFailureStore] using hr
  simpa only [cost, successBudget_eq, store, result] using hbody

theorem runAttempt_save_return_length (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState)
    (storageCost rest limit : Nat) (written : UInt64) (fuel : Nat)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hfuel : 15 ≤ fuel)
    (hinputLimit : withinLimit (ctx.toNearState cfg raw).config.maxRegisterLen ctx.input.length = true)
    (hmemory : postStorage.mem = preparedData cfg)
    (hregister : postStorage.host.registers 0 = some ctx.input)
    (hreturnLimit : postStorage.host.config.maxReturnLen = some limit)
    (hshort : limit < ctx.input.length)
    (hcount : logCountError postStorage = none)
    (hspace : 5 ≤ logSpace postStorage)
    (hreadCost : postStorage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, postStorage.host.config.maxLogLen = some limit →
      totalLogLength postStorage + 5 ≤ limit)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits
      (executionBudget cfg ctx raw postStorage storageCost rest))
    (hstorage : StorageFrontier cfg (executionStore cfg ctx raw)
      postStorage storageCost rest written) :
    runAttempt cfg module 0 "save" ctx raw fuel =
      outcomeOfExecution ctx raw (.trap (.host "value_return: return size exceeded")
      (returnLengthFailureStore cfg (executionStore cfg ctx raw) postStorage limit)) none := by
  let budget := successBudget cfg (executionStore cfg ctx raw) postStorage storageCost rest
  have hs : runAttempt cfg module 0 "save" ctx raw fuel =
      (let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg (executionLoaded cfg ctx raw)))
       outcomeOfExecution ctx raw result.1 result.2) ∧
      (executionLoaded cfg ctx raw).gas.Credits (8 * cfg.wasm.regularOpCost + budget) := by
    simpa only [executionLoaded] using runAttempt_save_credits cfg ctx raw fuel
      (8 * cfg.wasm.regularOpCost + budget) hpositive hminmax hmax htypes hfunctions hcredits
  have ha : (executionActive cfg ctx raw).gas.Credits budget := by
    have hc := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
      (8 * cfg.wasm.regularOpCost) budget hs.2
    simpa only [executionActive, chargeHost] using hc.2.2.2
  have hw := wp_save_return_length cfg (executionActive cfg ctx raw) cfg.wasm.limits.initialMemoryPages
    (some cfg.wasm.limits.maxMemoryPages) postStorage storageCost rest limit written execLimits hpositive
    (by rw [executionActive_config, executionActive_input]; exact hinputLimit) hmemory
    (by rw [executionActive_input]; exact hregister)
    hreturnLimit (by rw [executionActive_input]; exact hshort) hcount hspace hreadCost hpush ha hstorage
  obtain ⟨remaining, hpost, _⟩ := hw.result
  have hrun15 : runMetered cfg.wasm 15 (.next (entryConfig cfg (executionActive cfg ctx raw))) =
      (.trap (.host "value_return: return size exceeded")
        (returnLengthFailureStore cfg (executionStore cfg ctx raw) postStorage limit), none) := by
    apply Prod.ext
    · simpa only [executionStore, entryConfig, preparedData] using hpost.2.1
    · exact hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 15
    (.next (entryConfig cfg (executionActive cfg ctx raw)))
    (by rw [hrun15]; simp) (fuel - 15)
  have hrun : runMetered cfg.wasm fuel (.next (entryConfig cfg (executionActive cfg ctx raw))) =
      (.trap (.host "value_return: return size exceeded")
        (returnLengthFailureStore cfg (executionStore cfg ctx raw) postStorage limit), none) := by
    rw [show 15 + (fuel - 15) = fuel by omega] at hextra
    exact hextra.trans hrun15
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg ctx raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

theorem returnLengthAfter_fields (cfg : WasmConfig) (store : Store NearState)
    (bytes : List UInt8) (limit : Nat) :
    (returnLengthAfter cfg store bytes limit).host.lastError = some (.returnedValueLengthExceeded bytes.length limit) ∧
    (returnLengthAfter cfg store bytes limit).host.lastExecutionIssue = store.host.lastExecutionIssue ∧
    (returnLengthAfter cfg store bytes limit).host.logs = store.host.logs := by
  have hf := applyCharges_frame (inputBefore cfg store moduleInstance).host (returnCharges cfg store)
    (Output.valueReturn_burnsOnly _ u64Max 0)
  have hi := congrArg NearState.lastExecutionIssue hf
  have hl := congrArg NearState.logs hf
  exact ⟨by unfold returnLengthAfter; rfl,
    by simpa only [returnLengthAfter, Output.paidStore, inputBefore, chargedStore, chargeHost] using hi,
    by simpa only [returnLengthAfter, Output.paidStore, inputBefore, chargedStore, chargeHost] using hl⟩

/-- The trap keeps the completed `saved` log and its structured error marker. -/
theorem returnLengthFailureStore_fields (cfg : RuntimeConfig) (store : Store NearState)
    (post : HostStore NearState) (limit : Nat) :
    (returnLengthFailureStore cfg store post limit).host.lastError =
      some (.returnedValueLengthExceeded store.host.context.input.length limit) ∧
    (returnLengthFailureStore cfg store post limit).host.lastExecutionIssue = post.host.lastExecutionIssue ∧
    (returnLengthFailureStore cfg store post limit).host.logs = post.host.logs ++ ["saved".toUTF8.toList] := by
  have hr := returnLengthAfter_fields cfg.wasm (successReturnBefore cfg store post) store.host.context.input limit
  have hf := applyCharges_frame (inputBefore cfg.wasm (successLogBefore cfg store post) moduleInstance).host
    savedCharges (by
      simp only [savedCharges, extCharges, List.mem_map]
      rintro _ ⟨_, _, rfl⟩
      trivial)
  have hi := congrArg NearState.lastExecutionIssue hf
  have hl := congrArg NearState.logs hf
  refine ⟨by simpa only [returnLengthFailureStore, commitCall_host] using hr.1, ?_, ?_⟩
  · rw [show (returnLengthFailureStore cfg store post limit).host.lastExecutionIssue =
      (successReturnBefore cfg store post).host.lastExecutionIssue from by simpa only [returnLengthFailureStore, commitCall_host] using hr.2.1]
    simpa only [successReturnBefore, chargedMany, chargedStore, chargeHost, commitCall_host,
      successLogAfter, savedAfter, Output.paidStore, inputBefore, successLogBefore] using hi
  · rw [show (returnLengthFailureStore cfg store post limit).host.logs =
      (successReturnBefore cfg store post).host.logs from by simpa only [returnLengthFailureStore, commitCall_host] using hr.2.2]
    simpa only [successReturnBefore, chargedMany, chargedStore, chargeHost, commitCall_host,
      successLogAfter, savedAfter, Output.paidStore, inputBefore, successLogBefore] using
      congrArg (fun logs => logs ++ ["saved".toUTF8.toList]) hl


def returnLengthFailureOutcome (ctx : Context) (raw : Storage) (post : HostStore NearState) : VMOutcome :=
  outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.trap (.host "value_return: return size exceeded")
      (returnLengthFailureStore ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post
        ctx.protocol.wasm.limits.maxLengthReturnedData)) none

/-- Actual fresh markers classify the raw trap as the protocol return-length
error, while the previously emitted log remains observable. -/
theorem returnLengthFailureOutcome_fields (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post) :
    (returnLengthFailureOutcome ctx raw post).aborted =
      some (.hostError (.returnedValueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthReturnedData)) ∧
    (returnLengthFailureOutcome ctx raw post).logs = ["saved"] ∧
    (returnLengthFailureOutcome ctx raw post).receiptsValid = true := by
  have hf := returnLengthFailureStore_fields ctx.protocol
    (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post
    ctx.protocol.wasm.limits.maxLengthReturnedData
  have hi := (StorageFrame.Frame.lastExecutionIssue hframe).trans
    (storageInput_lastExecutionIssue ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hl := (StorageFrame.Frame.logs hframe).trans
    (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have he := hf.1
  have hinput : (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.context.input = ctx.args :=
    executionActive_input _ _ _
  rw [hinput] at he
  have hissue := hf.2.1.trans hi
  have hlogs := hf.2.2.trans (congrArg (fun logs => logs ++ ["saved".toUTF8.toList]) hl)
  change (returnLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post _).host.lastExecutionIssue = none at hissue
  change (returnLengthFailureStore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post _).host.logs = ["saved".toUTF8.toList] at hlogs
  simp [returnLengthFailureOutcome, outcomeOfExecution, StepResult.host, trapError, he, hissue, hlogs,
    logsOf, VMOutcome.receiptsValid, receiptsValidFrom]
  decide +kernel

/-- The public VM preserves the classified error and the emitted log. -/
theorem run_save_return_length_public (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hmemory : post.mem = preparedData ctx.protocol)
    (hregister : post.host.registers 0 = some ctx.args)
    (hreturnLimit : post.host.config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hcount : logCountError post = none) (hspace : 5 ≤ logSpace post)
    (hreadCost : post.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, post.host.config.maxLogLen = some limit → totalLogLength post + 5 ≤ limit)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest)) :
    run ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw = returnLengthFailureOutcome ctx raw post := by
  have hr := runAttempt_save_return_length ctx.protocol (Near.Boundary.toVMContext ctx) raw post
    storageCost rest ctx.protocol.wasm.limits.maxLengthReturnedData written
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hp.positive hp.minmax hp.maximum hp.types hp.functions
    (Nat.le_trans (by decide : 15 ≤ 16) (fuelFor_save _ _))
    (by change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
        simpa [withinLimit] using hinput)
    hmemory hregister hreturnLimit hshort hcount hspace hreadCost hpush hcredits hstorage
  simp only [run, hr]
  change (returnLengthFailureOutcome ctx raw post).checkReceipts _ _ _ = _
  simp only [VMOutcome.checkReceipts, (returnLengthFailureOutcome_fields ctx raw post hframe).2.2, ↓reduceIte]

/-- Model rejection agrees with the structured marker, rather than the raw host trap string. -/
theorem modelStep_return_length (ctx : Context) (st : Option Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hlogs : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length) :
    modelStep ctx st () = .error ⟨.panic (.other
      (HostError.returnedValueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthReturnedData).message), ["saved"]⟩ := by
  simp [modelStep, Nat.not_lt.mpr hinput, Nat.not_lt.mpr hkey, Nat.not_lt.mpr hvalue,
    Nat.ne_of_gt hcount, Nat.not_lt.mpr hlogs, hshort]

/-- Public receipt-level refinement for the deterministic return rejection.
Only storage remains a local host frontier. Its frame derives all post-write
resource facts from the original protocol and fresh runtime state. -/
theorem execOn_matches_return_length
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcountpos : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hreadCost : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).extCosts.cost
      "read_memory_byte" * 5 < 2 ^ 64)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest)) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hcfg := (StorageFrame.Frame.config hframe).trans
    (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hn := congrArg NearConfig.maxNumberLogs hcfg
  have hl := congrArg NearConfig.maxLogLen hcfg
  have hr := congrArg NearConfig.maxReturnLen hcfg
  have hnum : post.host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlen : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hl
  have hreturn : post.host.config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := hr
  have hlogs : post.host.logs = [] := (StorageFrame.Frame.logs hframe).trans
    (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hcount : logCountError post = none := by
    simp [logCountError, hnum, hlogs, Nat.not_le.mpr hcountpos]
  have hspace : 5 ≤ logSpace post := by
    simpa [logSpace, totalLogLength, hlogs, hlen] using hloglen
  have hpush : ∀ limit, post.host.config.maxLogLen = some limit → totalLogLength post + 5 ≤ limit := by
    intro limit he
    have heq : ctx.protocol.wasm.limits.maxTotalLogLength = limit := Option.some.inj (hlen.symm.trans he)
    simpa [totalLogLength, hlogs, ← heq] using hloglen
  have hmem := hframe.1.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hreg := (congrFun (StorageFrame.Frame.registers hframe) 0).trans
    (storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hext := (StorageFrame.Frame.extCosts hframe).trans
    (storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hread : post.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64 := by
    rw [hext]
    exact hreadCost
  change Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) (modelStep ctx st ())
  rw [modelStep_return_length ctx st hinput hkey hvalue hcountpos hloglen hshort]
  have hrun := run_save_return_length_public ctx raw post storageCost rest written hp hinput
    hmem hreg hreturn hshort hcount hspace hread hpush hstorage hframe hcredits
  have hf := returnLengthFailureOutcome_fields ctx raw post hframe
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hrun]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.returnedValueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthReturnedData),
    hf.1, rfl, hf.2.1⟩

end WNear.Skeleton
