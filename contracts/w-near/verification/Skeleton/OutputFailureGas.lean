import Skeleton.SuccessCost
import Skeleton.LogLengthFailure
import Skeleton.ReturnLengthFailure

/-! Gas bounds for actual output failures, including loading and activation. -/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem startup_credits_and_burnt (cfg : RuntimeConfig) (vm : VMContext)
    (raw : Storage) (budget : Nat)
    (hcredits : (vm.toNearState cfg raw).gas.Credits
      (burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
        (8 * cfg.wasm.regularOpCost + budget))) :
    (executionActive cfg vm raw).gas.Credits budget ∧
    (executionActive cfg vm raw).gas.burnt =
      burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) + 8 * cfg.wasm.regularOpCost := by
  have hl := applyCharges_credits (vm.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + budget) (by simp [loadingCharges, BurnsOnly]) hcredits
  have hload : (executionLoaded cfg vm raw).gas.burnt =
      burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) := by
    simpa only [executionLoaded, VMContext.toNearState, Nat.zero_add] using hl.2.1
  have ha := GasCounter.burn_credits (executionLoaded cfg vm raw).gas
    (8 * cfg.wasm.regularOpCost) budget (by simpa only [executionLoaded] using hl.2.2.2.2)
  refine ⟨by simpa only [executionActive, chargeHost] using ha.2.2.2, ?_⟩
  simpa only [executionActive, chargeHost, hload] using ha.2.1

private theorem active_input_limit (ctx : Context) (raw : Storage)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize) :
    withinLimit (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.config.maxRegisterLen
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.context.input.length = true := by
  simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
  change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
  simpa [withinLimit] using hinput

/-- The exact count-failure WP bounds burnt gas through the real prefix. -/
theorem logFailureOutcome_burnt_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hzero : post.host.config.maxNumberLogs = some 0)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logFailureAttemptBudget ctx raw post storageCost rest)) :
    (logFailureOutcome ctx raw post).burntGas ≤ logFailureAttemptBudget ctx raw post storageCost rest := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := logFailureBudget cfg (executionStore cfg vm raw) post storageCost rest
  have hs := startup_credits_and_burnt cfg vm raw budget hcredits
  have hw := wp_save_log_zero cfg (executionStore cfg vm raw) post storageCost rest written execLimits
    (by rfl) (by rfl) (by rfl) (by rfl) (active_input_limit ctx raw hinput) hzero hstorage hs.1
  obtain ⟨_, hpost, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hpost.2.1] at hb
  simp only [StepResult.host, atCode, executionStore, initialized_host] at hb
  simp only [logFailureOutcome, outcomeOfExecution, StepResult.host]
  change (logFailureStore cfg (executionStore cfg vm raw) post).host.gas.burnt ≤ _
  change (logFailureStore cfg (executionStore cfg vm raw) post).host.gas.burnt ≤
    (executionActive cfg vm raw).gas.burnt + budget at hb
  change _ ≤ burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget)
  rw [hs.2] at hb
  omega

/-- Boundary observation retains the proved startup-inclusive count bound. -/
theorem execOn_log_failure_usedGas_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hzero : post.host.config.maxNumberLogs = some 0)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logFailureAttemptBudget ctx raw post storageCost rest)) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ logFailureAttemptBudget ctx raw post storageCost rest := by
  have hr := run_save_log_zero_public ctx raw post storageCost rest written hp hinput hzero hstorage hframe hcredits
  have hb := logFailureOutcome_burnt_le ctx raw post storageCost rest written hinput hzero hstorage hcredits
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
  rw [hmethod, hr, Near.Boundary.observe_usedGas_abort (logFailureOutcome_fields ctx raw post hframe).1]
  exact hb

/-- The length-failure WP bounds burnt gas without reading the log memory. -/
theorem logLengthFailureOutcome_burnt_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hcount : logCountError post = none) (hlogs : post.host.logs = [])
    (hlimit : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logLengthFailureAttemptBudget ctx raw post storageCost rest)) :
    (logLengthFailureOutcome ctx raw post).burntGas ≤ logLengthFailureAttemptBudget ctx raw post storageCost rest := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := logLengthFailureBudget cfg (executionStore cfg vm raw) post storageCost rest
  have hs := startup_credits_and_burnt cfg vm raw budget hcredits
  have hw := wp_save_log_length cfg (executionStore cfg vm raw) post storageCost rest
    cfg.wasm.limits.maxTotalLogLength written execLimits (by rfl) (by rfl) (by rfl) (by rfl)
    (active_input_limit ctx raw hinput) hcount hlogs hlimit hshort hstorage hs.1
  obtain ⟨_, hpost, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hpost.2.1] at hb
  simp only [StepResult.host, atCode, executionStore, initialized_host] at hb
  simp only [logLengthFailureOutcome, outcomeOfExecution, StepResult.host]
  change (logLengthFailureStore cfg (executionStore cfg vm raw) post cfg.wasm.limits.maxTotalLogLength).host.gas.burnt ≤ _
  change (logLengthFailureStore cfg (executionStore cfg vm raw) post cfg.wasm.limits.maxTotalLogLength).host.gas.burnt ≤
    (executionActive cfg vm raw).gas.burnt + budget at hb
  change _ ≤ burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget)
  rw [hs.2] at hb
  omega

/-- Boundary observation retains the startup-inclusive log-length bound. -/
theorem execOn_log_length_failure_usedGas_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hcount : logCountError post = none) (hlogs : post.host.logs = [])
    (hlimit : post.host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hstorage : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
      post storageCost rest written)
    (hframe : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) post)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (logLengthFailureAttemptBudget ctx raw post storageCost rest)) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ logLengthFailureAttemptBudget ctx raw post storageCost rest := by
  have hr := run_save_log_length_public ctx raw post storageCost rest written hp hinput
    hcount hlogs hlimit hshort hstorage hframe hcredits
  have hb := logLengthFailureOutcome_burnt_le ctx raw post storageCost rest written hinput
    hcount hlogs hlimit hshort hstorage hcredits
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
  rw [hmethod, hr, Near.Boundary.observe_usedGas_abort (logLengthFailureOutcome_fields ctx raw post hframe).1]
  exact hb

/-- The final return trap is bounded by its actual four-host execution budget. -/
theorem returnLengthFailureOutcome_burnt_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
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
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest)) :
    (returnLengthFailureOutcome ctx raw post).burntGas ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := successBudget cfg (executionStore cfg vm raw) post storageCost rest
  have hs := startup_credits_and_burnt cfg vm raw budget hcredits
  have hw := wp_save_return_length cfg (executionActive cfg vm raw) cfg.wasm.limits.initialMemoryPages
    (some cfg.wasm.limits.maxMemoryPages) post storageCost rest cfg.wasm.limits.maxLengthReturnedData
    written execLimits hp.positive
    (by simpa only [executionStore, initialized_host] using active_input_limit ctx raw hinput)
    hmemory (by rw [executionActive_input]; exact hregister)
    hreturnLimit (by rw [executionActive_input]; exact hshort) hcount hspace hreadCost hpush hs.1 hstorage
  obtain ⟨_, hpost, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hpost.2.1] at hb
  simp only [StepResult.host, atCode, initialized_host] at hb
  simp only [returnLengthFailureOutcome, outcomeOfExecution, StepResult.host]
  change (returnLengthFailureStore cfg (executionStore cfg vm raw) post cfg.wasm.limits.maxLengthReturnedData).host.gas.burnt ≤ _
  change (returnLengthFailureStore cfg (executionStore cfg vm raw) post cfg.wasm.limits.maxLengthReturnedData).host.gas.burnt ≤
    (executionActive cfg vm raw).gas.burnt + budget at hb
  change _ ≤ burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget)
  rw [hs.2] at hb
  omega

/-- Public boundary gas coverage for the rejected return. -/
theorem execOn_return_length_failure_usedGas_le (ctx : Context) (raw : Storage) (post : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
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
    (Near.Boundary.execOn code raw ctx).usedGas ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  have hr := run_save_return_length_public ctx raw post storageCost rest written hp hinput
    hmemory hregister hreturnLimit hshort hcount hspace hreadCost hpush hstorage hframe hcredits
  have hb := returnLengthFailureOutcome_burnt_le ctx raw post storageCost rest written hp hinput
    hmemory hregister hreturnLimit hshort hcount hspace hreadCost hpush hstorage hcredits
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
  rw [hmethod, hr, Near.Boundary.observe_usedGas_abort (returnLengthFailureOutcome_fields ctx raw post hframe).1]
  exact hb

private theorem output_log_budget_le (ctx : Context) (raw : Storage)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logFailureAttemptBudget ctx raw post storageCost rest ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  have hb : logFailureCost post ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" ≤ burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logFailureAttemptBudget_eq, executionBudget_eq]
  omega


private theorem output_log_length_budget_le (ctx : Context) (raw : Storage)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logLengthFailureAttemptBudget ctx raw post storageCost rest ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  have hb : logLengthFailureCost post ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" + post.host.extCosts.cost "utf8_decoding_base" ≤
      burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logLengthFailureAttemptBudget_eq, executionBudget_eq]
  omega


/-- Original sufficient gas covers the actual empty-base output rejection. -/
theorem execOn_empty_log_failure_usedGas_le
    (ctx : Context) (raw : Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc := emptyCredits_of_gasLimit_allReturn ctx raw 0 hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := empty_storageFrontier_of_initialCredits ctx raw raw.toFinset 0 hwf rfl
    hp.positive hkey hvalue hentries hselected hc hproof
  have hz := congrArg NearConfig.maxNumberLogs (emptyAfter_config ctx raw)
  have hzero : (emptyAfter ctx raw).host.config.maxNumberLogs = some 0 := by
    change (emptyAfter ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs at hz
    simpa only [hzero] using hz
  have hb := execOn_log_failure_usedGas_le ctx raw (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hzero hs (emptyAfter_frame ctx raw) (hc.mono (output_log_budget_le ctx raw _ _ _))
  exact hb.trans ((output_log_budget_le ctx raw _ _ _).trans
    (by simpa only [Nat.add_zero] using executionBudget_empty_le ctx raw 0 hp.positive hkey hvalue))

/-- Original sufficient gas covers the actual empty-base output rejection. -/
theorem execOn_empty_log_length_failure_usedGas_le
    (ctx : Context) (raw : Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc := emptyCredits_of_gasLimit_allReturn ctx raw 0 hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := empty_storageFrontier_of_initialCredits ctx raw raw.toFinset 0 hwf rfl
    hp.positive hkey hvalue hentries hselected hc hproof
  have hn := congrArg NearConfig.maxNumberLogs (emptyAfter_config ctx raw)
  have hl := congrArg NearConfig.maxLogLen (emptyAfter_config ctx raw)
  have hnum : (emptyAfter ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlen : (emptyAfter ctx raw).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hl
  have hcountOk : logCountError (emptyAfter ctx raw) = none := by
    simp [logCountError, hnum, emptyAfter_logs, Nat.not_le.mpr hcount]
  have hb := execOn_log_length_failure_usedGas_le ctx raw (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hcountOk (emptyAfter_logs ctx raw) hlen hshort hs (emptyAfter_frame ctx raw)
    (hc.mono (output_log_length_budget_le ctx raw _ _ _))
  exact hb.trans ((output_log_length_budget_le ctx raw _ _ _).trans
    (by simpa only [Nat.add_zero] using executionBudget_empty_le ctx raw 0 hp.positive hkey hvalue))

/-- Original sufficient gas covers the actual empty-base output rejection. -/
theorem execOn_empty_return_length_failure_usedGas_le
    (ctx : Context) (raw : Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc := emptyCredits_of_gasLimit_allReturn ctx raw 0 hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := empty_storageFrontier_of_initialCredits ctx raw raw.toFinset 0 hwf rfl
    hp.positive hkey hvalue hentries hselected hc hproof
  have hf := emptyAfter_frame ctx raw
  have hn := congrArg NearConfig.maxNumberLogs (emptyAfter_config ctx raw)
  have hl := congrArg NearConfig.maxLogLen (emptyAfter_config ctx raw)
  have hr := congrArg NearConfig.maxReturnLen (emptyAfter_config ctx raw)
  have hnum : (emptyAfter ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlen : (emptyAfter ctx raw).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hl
  have hreturn : (emptyAfter ctx raw).host.config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := hr
  have hcountOk : logCountError (emptyAfter ctx raw) = none := by
    simp [logCountError, hnum, emptyAfter_logs, Nat.not_le.mpr hcount]
  have hspace : 5 ≤ logSpace (emptyAfter ctx raw) := by
    simpa [logSpace, totalLogLength, emptyAfter_logs, hlen] using hloglen
  have hpush : ∀ limit, (emptyAfter ctx raw).host.config.maxLogLen = some limit →
      totalLogLength (emptyAfter ctx raw) + 5 ≤ limit := by
    intro limit he
    have heq := Option.some.inj (hlen.symm.trans he)
    simpa [totalLogLength, emptyAfter_logs, ← heq] using hloglen
  have hmem := hf.1.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hreg := (congrFun (StorageFrame.Frame.registers hf) 0).trans
    (storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hread : (emptyAfter ctx raw).host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64 := by
    rw [emptyAfter_extCosts]
    exact saveEmptyCost_read_room ctx raw.toFinset hwf hgas
  have hb := execOn_return_length_failure_usedGas_le ctx raw (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hmem hreg hreturn hshort hcountOk hspace hread hpush hs hf hc
  exact hb.trans (by simpa only [Nat.add_zero] using
    executionBudget_empty_le ctx raw 0 hp.positive hkey hvalue)

end WNear.Skeleton
