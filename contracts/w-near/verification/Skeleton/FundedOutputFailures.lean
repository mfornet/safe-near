import Skeleton.FundedObservation
import Skeleton.LogLengthFailure
import Skeleton.ReturnLengthFailure

/-! Auxiliary reference executions for output-limit rejections. Original
guest context and prepaid gas are fixed; only internal counter limits grow. -/
namespace WNear.Skeleton.FundedOutputFailures
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation FundedEmpty FundedObservation
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

private theorem resources (ctx : Context) (raw : Storage) (rest : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    PreEq (origin ctx raw) host ∧
    host.gas.Credits (successBudget ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest) ∧
    StorageFrontier ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest 0 := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hs := StartupSimulation.reference_startup_credits ctx raw (saveEmptyCost ctx + rest)
  have hc : host.gas.Credits (saveEmptyCost ctx + rest) := hs.2.2
  have hb := hc.mono (budget_le ctx raw host rest hh hpages hkey hvalue)
  exact ⟨hh, hb, frontier ctx raw host rest hh hwf hpages hkey hvalue hentries hselected hb hproof⟩

private theorem input_limit (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) (hi : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize) :
    withinLimit (bodyStore ctx host).host.config.maxRegisterLen (bodyStore ctx host).host.context.input.length = true := by
  simp only [bodyStore, initialized_host, hh.config, hh.input]
  change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
  simpa [withinLimit] using hi

private theorem post_fields (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    (FundedEmpty.after ctx host).host.config = (origin ctx raw).config ∧
    (FundedEmpty.after ctx host).host.logs = [] ∧ (FundedEmpty.after ctx host).host.lastExecutionIssue = none := by
  have hb := (before_resources ctx raw host hh).1.fields
  have hf := after_frame ctx host
  exact ⟨hf.config.trans hb.config, hf.logs.trans (congrArg NearState.logs hb), hf.lastExecutionIssue.trans hb.issue⟩

private theorem count_budget_le (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) : logFailureBudget cfg store post storageCost rest ≤ successBudget cfg store post storageCost rest := by
  have hcost : logFailureCost post ≤ burnSum (successLogBefore cfg store post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" ≤ burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logFailureBudget_eq]
  unfold successBudget
  omega

private theorem length_budget_le (cfg : RuntimeConfig) (store : Store NearState) (post : HostStore NearState)
    (storageCost rest : Nat) : logLengthFailureBudget cfg store post storageCost rest ≤ successBudget cfg store post storageCost rest := by
  have hcost : logLengthFailureCost post ≤ burnSum (successLogBefore cfg store post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" + post.host.extCosts.cost "utf8_decoding_base" ≤ burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logLengthFailureBudget_eq]
  unfold successBudget
  omega

private theorem reference_of_wp (ctx : Context) (raw : Storage) (rest fuel steps credits : Nat) (final : StepResult NearState)
    (hsteps : steps ≤ fuel)
    (hw : WP ctx.protocol.wasm steps
      (.next (atCode (bodyStore ctx (referenceHost ctx raw rest)) execLimits #[] saveFrame [] module.funcs[0]!.body)) credits
      (fun remaining result error => remaining = rest ∧ result = final ∧ error = none)) :
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel = (final, none) := by
  obtain ⟨_, hp, _⟩ := hw.result
  have hr : runMetered ctx.protocol.wasm steps
      (StartupSimulation.body ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))) = (final, none) := by
    apply Prod.ext
    · simpa only [StartupSimulation.body, referenceHost, entryConfig, bodyStore, preparedData] using hp.2.1
    · simpa only [StartupSimulation.body, referenceHost, entryConfig, bodyStore, preparedData] using hp.2.2
  have hextra := runMetered_extra_fuel ctx.protocol.wasm steps
    (StartupSimulation.body ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest)))
    (by rw [hr]; simp) (fuel - steps)
  rw [show steps + (fuel - steps) = fuel by omega] at hextra
  exact hextra.trans hr

/-- An actual funded reference rejects log count after a completed write. -/
theorem count_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host (HostError.numberOfLogsExceeded 0).message)
        (logFailureStore ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)), none) := by
  let host := referenceHost ctx raw rest
  obtain ⟨hh, hc, hs⟩ := resources ctx raw rest hwf hpages hkey hvalue hentries hselected hproof
  have hcfg := (post_fields ctx raw host hh).1
  have hz := congrArg NearConfig.maxNumberLogs hcfg
  have hzeroPost : (FundedEmpty.after ctx host).host.config.maxNumberLogs = some 0 := by
    change (FundedEmpty.after ctx host).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs at hz
    simpa only [hzero] using hz
  have hcredits : (bodyStore ctx host).host.gas.Credits
      (logFailureBudget ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest) := by
    simpa only [bodyStore, initialized_host] using hc.mono (count_budget_le ctx.protocol _ _ _ _)
  have hw := wp_save_log_zero ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest 0 execLimits
    (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl)
    (by simp only [bodyStore]; rfl) (input_limit ctx raw host hh hinput) hzeroPost hs hcredits
  exact reference_of_wp ctx raw rest fuel 12 _ _ (by omega) hw


private theorem checked_trap_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (store : Store NearState) (message : String)
    (error : HostError) (failure : NearInterface.Failure) (bytes : List Near.Bytes) (logs : List String)
    (hmarker : store.host.lastError = some error) (hissue : store.host.lastExecutionIssue = none)
    (hlogs : store.host.logs = bytes)
    (hdecode : bytes.map (fun b => (String.fromUTF8? ⟨b.toArray⟩).getD "") = logs)
    (hfailure : Near.Boundary.failureOf (.hostError error) = failure) :
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw (.trap (.host message) store) none))
      (.error ⟨.panic failure, logs⟩) := by
  have ha : (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw (.trap (.host message) store) none).aborted =
      some (.hostError error) := by
    simp [outcomeOfExecution, StepResult.host, trapError, hmarker, hissue]
  have hl : (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw (.trap (.host message) store) none).logs = logs := by
    simpa only [Near.Boundary.outcomeOfExecution_logs, StepResult.host, logsOf, hlogs] using hdecode
  have hv : (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw (.trap (.host message) store) none).receiptsValid = true := by
    simp [outcomeOfExecution, StepResult.host, VMOutcome.receiptsValid, receiptsValidFrom]
  have hr : (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw (.trap (.host message) store) none).receipts = [] := rfl
  unfold Near.Boundary.observeChecked
  simp only [VMOutcome.checkReceipts, hv, ↓reduceIte, hr, Near.Boundary.actionsIssue?, List.findSome?_nil,
    Near.checkVMReceipts, List.zipIdx_nil, List.forIn_nil, pure, Except.pure]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError error, ha, hfailure, hl⟩

/-- The checked actual funded reference agrees with the independent log-count rejection. -/
theorem count_reference_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2))
      ((model gasBound).step ctx st ()) := by
  have hr := count_run ctx raw rest fuel hwf hpages hfuel hinput hkey hvalue hzero hentries hselected hproof
  dsimp only
  rw [hr]
  change Matches (model gasBound) ctx raw.toFinset _ (modelStep ctx st ())
  rw [modelStep_log_zero ctx st hinput hkey hvalue hzero]
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hp := post_fields ctx raw host hh
  have hf := logFailureStore_fields ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)
  exact checked_trap_matches gasBound ctx raw _ _ (.numberOfLogsExceeded 0) _ [] []
    hf.1 (hf.2.1.trans hp.2.2) (hf.2.2.trans hp.2.1) rfl rfl


/-- The funded reference rejects total log length before reading message memory. -/
theorem length_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host (HostError.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength).message)
        (logLengthFailureStore ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) ctx.protocol.wasm.limits.maxTotalLogLength), none) := by
  let host := referenceHost ctx raw rest
  obtain ⟨hh, hc, hs⟩ := resources ctx raw rest hwf hpages hkey hvalue hentries hselected hproof
  have hp := post_fields ctx raw host hh
  have hn := congrArg NearConfig.maxNumberLogs hp.1
  have hl := congrArg NearConfig.maxLogLen hp.1
  have hnum : (FundedEmpty.after ctx host).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlimit : (FundedEmpty.after ctx host).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hl
  have hcountPost : logCountError (FundedEmpty.after ctx host) = none := by
    simp [logCountError, hnum, hp.2.1, Nat.not_le.mpr hcount]
  have hcredits : (bodyStore ctx host).host.gas.Credits
      (logLengthFailureBudget ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest) := by
    simpa only [bodyStore, initialized_host] using hc.mono (length_budget_le ctx.protocol _ _ _ _)
  have hw := wp_save_log_length ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest
    ctx.protocol.wasm.limits.maxTotalLogLength 0 execLimits
    (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl)
    (by simp only [bodyStore]; rfl) (input_limit ctx raw host hh hinput)
    hcountPost hp.2.1 hlimit hshort hs hcredits
  exact reference_of_wp ctx raw rest fuel 12 _ _ (by omega) hw

/-- The checked actual reference matches the independent log-length rejection. -/
theorem length_reference_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2))
      ((model gasBound).step ctx st ()) := by
  have hr := length_run ctx raw rest fuel hwf hpages hfuel hinput hkey hvalue hcount hshort hentries hselected hproof
  dsimp only
  rw [hr]
  change Matches (model gasBound) ctx raw.toFinset _ (modelStep ctx st ())
  rw [modelStep_log_length ctx st hinput hkey hvalue hcount hshort]
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hp := post_fields ctx raw host hh
  have hf := logLengthFailureStore_fields ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) ctx.protocol.wasm.limits.maxTotalLogLength
  exact checked_trap_matches gasBound ctx raw _ _ (.totalLogLengthExceeded 5 ctx.protocol.wasm.limits.maxTotalLogLength) _ [] []
    hf.1 (hf.2.1.trans hp.2.2) (hf.2.2.trans hp.2.1) rfl rfl


/-- The funded reference logs `saved`, then rejects returned-data length. -/
theorem return_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host "value_return: return size exceeded")
        (returnLengthFailureStore ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)
          ctx.protocol.wasm.limits.maxLengthReturnedData), none) := by
  let host := referenceHost ctx raw rest
  obtain ⟨hh, hc, hs⟩ := resources ctx raw rest hwf hpages hkey hvalue hentries hselected hproof
  have hp := post_fields ctx raw host hh
  have hn := congrArg NearConfig.maxNumberLogs hp.1
  have hl := congrArg NearConfig.maxLogLen hp.1
  have hr := congrArg NearConfig.maxReturnLen hp.1
  have hnum : (FundedEmpty.after ctx host).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs := hn
  have hlen : (FundedEmpty.after ctx host).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := hl
  have hreturn : (FundedEmpty.after ctx host).host.config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := hr
  have hcountPost : logCountError (FundedEmpty.after ctx host) = none := by
    simp [logCountError, hnum, hp.2.1, Nat.not_le.mpr hcount]
  have hspace : 5 ≤ logSpace (FundedEmpty.after ctx host) := by
    simpa [logSpace, totalLogLength, hp.2.1, hlen] using hloglen
  have hpush : ∀ limit, (FundedEmpty.after ctx host).host.config.maxLogLen = some limit →
      totalLogLength (FundedEmpty.after ctx host) + 5 ≤ limit := by
    intro limit he
    have heq := Option.some.inj (hlen.symm.trans he)
    simpa [totalLogLength, hp.2.1, ← heq] using hloglen
  have hb := before_resources ctx raw host hh
  have hf := after_frame ctx host
  have hmem := hf.1.trans hb.1.memory
  have hreg := (congrFun hf.registers 0).trans hb.2
  have hext : (FundedEmpty.after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hreadPost : (FundedEmpty.after ctx host).host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64 := by
    rw [hext]
    exact hread
  have hi : withinLimit host.config.maxRegisterLen host.context.input.length = true := by
    simpa only [bodyStore, initialized_host] using input_limit ctx raw host hh hinput
  have hw := wp_save_return_length ctx.protocol host ctx.protocol.wasm.limits.initialMemoryPages
    (some ctx.protocol.wasm.limits.maxMemoryPages) (FundedEmpty.after ctx host) (cost ctx host) rest
    ctx.protocol.wasm.limits.maxLengthReturnedData 0 execLimits hpages hi hmem
    (by rw [hh.input]; exact hreg) hreturn (by rw [hh.input]; exact hshort)
    hcountPost hspace hreadPost hpush
    (by simpa only [bodyStore, preparedData] using hc)
    (by simpa only [bodyStore, preparedData] using hs)
  apply reference_of_wp ctx raw rest fuel 15
    (successBudget ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host) (cost ctx host) rest) _ (by omega)
  simpa only [bodyStore, preparedData] using hw

/-- Checked observation retains the saved log and classifies the exact raw
return trap through its structured protocol error marker. -/
theorem return_reference_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hfuel : 16 ≤ fuel)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2))
      ((model gasBound).step ctx st ()) := by
  have hr := return_run ctx raw rest fuel hwf hpages hfuel hinput hkey hvalue hcount hloglen hshort hread
    hentries hselected hproof
  dsimp only
  rw [hr]
  change Matches (model gasBound) ctx raw.toFinset _ (modelStep ctx st ())
  rw [modelStep_return_length ctx st hinput hkey hvalue hcount hloglen hshort]
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hp := post_fields ctx raw host hh
  have hf := returnLengthFailureStore_fields ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)
    ctx.protocol.wasm.limits.maxLengthReturnedData
  have hinputHost : (bodyStore ctx host).host.context.input = ctx.args := by
    simpa only [bodyStore, initialized_host] using (show host.context.input = ctx.args from hh.input)
  rw [hinputHost] at hf
  have hlogs := hf.2.2.trans (congrArg (fun logs => logs ++ ["saved".toUTF8.toList]) hp.2.1)
  exact checked_trap_matches gasBound ctx raw _ _
    (.returnedValueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthReturnedData) _
    ["saved".toUTF8.toList] ["saved"] hf.1 (hf.2.1.trans hp.2.2) hlogs (by decide +kernel) rfl


private theorem matched_logs (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (observed : Observation) (result : NearInterface.StepResult M.Panic M.State M.Ret M.Promise)
    (h : Matches M ctx raw observed result) : observed.logs = result.logs := by
  cases result with
  | ok out => exact h.2.2.2.2.1
  | error failure => exact h.2.2.2.2.1

/-- Actual public execution at any original gas budget agrees with an output
rejection or aborts out of gas with rollback and a prefix of the model logs.
All storage execution is derived from original empty-base resources. -/
theorem output_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hfailed : ctx.protocol.wasm.limits.maxNumberLogs = 0 ∨
      ctx.protocol.wasm.limits.maxTotalLogLength < 5 ∨
      ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have hhigh : Matches (model gasBound) ctx raw.toFinset
      (ReceiptSimulation.referenceObservation ctx raw (referenceBudget ctx raw 0)) ((model gasBound).step ctx st ()) := by
    by_cases hz : ctx.protocol.wasm.limits.maxNumberLogs = 0
    · exact count_reference_matches gasBound ctx raw st 0 _ hwf hp.positive (fuelFor_save _ _)
        hinput hkey hvalue hz hentries hselected hproof
    have hcount := Nat.pos_of_ne_zero hz
    by_cases hl : ctx.protocol.wasm.limits.maxTotalLogLength < 5
    · exact length_reference_matches gasBound ctx raw st 0 _ hwf hp.positive (fuelFor_save _ _)
        hinput hkey hvalue hcount hl hentries hselected hproof
    have hloglen := Nat.le_of_not_gt hl
    have hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length := by omega
    exact return_reference_matches gasBound ctx raw st 0 _ hwf hp.positive (fuelFor_save _ _)
      hinput hkey hvalue hcount hloglen hshort hread hentries hselected hproof
  have hl := matched_logs (model gasBound) ctx raw.toFinset _ _ hhigh
  have hr := ReceiptSimulation.execOn_replay ctx raw (referenceBudget ctx raw 0) hmethod hwf
    hp.positive hp.minmax hp.maximum hp.types hp.functions hentries hselected hproof
  rcases hr with he | hg
  · left
    rw [he]
    exact hhigh
  · right
    rw [hl] at hg
    exact hg

end WNear.Skeleton.FundedOutputFailures
