import Skeleton.FundedObservation
import Skeleton.StorageValueFailure

/-!
# Funded reference failures before trie access

The original guest-visible context and gas budget remain fixed. A separate
internal reservation pays real startup and the failing input/storage prefix.
-/
namespace WNear.Skeleton.FundedInputFailures
open Wasm Wasm.Near MeteredLogic MeteredPrefix NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation FundedEmpty
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- Enough body gas for input, five storage arguments and both span reads. -/
def earlyCost (ctx : Context) : Nat :=
  8 * ctx.protocol.wasm.regularOpCost +
    (ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base") +
    (ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "storage_write_base" +
      ctx.protocol.wasm.extCosts.cost "read_memory_base" + ctx.protocol.wasm.extCosts.cost "read_memory_byte" +
      ctx.protocol.wasm.extCosts.cost "read_register_base" +
      ctx.protocol.wasm.extCosts.cost "read_register_byte" * ctx.args.length)

def referenceBudget (ctx : Context) (raw : Storage) (rest : Nat) : Nat :=
  burnSum (origin ctx raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + (earlyCost ctx + rest))

def referenceHost (ctx : Context) (raw : Storage) (rest : Nat) : NearState :=
  StartupSimulation.active ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))

theorem reference_resources (ctx : Context) (raw : Storage) (rest : Nat) :
    PreEq (origin ctx raw) (referenceHost ctx raw rest) ∧
      (referenceHost ctx raw rest).gas.Credits (earlyCost ctx + rest) := by
  exact ⟨(PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _),
    (StartupSimulation.reference_startup_credits ctx raw (earlyCost ctx + rest)).2.2⟩

theorem input_budget_le (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) :
    inputFailureBudget ctx.protocol.wasm (bodyStore ctx host) rest ≤ earlyCost ctx + rest := by
  have he : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hh
  simp only [inputFailureBudget, bodyStore, initialized_host, Input.cost, he, earlyCost]
  omega

theorem key_budget_le (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) :
    keyFailureBudget ctx.protocol (bodyStore ctx host) rest ≤ earlyCost ctx + rest := by
  have hb := (before_resources ctx raw host hh).1.fields
  have he : (keyFailureBefore ctx.protocol (bodyStore ctx host)).host.extCosts = ctx.protocol.wasm.extCosts :=
    by simpa only [FundedEmpty.before, keyFailureBefore, preView, origin, VMContext.toNearState] using congrArg NearState.extCosts hb
  have hi : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hh
  rw [keyFailureBudget_eq, keyFailureCost_eq, he]
  simp only [Input.cost, successInputBefore, chargedMany, chargedStore, chargeHost, bodyStore,
    initialized_host, hi, earlyCost]
  omega

theorem value_budget_le (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) :
    valueFailureBudget ctx.protocol (bodyStore ctx host) rest ≤ earlyCost ctx + rest := by
  have hb := before_resources ctx raw host hh
  have he : (valueFailureBefore ctx.protocol (bodyStore ctx host)).host.extCosts = ctx.protocol.wasm.extCosts :=
    by simpa only [FundedEmpty.before, valueFailureBefore, preView, origin, VMContext.toNearState] using congrArg NearState.extCosts hb.1.fields
  have hi : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hh
  have hreg : (valueFailureBefore ctx.protocol (bodyStore ctx host)).host.registers 0 = some ctx.args := by simpa only [FundedEmpty.before, valueFailureBefore] using hb.2
  rw [valueFailureBudget_eq, valueFailureCost_eq _ _ ctx.args hreg, he]
  simp only [Input.cost, successInputBefore, chargedMany, chargedStore, chargeHost, bodyStore,
    initialized_host, hi, earlyCost]
  omega

private theorem extra_fuel (cfg : WasmConfig) (steps fuel : Nat) (machine final : Machine)
    (hbound : steps ≤ fuel)
    (hr : runMetered cfg steps machine = (final, none)) :
    runMetered cfg fuel machine = (final, none) := by
  have hx := runMetered_extra_fuel cfg steps machine (by rw [hr]; simp) (fuel - steps)
  rw [show steps + (fuel - steps) = fuel by omega] at hx
  exact hx.trans hr

/-- Actual reference input rejection; no original gas premise is present. -/
theorem reference_input_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length) (hfuel : 2 ≤ fuel) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host "input: register size exceeded") (inputFailureStore ctx.protocol.wasm (bodyStore ctx host)), none) := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (reference_resources ctx raw rest).1
  have hc := (reference_resources ctx raw rest).2.mono (input_budget_le ctx raw host rest hh)
  have hl : withinLimit (bodyStore ctx host).host.config.maxRegisterLen (bodyStore ctx host).host.context.input.length = false := by
    simp only [bodyStore, initialized_host]
    rw [hh.config, hh.input]
    change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = false
    simp [withinLimit, Nat.not_le_of_gt hinput]
  have hr := run_save_input_too_long ctx.protocol (bodyStore ctx host) execLimits rest (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl) hl
    (by simpa only [bodyStore, initialized_host] using hc)
  have hx := extra_fuel ctx.protocol.wasm 2 fuel _ _ hfuel hr
  simpa only [StartupSimulation.reference, StartupSimulation.body, referenceHost, host, bodyStore,
    entryConfig, preparedData] using hx

/-- Original resources classify the actual rejected input store. -/
theorem input_outcome_fields (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    let result := outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
      (.trap (.host "input: register size exceeded") (inputFailureStore ctx.protocol.wasm (bodyStore ctx host))) none
    result.aborted = some (.hostError (.guestPanic "input: register size exceeded")) ∧
      result.logs = [] ∧ result.receiptsValid = true := by
  have he : host.lastError = none := congrArg NearState.lastError hh
  have hi : host.lastExecutionIssue = none := hh.issue
  have hl : host.logs = [] := congrArg NearState.logs hh
  have ht := inputFailure_error ctx.protocol.wasm (bodyStore ctx host)
    (by simpa only [bodyStore, initialized_host] using he) (by simpa only [bodyStore, initialized_host] using hi)
  have hf := (inputFailureStore_frame ctx.protocol.wasm (bodyStore ctx host)).2.2.1
  have hz : (inputFailureStore ctx.protocol.wasm (bodyStore ctx host)).host.logs = [] := hf.trans (by simpa only [bodyStore, initialized_host] using hl)
  simp [outcomeOfExecution, StepResult.host, ht, hz, logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- Funded input rejection is the independent model's first failure. -/
theorem reference_input_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length) (hfuel : 2 ≤ fuel) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2)) (modelStep ctx st ()) := by
  dsimp only
  rw [reference_input_run ctx raw rest fuel hinput hfuel, modelStep_input_too_long ctx st hinput]
  have hf := input_outcome_fields ctx raw (referenceHost ctx raw rest) (reference_resources ctx raw rest).1
  unfold Near.Boundary.observeChecked
  rw [VMOutcome.checkReceipts, hf.2.2]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.guestPanic "input: register size exceeded"), hf.1, rfl, hf.2.1⟩

private theorem prepared_key (ctx : Context) (raw : Storage) (b : HostStore NearState)
    (hm : b.mem = preparedData ctx.protocol) (hp : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg b 0 1 = some "k".toUTF8.toList := by
  let ref := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have he : b.mem = ref.mem := hm.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg b 0 1 = getMemOrReg ref 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, he]
    _ = _ := emptyPaid_key ctx raw hp

private theorem before_frame (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    BeforeWrite ctx raw (keyFailureBefore ctx.protocol (bodyStore ctx host)) ∧
      (keyFailureBefore ctx.protocol (bodyStore ctx host)).host.registers 0 = some ctx.args := by
  simpa only [keyFailureBefore, FundedEmpty.before] using before_resources ctx raw host hh

private theorem rejected_outcome_fields (ctx : Context) (raw : Storage) (store : Store NearState)
    (before : HostStore NearState) (charges : List Charge) (error : HostError)
    (hh : PreEq (origin ctx raw) before.host) (hburn : ∀ c ∈ charges, BurnsOnly c) :
    let out := outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
      (.trap (.host error.message) (commitCall ctx.protocol.wasm store (StorageFailure.rejected before charges error))) none
    out.aborted = some (.hostError error) ∧ out.logs = [] ∧ out.receiptsValid = true := by
  have hf := StorageFailure.rejected_fields before charges error hburn
  have hi : (StorageFailure.rejected before charges error).host.lastExecutionIssue = none := hf.2.2.2.2.2.trans hh.issue
  have hl : (StorageFailure.rejected before charges error).host.logs = [] :=
    hf.2.2.2.1.trans (congrArg NearState.logs hh)
  simp [outcomeOfExecution, StepResult.host, commitCall_host, trapError, hi, hf.2.2.2.2.1,
    hl, logsOf, VMOutcome.receiptsValid, receiptsValidFrom]

/-- Actual funded key rejection executes only the eight-instruction prefix. -/
theorem reference_key_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1) (hfuel : 8 ≤ fuel) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey).message)
        (keyFailureStore ctx.protocol (bodyStore ctx host) ctx.protocol.wasm.limits.maxLengthStorageKey), none) := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (reference_resources ctx raw rest).1
  have hc := (reference_resources ctx raw rest).2.mono (key_budget_le ctx raw host rest hh)
  have hb := before_frame ctx raw host hh
  have hi : withinLimit (bodyStore ctx host).host.config.maxRegisterLen (bodyStore ctx host).host.context.input.length = true := by
    simp only [bodyStore, initialized_host]
    rw [hh.config, hh.input]
    change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hinput
  have hk := prepared_key ctx raw _ hb.1.memory hpages
  have hw := wp_save_key_too_long ctx.protocol (bodyStore ctx host) execLimits
    ctx.protocol.wasm.limits.maxLengthStorageKey rest (by simp only [bodyStore]; rfl)
    (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl) hi hb.1.isView hk
    (congrArg NearConfig.maxStorageKeyLen hb.1.fields.config) hlong (by simpa only [bodyStore, initialized_host] using hc)
  obtain ⟨_, hp, _⟩ := hw.result
  have hr : runMetered ctx.protocol.wasm 8
      (.next (atCode (bodyStore ctx host) execLimits #[] saveFrame [] module.funcs[0]!.body)) = (_, none) :=
    Prod.ext hp.2.1 hp.2.2
  have hx := extra_fuel ctx.protocol.wasm 8 fuel _ _ hfuel hr
  simpa only [StartupSimulation.reference, StartupSimulation.body, referenceHost, host, bodyStore,
    entryConfig, preparedData] using hx

theorem key_outcome_fields (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    let out := outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
      (.trap (.host (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey).message)
        (keyFailureStore ctx.protocol (bodyStore ctx host) ctx.protocol.wasm.limits.maxLengthStorageKey)) none
    out.aborted = some (.hostError (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey)) ∧ out.logs = [] ∧ out.receiptsValid = true := by
  have hb := (before_frame ctx raw host hh).1.fields
  simpa only [keyFailureStore, keyFailureAfter, valueFailureBefore, keyFailureBefore] using
    rejected_outcome_fields ctx raw (successStorageBefore ctx.protocol (bodyStore ctx host))
      (keyFailureBefore ctx.protocol (bodyStore ctx host)) (StorageFailure.keyCharges _ 1 0) (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey)
      hb (StorageFailure.keyCharges_burns _ 1 0)

/-- Checked actual reference key failure matches the model's ordered checks. -/
theorem reference_key_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1) (hfuel : 8 ≤ fuel) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2)) (modelStep ctx st ()) := by
  dsimp only
  rw [reference_key_run ctx raw rest fuel hpages hinput hlong hfuel,
    modelStep_key_too_long ctx st hinput hlong]
  have hf := key_outcome_fields ctx raw (referenceHost ctx raw rest) (reference_resources ctx raw rest).1
  unfold Near.Boundary.observeChecked
  rw [VMOutcome.checkReceipts, hf.2.2]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (HostError.keyLengthExceeded 1 ctx.protocol.wasm.limits.maxLengthStorageKey), hf.1, rfl, hf.2.1⟩

/-- Actual funded value rejection executes only the eight-instruction prefix. -/
theorem reference_value_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length) (hfuel : 8 ≤ fuel) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.trap (.host (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue).message)
        (valueFailureStore ctx.protocol (bodyStore ctx host) ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue), none) := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host := (reference_resources ctx raw rest).1
  have hc := (reference_resources ctx raw rest).2.mono (value_budget_le ctx raw host rest hh)
  have hb := before_frame ctx raw host hh
  have hi : withinLimit (bodyStore ctx host).host.config.maxRegisterLen (bodyStore ctx host).host.context.input.length = true := by
    simp only [bodyStore, initialized_host]
    rw [hh.config, hh.input]
    change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hinput
  have hk := prepared_key ctx raw _ hb.1.memory hpages
  have hkeyLimit : ∀ n, (valueFailureBefore ctx.protocol (bodyStore ctx host)).host.config.maxStorageKeyLen = some n → 1 ≤ n := by
    intro n hn
    change (keyFailureBefore ctx.protocol (bodyStore ctx host)).host.config.maxStorageKeyLen = some n at hn
    rw [congrArg NearConfig.maxStorageKeyLen hb.1.fields.config] at hn
    cases Option.some.inj hn
    exact hkey
  have hvalue : getMemOrReg (valueFailureBefore ctx.protocol (bodyStore ctx host)) 0 u64Max = some ctx.args := by
    simp only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero]
    exact hb.2
  have hw := wp_save_value_too_long ctx.protocol (bodyStore ctx host) execLimits ctx.args
    ctx.protocol.wasm.limits.maxLengthStorageValue rest (by simp only [bodyStore]; rfl)
    (by simp only [bodyStore]; rfl) (by simp only [bodyStore]; rfl) hi hb.1.isView hk hkeyLimit hvalue
    (congrArg NearConfig.maxStorageValueLen hb.1.fields.config) hlong (by simpa only [bodyStore, initialized_host] using hc)
  obtain ⟨_, hp, _⟩ := hw.result
  have hr : runMetered ctx.protocol.wasm 8
      (.next (atCode (bodyStore ctx host) execLimits #[] saveFrame [] module.funcs[0]!.body)) = (_, none) :=
    Prod.ext hp.2.1 hp.2.2
  have hx := extra_fuel ctx.protocol.wasm 8 fuel _ _ hfuel hr
  simpa only [StartupSimulation.reference, StartupSimulation.body, referenceHost, host, bodyStore,
    entryConfig, preparedData] using hx

theorem value_outcome_fields (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    let out := outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
      (.trap (.host (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue).message)
        (valueFailureStore ctx.protocol (bodyStore ctx host) ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)) none
    out.aborted = some (.hostError (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)) ∧ out.logs = [] ∧ out.receiptsValid = true := by
  have hb := (before_frame ctx raw host hh).1.fields
  simpa only [valueFailureStore, valueFailureAfter, valueFailureBefore, keyFailureBefore] using
    rejected_outcome_fields ctx raw (successStorageBefore ctx.protocol (bodyStore ctx host))
      (valueFailureBefore ctx.protocol (bodyStore ctx host)) (StorageFailure.valueCharges _ 1 0 u64Max 0) (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue)
      hb (StorageFailure.valueCharges_burns _ 1 0 u64Max 0)

/-- Checked actual reference value failure matches the model's ordered checks. -/
theorem reference_value_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length) (hfuel : 8 ≤ fuel) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2)) (modelStep ctx st ()) := by
  dsimp only
  rw [reference_value_run ctx raw rest fuel hpages hinput hkey hlong hfuel,
    modelStep_value_too_long ctx st hinput hkey hlong]
  have hf := value_outcome_fields ctx raw (referenceHost ctx raw rest) (reference_resources ctx raw rest).1
  unfold Near.Boundary.observeChecked
  rw [VMOutcome.checkReceipts, hf.2.2]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (HostError.valueLengthExceeded ctx.args.length ctx.protocol.wasm.limits.maxLengthStorageValue), hf.1, rfl, hf.2.1⟩

/-- At least one of the three checks before trie access rejects the input. -/
def PreStorageRejected (ctx : Context) : Prop :=
  ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length ∨
    ctx.protocol.wasm.limits.maxLengthStorageKey < 1 ∨
    ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length

/-- The reference retains the entire original guest-visible context. -/
theorem reference_context (ctx : Context) (raw : Storage) (rest : Nat) :
    (referenceHost ctx raw rest).context = (origin ctx raw).context := by
  exact (StartupSimulation.active_context _ _).trans (enlargeHost_context _ _)

/-- The model's ordered pre-storage failure is proved by actual funded
execution. Rejection assumptions occur only on original protocol/input data. -/
theorem reference_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hfail : PreStorageRejected ctx) (hfuel : 8 ≤ fuel) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2)) (modelStep ctx st ()) := by
  by_cases hi : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length
  · exact reference_input_matches gasBound ctx raw st rest fuel hi (by omega)
  · have hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize := by omega
    by_cases hk : ctx.protocol.wasm.limits.maxLengthStorageKey < 1
    · exact reference_key_matches gasBound ctx raw st rest fuel hpages hinput hk hfuel
    · have hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey := by omega
      have hv : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length := by
        rcases hfail with h | h | h
        · exact False.elim (hi h)
        · exact False.elim (hk h)
        · exact h
      exact reference_value_matches gasBound ctx raw st rest fuel hpages hinput hkey hv hfuel

private theorem matched_logs (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (observed : Observation) (result : NearInterface.StepResult M.Panic M.State M.Ret M.Promise)
    (h : Matches M ctx raw observed result) : observed.logs = result.logs := by
  cases result with
  | ok out => exact h.2.2.2.2.1
  | error failure => exact h.2.2.2.2.1

/-- Actual default-fuel execution for any original gas budget, on the explicit
empty-base simulation slice. A pre-storage rejection either matches its model
failure or stops earlier for gas with rollback and a prefix of the model logs. -/
theorem execOn_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hp : PreparationLimits ctx.protocol) (hfail : PreStorageRejected ctx)
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
  have hhigh := reference_matches gasBound ctx raw st 0
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hp.positive hfail
    (Nat.le_trans (by decide : 8 ≤ 16) (fuelFor_save _ _))
  change Matches (model gasBound) ctx raw.toFinset
    (ReceiptSimulation.referenceObservation ctx raw (referenceBudget ctx raw 0)) ((model gasBound).step ctx st ()) at hhigh
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

end WNear.Skeleton.FundedInputFailures
