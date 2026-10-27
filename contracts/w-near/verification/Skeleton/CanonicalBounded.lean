import Skeleton.CanonicalObservation
import Skeleton.SuccessGas
import NearRuntime.InitialCredits

/-! Sufficient original gas for the actual public canonical save execution.
No auxiliary reference or whole-execution callback is assumed. -/
namespace WNear.Skeleton.CanonicalBounded
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation CanonicalBody
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- The original runtime host after real loading and activation. -/
def originalHost (ctx : Context) (raw : Storage) : NearState :=
  executionActive ctx.protocol (Near.Boundary.toVMContext ctx) raw

theorem originalHost_preEq (ctx : Context) (raw : Storage) :
    PreEq (origin ctx raw) (originalHost ctx raw) := by
  simpa only [originalHost, executionActive, executionLoaded, StartupSimulation.active,
    StartupSimulation.loaded, origin] using StartupSimulation.active_preEq ctx.protocol (origin ctx raw)

theorem bodyStore_eq (ctx : Context) (raw : Storage) :
    bodyStore ctx (originalHost ctx raw) = executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw := by
  unfold bodyStore FundedEmpty.bodyStore originalHost executionStore
  rfl

/-- The complete original loading, activation, body and output budget is
bounded by original data for arbitrary canonical trie storage. -/
theorem executionBudget_le (ctx : Context) (raw : Storage) (rest : Nat)
    (hwf : ctx.WF raw.toFinset) (hnodes : ctx.trie.NonzeroNodes)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest ≤ CanonicalCost.saveCost ctx + rest := by
  let host := originalHost ctx raw
  have hh := originalHost_preEq ctx raw
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hf := after_frame ctx host
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hfees : (after ctx host).host.fees = ctx.protocol.fees.actionFees :=
    hf.fees.trans (congrArg NearState.fees hb.1.fields)
  have ho := congrArg NearState.outputDataReceivers hf.2
  have hreceivers : (after ctx host).host.outputDataReceivers = (Near.Boundary.toVMContext ctx).outputDataReceivers :=
    ho.trans (congrArg NearState.outputDataReceivers hb.1.fields)
  have hcurrent : (after ctx host).host.context.currentAccountId = ctx.current.bytes :=
    hf.currentAccountId.trans hb.1.fields.current
  have hregister := (congrFun hf.registers 0).trans hb.2
  have hr := successReturn_cost_le ctx.protocol (bodyStore ctx host) (after ctx host) ctx.args hregister
  rw [hext, hfees, hreceivers, hcurrent] at hr
  have hhostExt : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hh
  have hi : Input.cost (successInputBefore ctx.protocol (bodyStore ctx host)).host =
      ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base" := by
    simp only [Input.cost, successInputBefore, chargedMany, chargedStore, chargeHost, bodyStore,
      FundedEmpty.bodyStore, initialized_host, hhostExt]
  have hl : (successLogBefore ctx.protocol (bodyStore ctx host) (after ctx host)).host.extCosts = ctx.protocol.wasm.extCosts := hext
  have hc := CanonicalCost.storage_cost_le ctx raw host hh hwf hnodes hpages hk hv
  unfold executionBudget
  rw [← bodyStore_eq ctx raw]
  unfold successBudget
  rw [hi, hl]
  unfold CanonicalCost.saveCost saveEmptyCost
  dsimp only [VMContext.toNearState]
  dsimp only [host] at hr hc
  omega

/-- Original total credits pay startup and leave the exact body reservation. -/
theorem active_credits (ctx : Context) (raw : Storage) (rest : Nat)
    (hc : (origin ctx raw).gas.Credits (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest)) :
    (originalHost ctx raw).gas.Credits (successBudget ctx.protocol (bodyStore ctx (originalHost ctx raw))
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest) := by
  rw [bodyStore_eq]
  exact StorageCredits.active ctx.protocol (Near.Boundary.toVMContext ctx) raw _ hc

/-- Every actual storage/output resource follows from original bounds,
canonical lookup and the original complete execution reservation. -/
theorem resources (ctx : Context) (raw : Storage) (rest : Nat)
    (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hnodes : ctx.trie.NonzeroNodes)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hc : (origin ctx raw).gas.Credits (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    SaveResources ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest (flag ctx (originalHost ctx raw)) := by
  let host := originalHost ctx raw
  have hh := originalHost_preEq ctx raw
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hf := after_frame ctx host
  have hcfg := hf.config.trans hb.1.fields.config
  have hlogs : (after ctx host).host.logs = [] := hf.logs.trans (congrArg NearState.logs hb.1.fields)
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hregister := (congrFun hf.registers 0).trans hb.2
  dsimp only [host] at hcfg hlogs hext
  refine ⟨?_, hf.1.trans hb.1.memory, hregister, ?_, ?_, ?_, ?_, ?_, hc, ?_⟩
  · change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hm.input
  · rw [hcfg]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthReturnedData) ctx.args.length = true
    simpa [withinLimit] using hm.returned
  · simp only [logCountError, hcfg, hlogs]
    change (if 0 ≥ ctx.protocol.wasm.limits.maxNumberLogs then _ else none) = none
    simp only [Nat.not_le.mpr hm.logs, ↓reduceIte]
  · simp only [Wasm.Near.logSpace, hcfg, totalLogLength, hlogs, List.map_nil, List.sum_nil]
    change 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength - 0
    simpa using hm.logBytes
  · rw [hext]
    exact hread
  · intro limit hl
    have hl' := congrArg NearConfig.maxLogLen hcfg
    change (after ctx host).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength at hl'
    rw [hl'] at hl
    cases Option.some.inj hl
    simpa only [totalLogLength, hlogs, List.map_nil, List.sum_nil, Nat.zero_add] using hm.logBytes
  · have hs := frontier ctx raw host rest hh hwf hnodes hp.positive hm.key hm.value (active_credits ctx raw rest hc) hproof
    simpa only [host, bodyStore_eq] using hs

/-- Sufficient original gas supplies all complete-execution credits. -/
theorem credits_of_gasLimit (ctx : Context) (raw : Storage) (rest : Nat)
    (hwf : ctx.WF raw.toFinset) (hnodes : ctx.trie.NonzeroNodes)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hgas : CanonicalCost.saveCost ctx + rest ≤ ctx.gasLimit) :
    (origin ctx raw).gas.Credits (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) rest) := by
  apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
  exact (executionBudget_le ctx raw rest hwf hnodes hpages hk hv).trans hgas

/-- The sufficiently funded original public execution matches the independent
model for any canonical storage, insertion or replacement, and either stake
outcome. Its exposed used gas is bounded solely by original context data. -/
theorem execOn_matches_and_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset) (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hnodes : ctx.trie.NonzeroNodes)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  have hc := credits_of_gasLimit ctx raw 0 hwf hnodes hp.positive hm.key hm.value
    (by simpa only [Nat.add_zero] using hgas)
  have hr := resources ctx raw 0 hwf hp hm hnodes hread hc hproof
  have hh := originalHost_preEq ctx raw
  have hb := (FundedEmpty.before_resources ctx raw (originalHost ctx raw) hh).1.fields
  have hf := after_frame ctx (originalHost ctx raw)
  have hpromises : (after ctx (originalHost ctx raw)).host.promises = [] :=
    hf.promises.trans (congrArg NearState.promises hb)
  have hmatch := CanonicalObservation.checked_body_matches gasBound ctx raw st (originalHost ctx raw)
    hh hwf hrepresented hp.positive hm hnodes (active_credits ctx raw 0 hc) hproof hroom
  rw [FundedObservation.final_eq ctx raw (originalHost ctx raw) _ hh.input] at hmatch
  have hrun := runAttempt_save_default ctx.protocol (Near.Boundary.toVMContext ctx) raw
    (after ctx (originalHost ctx raw)) (cost ctx (originalHost ctx raw)) 0
    (flag ctx (originalHost ctx raw)) hp hr
  have hexec := Near.Boundary.execOn_observeChecked code ctx raw rfl
  change Near.Boundary.execOn code raw ctx = Near.Boundary.observeChecked code.codeOf ctx raw
    (runAttempt ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw
      (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx))) at hexec
  rw [hmethod, hrun] at hexec
  have hmatched : Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
    rw [hexec]
    exact hmatch
  have hg := execOn_save_success_used_add_rest_le ctx raw (after ctx (originalHost ctx raw))
    (cost ctx (originalHost ctx raw)) 0 (flag ctx (originalHost ctx raw)) hmethod hp hr hpromises
  have hbudget := executionBudget_le ctx raw 0 hwf hnodes hp.positive hm.key hm.value
  exact ⟨hmatched, by simpa only [Nat.add_zero] using hg.trans hbudget⟩

end WNear.Skeleton.CanonicalBounded
