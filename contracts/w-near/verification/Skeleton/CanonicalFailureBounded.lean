import Skeleton.CanonicalBounded
import Skeleton.CanonicalReady
import Skeleton.OutputFailureGas

/-!
# Original sufficient gas for canonical output resource failures

The real canonical storage frontier and its frame are derived from original
credits. Count/length/return failures then reuse their exact operational and
receipt contracts, without empty-base or selected-key assumptions.
-/
namespace WNear.Skeleton.CanonicalFailureBounded
open Wasm Wasm.Near MeteredLogic NearInterface MeteredHosts
open FunctionalInvariant
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

abbrev post (ctx : Context) (raw : Storage) := CanonicalBody.after ctx (CanonicalBounded.originalHost ctx raw)
abbrev storageCost (ctx : Context) (raw : Storage) := CanonicalBody.cost ctx (CanonicalBounded.originalHost ctx raw)
abbrev written (ctx : Context) (raw : Storage) := CanonicalBody.flag ctx (CanonicalBounded.originalHost ctx raw)

structure Resources (ctx : Context) (raw : Storage) : Prop where
  credits : (origin ctx raw).gas.Credits (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
    (post ctx raw) (storageCost ctx raw) 0)
  frontier : StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)
    (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
  frame : StorageFrame.Frame (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw) (post ctx raw)
  budget : executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw (post ctx raw) (storageCost ctx raw) 0 ≤
    CanonicalCost.saveCost ctx

/-- Canonical storage is an actual derived call, with original sufficient gas;
no successful storage-execution premise occurs among the hypotheses. -/
theorem resources (ctx : Context) (raw : Storage) (hwf : ctx.WF raw.toFinset)
    (hp : PreparationLimits ctx.protocol) (hnodes : ctx.trie.NonzeroNodes)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Resources ctx raw := by
  have hc := CanonicalBounded.credits_of_gasLimit ctx raw 0 hwf hnodes hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := CanonicalBody.frontier ctx raw (CanonicalBounded.originalHost ctx raw) 0
    (CanonicalBounded.originalHost_preEq ctx raw) hwf hnodes hp.positive hkey hvalue
    (CanonicalBounded.active_credits ctx raw 0 hc) hproof
  have hf := CanonicalBody.after_frame ctx (CanonicalBounded.originalHost ctx raw)
  refine ⟨hc, ?_, ?_, ?_⟩
  · simpa only [CanonicalBounded.bodyStore_eq] using hs
  · simpa only [CanonicalBody.before, FundedEmpty.before, CanonicalBounded.bodyStore_eq, storageInput] using hf
  · simpa only [Nat.add_zero] using CanonicalBounded.executionBudget_le ctx raw 0 hwf hnodes hp.positive hkey hvalue

private theorem log_budget_le (ctx : Context) (raw : Storage) (p : HostStore NearState) (c rest : Nat) :
    logFailureAttemptBudget ctx raw p c rest ≤ executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw p c rest := by
  have hb : logFailureCost p ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) p).host.extCosts savedCharges := by
    change p.host.extCosts.cost "base" ≤ burnSum p.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logFailureAttemptBudget_eq, executionBudget_eq]
  omega

private theorem log_length_budget_le (ctx : Context) (raw : Storage) (p : HostStore NearState) (c rest : Nat) :
    logLengthFailureAttemptBudget ctx raw p c rest ≤ executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw p c rest := by
  have hb : logLengthFailureCost p ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) p).host.extCosts savedCharges := by
    change p.host.extCosts.cost "base" + p.host.extCosts.cost "utf8_decoding_base" ≤ burnSum p.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logLengthFailureAttemptBudget_eq, executionBudget_eq]
  omega

/-- Sufficient original gas matches log-count rejection and bounds actual used gas. -/
theorem execOn_log_count (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0) (hnodes : ctx.trie.NonzeroNodes)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ((model gasBound).step ctx st ()) ∧
      (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  have hr := resources ctx raw hwf hp hnodes hkey hvalue hgas hproof
  have hc := hr.credits.mono (log_budget_le ctx raw (post ctx raw) (storageCost ctx raw) 0)
  have hz : (post ctx raw).host.config.maxNumberLogs = some 0 := by
    have he := congrArg NearConfig.maxNumberLogs (hr.frame.config.trans (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw))
    change (post ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs at he
    simpa only [hzero] using he
  refine ⟨execOn_matches_log_zero gasBound ctx raw st (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hkey hvalue hzero hr.frontier hr.frame hc, ?_⟩
  exact (execOn_log_failure_usedGas_le ctx raw (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hz hr.frontier hr.frame hc).trans ((log_budget_le ctx raw _ _ _).trans hr.budget)

/-- Sufficient original gas matches cumulative-log-length rejection. -/
theorem execOn_log_length (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5) (hnodes : ctx.trie.NonzeroNodes)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ((model gasBound).step ctx st ()) ∧
      (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  have hr := resources ctx raw hwf hp hnodes hkey hvalue hgas hproof
  have hc := hr.credits.mono (log_length_budget_le ctx raw (post ctx raw) (storageCost ctx raw) 0)
  have hcfg := hr.frame.config.trans (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hnum : (post ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs :=
    congrArg NearConfig.maxNumberLogs hcfg
  have hlen : (post ctx raw).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength :=
    congrArg NearConfig.maxLogLen hcfg
  have hl : (post ctx raw).host.logs = [] := hr.frame.logs.trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hn : logCountError (post ctx raw) = none := by
    simp [logCountError, hnum, hl, Nat.not_le.mpr hcount]
  refine ⟨execOn_matches_log_length gasBound ctx raw st (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hkey hvalue hcount hshort hr.frontier hr.frame hc, ?_⟩
  exact (execOn_log_length_failure_usedGas_le ctx raw (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hn hl hlen hshort hr.frontier hr.frame hc).trans
    ((log_length_budget_le ctx raw _ _ _).trans hr.budget)

/-- Sufficient original gas matches a rejected return after the real write/log,
with the exposed used gas bounded by the same original canonical gas function. -/
theorem execOn_return_length (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hnodes : ctx.trie.NonzeroNodes)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ((model gasBound).step ctx st ()) ∧
      (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  have hr := resources ctx raw hwf hp hnodes hkey hvalue hgas hproof
  have hcfg := hr.frame.config.trans (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hnum : (post ctx raw).host.config.maxNumberLogs = some ctx.protocol.wasm.limits.maxNumberLogs :=
    congrArg NearConfig.maxNumberLogs hcfg
  have hlen : (post ctx raw).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength :=
    congrArg NearConfig.maxLogLen hcfg
  have hreturn : (post ctx raw).host.config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData :=
    congrArg NearConfig.maxReturnLen hcfg
  have hl : (post ctx raw).host.logs = [] := hr.frame.logs.trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hn : logCountError (post ctx raw) = none := by
    simp [logCountError, hnum, hl, Nat.not_le.mpr hcount]
  have hspace : 5 ≤ logSpace (post ctx raw) := by
    simpa [logSpace, totalLogLength, hl, hlen] using hloglen
  have hpush : ∀ limit, (post ctx raw).host.config.maxLogLen = some limit → totalLogLength (post ctx raw) + 5 ≤ limit := by
    intro limit he
    have heq := Option.some.inj (hlen.symm.trans he)
    simpa [totalLogLength, hl, ← heq] using hloglen
  have hm := hr.frame.1.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hreg := (congrFun hr.frame.registers 0).trans (storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hext := hr.frame.extCosts.trans (storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hreadPost : (post ctx raw).host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64 := by
    rw [hext]
    exact hread
  refine ⟨execOn_matches_return_length gasBound ctx raw st (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hkey hvalue hcount hloglen hshort hread hr.frontier hr.frame hr.credits, ?_⟩
  exact (execOn_return_length_failure_usedGas_le ctx raw (post ctx raw) (storageCost ctx raw) 0 (written ctx raw)
    hmethod hp hinput hm hreg hreturn hshort hn hspace hreadPost hpush hr.frontier hr.frame hr.credits).trans hr.budget

/-- The ordered output-failure union has the same original sufficient-gas
matching and used-gas bound for any canonical fresh/replacement write. -/
theorem execOn_matches_and_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset) (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (houtput : ctx.protocol.wasm.limits.maxNumberLogs = 0 ∨
      ctx.protocol.wasm.limits.maxTotalLogLength < 5 ∨
      ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
    (hnodes : ctx.trie.NonzeroNodes)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ((model gasBound).step ctx st ()) ∧
      (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  by_cases hz : ctx.protocol.wasm.limits.maxNumberLogs = 0
  · exact execOn_log_count gasBound ctx raw st hmethod hwf hp hinput hkey hvalue hz hnodes hgas hproof
  have hn : 0 < ctx.protocol.wasm.limits.maxNumberLogs := Nat.pos_of_ne_zero hz
  by_cases hl : ctx.protocol.wasm.limits.maxTotalLogLength < 5
  · exact execOn_log_length gasBound ctx raw st hmethod hwf hp hinput hkey hvalue hn hl hnodes hgas hproof
  have hlen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength := by omega
  have hreturn : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length := by
    rcases houtput with h | h | h
    · exact False.elim (hz h)
    · exact False.elim (hl h)
    · exact h
  exact execOn_return_length gasBound ctx raw st hmethod hwf hp hinput hkey hvalue hn hlen hreturn hnodes hread hgas hproof

end WNear.Skeleton.CanonicalFailureBounded
