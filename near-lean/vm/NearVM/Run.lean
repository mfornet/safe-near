import NearVM.Interp
import NearVM.Metered
import NearVM.Context
import NearVM.PromiseGraph
import NearVM.GasDistribution
import Wasm.CodeSize

/-!
# `run`: one function call

The `near_vm_runner::run` seam. Resolves the module's imports against the
metered host, validates and instantiates the module, finds the method,
charges contract loading, runs the machine one step at a time charging
`regular_op_cost` per Wasm instruction, and packs the result as a `VMOutcome`.

Instruction charging implements the supported instrumentation rules. Exact
reference fixtures compare gas profiles, but do not establish metering
correctness for every module or state-trie-dependent cost.
-/

namespace Wasm.Near

/-- A fixed interpreter step budget, for callers that run without a context.
Calls default to `fuelFor`, which `NearVM.Fuel` proves enough. -/
def defaultFuel : Nat := 2_000_000_000

/-- A running configuration, or a finished execution with its final store. -/
abbrev Machine := StepResult NearState

-- nearcore divergence: no `max_stack_height` stack-limiter instrumentation; recursion instead
-- traps at call depth 10000, so stack-overflow points differ from nearcore.
/-- nearcore's stack limiter is not modelled; recursion deeper than this
traps with `stackOverflow`. -/
def execLimits : ExecLimits := { maxCallDepth := 10000 }

/-- The largest function body of a module. -/
def moduleBody (m : Module) : Nat := m.funcs.foldl (fun acc f => max acc (Exec.codeSize f.body)) 0

/-- The least gas any charged instruction costs. -/
def minOpCost (cfg : WasmConfig) : Nat := min cfg.regularOpCost cfg.linearOpBaseCost

/-- The per-call burn limit of a context: `max_gas_burnt`, or a view's own. -/
def VMContext.maxBurnt (cfg : RuntimeConfig) (ctx : VMContext) : Nat :=
  match ctx.viewConfig with
  | some v => v.maxGasBurnt
  | none => cfg.wasm.limits.maxGasBurnt

/-- Enough fuel for any call of `code` under `ctx`: one more than the
cheapest-instruction count the burn limit allows, times one more than call
depth times the largest function body. -/
def fuelFor (cfg : RuntimeConfig) (code : Module) (ctx : VMContext) : Nat :=
  (ctx.maxBurnt cfg / minOpCost cfg.wasm + 1) *
    (max 1 execLimits.maxCallDepth * (moduleBody code + 1) + 1)

/-- Map a runtime trap to nearcore's error. -/
def trapError (reason : Trap) (host : NearState) : FunctionCallError :=
  if let some issue := host.lastExecutionIssue then .executionIssue issue else
  match host.lastError with
  | some e => .hostError e
  | none =>
    match reason with
    | .unreachable => .wasmTrap .unreachable
    | .integerDivideByZero | .integerOverflow | .invalidConversionToInteger =>
      .wasmTrap .illegalArithmetic
    | .outOfBoundsMemoryAccess => .wasmTrap .memoryOutOfBounds
    | .outOfBoundsTableAccess | .undefinedElement => .wasmTrap .callIndirectOOB
    | .uninitializedElement => .wasmTrap .indirectCallToNull
    | .indirectCallTypeMismatch => .wasmTrap .incorrectCallIndirectSignature
    | .callStackExhausted => .wasmTrap .stackOverflow
    | .host msg => .hostError (.guestPanic msg)

/-- nearcore's function activation estimate: 64 fixed bytes plus the parameter
and local value sizes, charged in rounded-up eight-byte units. -/
def activationGas (opCost : Nat) (locals : Array Value) : Nat :=
  let size : Value → Nat
    | .i32 _ | .f32 _ => 4
    | _ => 8
  ((64 + (locals.toList.map size).sum + 7) / 8) * opCost

def linearInstruction : Instr → Bool
  | .memory_grow | .memory_fill | .memory_copy | .memory_init _
  | .table_grow _ | .table_fill _ | .table_copy .. | .table_init .. => true
  | _ => false

/-- The stepper resumes a loop's body directly on a back-edge. nearcore's
instrumentation charges the `loop` operator again on every such iteration
(`finite-wasm::gas::visit_loop`), so that implicit re-entry needs a charge. -/
def loopBackedge (c : Config NearState) (instr : Instr) : Bool :=
  match instr with
  | .br depth => c.labelIsLoop depth
  | .br_if depth =>
    match c.stackTop? with
    | some (.i32 n) => n != 0 && c.labelIsLoop depth
    | _ => false
  | .br_table targets fallback =>
    match c.stackTop? with
    | some (.i32 index) => c.labelIsLoop (targets[index.toNat]?.getD fallback)
    | _ => false
  | _ => false

/-- Operator costs are paid before executing the instruction, so `used_gas`
and observable host side effects see the charge. Fall-through has no opcode. -/
def nextInstructionGas (cfg : WasmConfig) (c : Config NearState) : Nat :=
  match c.nextInstr? with
  | none | some (.block ..) => 0
  | some instr =>
    if linearInstruction instr then
      let amount := match c.stackTop? with
        | some (.i32 n) => n.toNat
        | _ => 0
      cfg.linearOpBaseCost + cfg.linearOpUnitCost * amount
    else cfg.regularOpCost + (if loopBackedge c instr then cfg.regularOpCost else 0)

/-- Entering a new frame costs its activation. -/
def frameTransitionGas (cfg : WasmConfig) (before : Config NearState) (after : Machine) : Nat :=
  match after with
  | .next next =>
    if next.callDepth > before.callDepth then activationGas cfg.regularOpCost next.locals else 0
  | _ => 0

/-- Burn Wasm gas on the host state. -/
def chargeHost (host : NearState) (cost : Nat) : NearState × Option HostError :=
  let r := host.gas.burn cost
  ({ host with gas := r.1, gasProfile := { host.gasProfile with
    wasm := host.gasProfile.wasm + (r.1.burnt - host.gas.burnt) } }, r.2)

def chargeConfig (c : Config NearState) (cost : Nat) : Config NearState × Option HostError :=
  let r := chargeHost c.store.host cost
  ({ c with store := { c.store with host := r.1 } }, r.2)

def chargeWasm (m : Machine) (cost : Nat) : Machine × Option HostError :=
  match m with
  | .next c =>
    let r := chargeConfig c cost
    (.next r.1, r.2)
  | .done values store =>
    let r := chargeHost store.host cost
    (.done values { store with host := r.1 }, r.2)
  | .trap reason store =>
    let r := chargeHost store.host cost
    (.trap reason { store with host := r.1 }, r.2)

/-- Run the stepper, charging instruction and frame costs, until the call ends
or gas runs out. Returns the final machine state and, on gas exhaustion, the
error. Written with projections rather than pattern bindings so that proofs
can split on the two charge outcomes directly. -/
def runMetered (cfg : WasmConfig) : Nat → Machine → Machine × Option FunctionCallError
  | 0, .next c => (.next c, some (.executionIssue .fuelExhausted))
  | 0, m => (m, none)
  | fuel + 1, .next c =>
    let charged := chargeConfig c (nextInstructionGas cfg c)
    match charged.2 with
    | some error => (.next charged.1, some (.hostError error))
    | none =>
      let next := Exec.step charged.1
      let charged' := chargeWasm next (frameTransitionGas cfg charged.1 next)
      match charged'.2 with
      | some error => (charged'.1, some (.hostError error))
      | none => runMetered cfg fuel charged'.1
  | _ + 1, m => (m, none)

/-- `runMetered` as it runs. `runMetered` reads the configuration before a
step after the step (for the call depth), so the step ran on a shared store
and copied memory pages; this reads the depth first. -/
def runMeteredInPlace (cfg : WasmConfig) : Nat → Machine → Machine × Option FunctionCallError
  | 0, .next c => (.next c, some (.executionIssue .fuelExhausted))
  | 0, m => (m, none)
  | fuel + 1, .next c =>
    let charged := chargeConfig c (nextInstructionGas cfg c)
    match charged.2 with
    | some error => (.next charged.1, some (.hostError error))
    | none =>
      let depth := charged.1.callDepth
      let next := Exec.step charged.1
      let gas := match next with
        | .next next => if next.callDepth > depth then activationGas cfg.regularOpCost next.locals else 0
        | _ => 0
      let charged' := chargeWasm next gas
      match charged'.2 with
      | some error => (charged'.1, some (.hostError error))
      | none => runMeteredInPlace cfg fuel charged'.1
  | _ + 1, m => (m, none)

@[csimp] theorem runMetered_eq_inPlace : @runMetered = @runMeteredInPlace := by
  funext cfg fuel m
  induction fuel generalizing m with
  | zero => cases m <;> rfl
  | succ fuel ih =>
    cases m with
    | next c =>
      simp only [runMetered, runMeteredInPlace, frameTransitionGas]
      generalize chargeConfig c (nextInstructionGas cfg c) = charged
      rcases charged with ⟨c, _ | error⟩
      · simp only
        generalize chargeWasm _ _ = charged
        rcases charged with ⟨m, _ | error⟩
        · exact ih m
        · rfl
      · rfl
    | done => rfl
    | trap => rfl

/-- Fuel exhaustion is an interpreter limit, not protocol gas exhaustion. -/
@[simp] theorem runMetered_zero (cfg : WasmConfig) (c : Config NearState) :
    runMetered cfg 0 (.next c) = (.next c, some (.executionIssue .fuelExhausted)) := rfl

/-- A completed execution needs no further interpreter steps. -/
theorem runMetered_done (cfg : WasmConfig) (fuel : Nat) (values : List Value)
    (store : Store NearState) : runMetered cfg fuel (.done values store) = (.done values store, none) := by
  cases fuel <;> rfl

/-- The stepper preserves a terminal trap for the caller to classify. -/
theorem runMetered_trapped (cfg : WasmConfig) (fuel : Nat) (reason : Trap)
    (store : Store NearState) : runMetered cfg fuel (.trap reason store) = (.trap reason store, none) := by
  cases fuel <;> rfl

def finalStorage (ns : NearState) : List (List UInt8 × List UInt8) :=
  ns.storageKeys.filterMap fun k => (ns.storage k).map fun v => (k, v)

def logsOf (ns : NearState) : List String :=
  ns.logs.map fun l => (String.fromUTF8? ⟨l.toArray⟩).getD ""

/-- Outcome of a call that did not run: nothing burnt beyond `burnt`. -/
def VMOutcome.failedBefore (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (burnt : Nat) (e : FunctionCallError) (profile : GasProfile := {}) : VMOutcome :=
  { balance := ctx.accountBalance, storageUsage := ctx.storageUsage, returnData := .none,
    burntGas := burnt, usedGas := burnt, logs := [], storage := storage, receipts := [],
    aborted := some e, gasProfile := profile, storageAccounting := ctx.storageAccounting }

/-- The activation charge of the entry frame. -/
def entryCost (cfg : WasmConfig) : Machine → Nat
  | .next c => activationGas cfg.regularOpCost c.locals
  | _ => 0

/-- Charge function entry and execute the metered loop, retaining an entry
charge failure as a structured protocol error. -/
def runInitialized (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    Machine × Option FunctionCallError :=
  let charged := chargeWasm m (entryCost cfg m)
  match charged.2 with
  | some error => (charged.1, some (.hostError error))
  | none => runMetered cfg fuel charged.1

/-- Build the VM result from a terminal or stopped execution. Failed calls
retain burnt gas and logs while restoring their input financial/storage state. -/
def outcomeOfExecution (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (final : Machine) (err : Option FunctionCallError) : VMOutcome :=
  let ns := final.host
  let aborted : Option FunctionCallError :=
    match err with
    | some e => some e
    | none =>
      match final with
      | .trap reason _ => some (trapError reason ns)
      | _ => none
  match aborted with
  | some e =>
    { balance := ctx.accountBalance, storageUsage := ctx.storageUsage, returnData := .none,
      burntGas := ns.gas.burnt, usedGas := ns.gas.burnt, logs := logsOf ns, storage := storage,
      receipts := [], aborted := some e, gasProfile := ns.gasProfile,
      subsidizedAmount := ns.subsidizedAmount, storageAccounting := ns.storageAccounting,
      actionProfile := ns.actionProfile }
  | none =>
    let outcome : VMOutcome := {
      balance := ns.context.accountBalance, storageUsage := ns.context.storageUsage.toNat
      returnData := .none, burntGas := ns.gas.burnt, usedGas := ns.gas.used
      logs := logsOf ns, storage := finalStorage ns, receipts := [], aborted := none
      gasProfile := ns.gasProfile, subsidizedAmount := ns.subsidizedAmount,
      storageAccounting := ns.storageAccounting, storageWrites := ns.storageLog.reverse,
      actionProfile := ns.actionProfile }
    match convertPromises ns.promises with
    | none => outcome.graphIssue ctx.accountBalance ctx.storageUsage storage
    | some graph =>
      let returned := graph.returnData? ns
      match returned with
      | none => outcome.graphIssue ctx.accountBalance ctx.storageUsage storage
      | some returnData =>
        let distributed := distributeGas (ctx.prepaidGas - ns.gas.used) graph.handles ns.gasWeights
          graph.receipts
        { outcome with
          returnData := returnData
          resumes := ns.yieldResumes
          receipts := distributed.1
          usedGas := ns.gas.used + distributed.2
          distributedGas := distributed.2 }

/-- A host function nearcore does not link at this protocol version (`imports.rs`: the
`#[global_contract_host_fns]`, `#[chain_id_host_fn]`, `#[p256_verify_host_fn]`,
`#[gas_key_host_fns]` and `#[yield_with_id_host_fns]` imports). Importing one fails to link. -/
def disabledHost (cfg : RuntimeConfig) (name : String) : Bool :=
  (!cfg.wasm.globalContractHostFns &&
    ["promise_batch_action_deploy_global_contract", "promise_batch_action_deploy_global_contract_by_account_id",
     "promise_batch_action_use_global_contract", "promise_batch_action_use_global_contract_by_account_id"].contains name) ||
  (!cfg.wasm.chainIdHostFn && name == "chain_id") ||
  (!cfg.wasm.p256VerifyHostFn && name == "p256_verify") ||
  (!cfg.wasm.gasKeyHostFns &&
    ["promise_batch_action_transfer_to_gas_key", "promise_batch_action_add_gas_key_with_full_access",
     "promise_batch_action_add_gas_key_with_function_call"].contains name) ||
  (!cfg.wasm.yieldWithIdHostFns &&
    ["promise_yield_create_with_id", "promise_yield_resume_with_yield_id"].contains name)

/-- nearcore's `prepare_v3` limits, checked in its section order: types,
imports (`env` functions only, counted as functions), tables and their
initial size, defined functions, then each body's size and locals.
nearcore divergence: nearcore interleaves these with validation, so a module
that is both invalid and over a limit may report the other error first. -/
def prepareLimitError (limits : LimitConfig) (code : Module) : Option PrepareError := Id.run do
  let within (limit : Option Nat) (n : Nat) := limit.all (n ≤ ·)
  if !within limits.maxTypesPerContract code.types.size then return some .tooManyTypes
  let mut functions := 0
  for imp in code.imports do
    if imp.module != "env" then return some .instantiate
    match imp.desc with
    | .func _ =>
      functions := functions + 1
      if !within limits.maxFunctionsNumberPerContract functions then return some .tooManyFunctions
    | .table _ | .global _ => return some .instantiate
    | .mem _ => return some .memory
  if !within limits.maxTablesPerContract code.tables.size then return some .tooManyTables
  if code.tables.any (fun table => !within limits.maxElementsPerContractTable table.type.limits.min) then
    return some .tooManyTableElements
  if !within limits.maxFunctionsNumberPerContract (functions + code.funcs.size) then
    return some .tooManyFunctions
  let mut locals := 0
  for fn in code.funcs do
    if !within limits.maxFunctionBodySize fn.bodySize then return some .functionBodyTooLarge
    locals := locals + fn.locals.length
    if !within limits.maxLocalsPerContract locals then return some .tooManyLocals
  return none

/-- nearcore replaces the contract's memory declaration during preparation. -/
def prepareMemory (cfg : RuntimeConfig) (code : Module) : Module :=
  { code with mems := code.mems.map fun _ => { type := { limits := {
      min := cfg.wasm.limits.initialMemoryPages,
      max := some cfg.wasm.limits.maxMemoryPages } } } }

/-- The charges for loading a contract of `codeSize` bytes. -/
def loadingCharges (codeSize : Nat) : List Charge :=
  [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]

/-- Execute `method` of `code` under `ctx` on `storage`. `codeSize` is the
byte size of the deployed Wasm (the loading cost depends on it). -/
def runAttempt (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (fuel : Nat := fuelFor cfg code ctx) : VMOutcome :=
  if method.isEmpty then
    VMOutcome.failedBefore ctx storage 0 (.methodResolveError .methodEmptyName)
  else
  -- A module nearcore cannot prepare yields a no-op outcome: nothing is burnt.
  match prepareLimitError cfg.wasm.limits code with
  | some e => VMOutcome.failedBefore ctx storage 0 (.prepareError e)
  | none =>
  let host0 := ctx.toNearState cfg storage
  -- contract loading
  let (host1, loadErr) := applyCharges host0 (loadingCharges codeSize)
  let gas1 := host1.gas
  match loadErr with
  | some e => VMOutcome.failedBefore ctx storage gas1.burnt (.hostError e) host1.gasProfile
  | none =>
  let code := prepareMemory cfg code
  match code.validate (Features.nearcore true) with
  | .error e =>
    VMOutcome.failedBefore ctx storage gas1.burnt (.compilationError e.message) host1.gasProfile
  | .ok valid =>
  -- nearcore divergence: a module with a start function is an execution issue, never run.
  -- nearcore runs a start function as a metered export before the method;
  -- no contract in the dataset has one, and the model does not support it.
  if code.start.isSome then
    VMOutcome.failedBefore ctx storage gas1.burnt
      (.executionIssue (.interpreterError "start function")) host1.gasProfile
  else
  -- nearcore links a gated host only when its protocol feature is on, and links
  -- before it looks the method up.
  if code.importDecls.any (fun decl => decl.module == "env" && disabledHost cfg decl.name) then
    VMOutcome.failedBefore ctx storage gas1.burnt (.linkError "unknown or invalid import") host1.gasProfile
  else
  -- Legacy protocols discard the loading charge on method-resolution failure,
  -- but loading exhaustion still takes precedence over an absent export.
  let methodErrorGas := if cfg.wasm.fixContractLoadingCost then gas1.burnt else 0
  let methodProfile := if cfg.wasm.fixContractLoadingCost then host1.gasProfile else {}
  match code.exportFunc? method with
  | none =>
    VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodNotFound)
      methodProfile
  | some entry =>
  match code.funcType? entry with
  | none =>
    VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodNotFound)
      methodProfile
  | some sig =>
  if !(sig.params.isEmpty && sig.results.isEmpty) then
    VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodInvalidSignature)
      methodProfile
  else
  match resolveMetered cfg code with
  | .error imp =>
    -- nearcore divergence: v86 imports `promise_set_refund_to`, `promise_batch_action_state_init*`,
    -- `set_state_init_data_entry`, `current_contract_code` and `refund_to_account_id` are missing.
    -- The registry is not yet a complete protocol host inventory. Failure to
    -- resolve an import cannot establish that nearcore would reject it.
    VMOutcome.failedBefore ctx storage gas1.burnt
      (.executionIssue (.unsupportedHost imp)) host1.gasProfile
  | .ok env =>
  let (store, imports) := env.allocate (Store.empty host1)
  match Link.instantiateModule store valid imports with
  | .error e => VMOutcome.failedBefore ctx storage gas1.burnt (.linkError e.message) host1.gasProfile
  | .ok (store, inst) =>
  -- A method is a Wasm function; exporting an import under a method name is a
  -- model gap, not a protocol error.
  match Exec.startWasm store execLimits inst.funcAddrs[entry]! [] with
  | none =>
    VMOutcome.failedBefore ctx storage gas1.burnt
      (.executionIssue (.interpreterError "method is an imported function")) host1.gasProfile
  | some c =>
  let (final, err) := runInitialized cfg.wasm fuel (.next c)
  outcomeOfExecution ctx storage final err

/-- The public VM boundary validates converted receipts on every exit. Raw
promise handles are resolved by the proved total converter in `runAttempt`. -/
def run (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (fuel : Nat := fuelFor cfg code ctx) : VMOutcome :=
  (runAttempt cfg code codeSize method ctx storage fuel).checkReceipts
    ctx.accountBalance ctx.storageUsage storage

/-- Every executable VM result has a checked, backward-only receipt graph and
an existing returned receipt, including failed or incomplete attempts. -/
theorem run_receipts_valid (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).receiptsValid = true := by
  exact checkReceipts_valid _ ctx.accountBalance ctx.storageUsage storage

theorem run_no_receipt_cycle (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel index : Nat) :
    ¬ReceiptDependencyPath (run cfg code codeSize method ctx storage fuel).receipts index index :=
  no_receipt_dependency_cycle
    ((run cfg code codeSize method ctx storage fuel).receiptsWellFormed
      (run_receipts_valid cfg code codeSize method ctx storage fuel)) index

theorem run_dependency_before (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat)
    {source target : Nat} {receipt : ReceiptSpec}
    (hlookup : (run cfg code codeSize method ctx storage fuel).receipts[source]? = some receipt)
    (hmember : target ∈ receipt.dependencies) : target < source :=
  dependencyPath_decreases
    ((run cfg code codeSize method ctx storage fuel).receiptsWellFormed
      (run_receipts_valid cfg code codeSize method ctx storage fuel))
    (.edge hlookup hmember)

theorem run_returnedReceipt_lt (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat) {index : Nat}
    (hreturn : (run cfg code codeSize method ctx storage fuel).returnData = .receiptIndex index) :
    index < (run cfg code codeSize method ctx storage fuel).receipts.length :=
  (run cfg code codeSize method ctx storage fuel).returnedReceipt_lt
    (run_receipts_valid cfg code codeSize method ctx storage fuel) hreturn

/-! ## How an attempt's outcome arises

Every consumer of `runAttempt` needs the same case analysis: either the call
failed before running, burning at most the loading charge, or the machine ran
from a Wasm entry of the instantiated module. -/

theorem runAttempt_cases (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat) :
    (∃ host1 loadErr burnt e profile,
      applyCharges (ctx.toNearState cfg storage) (loadingCharges codeSize) = (host1, loadErr) ∧
      burnt ≤ host1.gas.burnt ∧
      runAttempt cfg code codeSize method ctx storage fuel =
        VMOutcome.failedBefore ctx storage burnt e profile) ∨
    (∃ (host1 : NearState) (env : HostEnv NearState) (store : Store NearState)
      (imports : List ExternVal) (valid : ValidModule) (store' : Store NearState)
      (inst : ModuleInst) (entry : Nat) (c : Config NearState),
      applyCharges (ctx.toNearState cfg storage) (loadingCharges codeSize) = (host1, none) ∧
      resolveMetered cfg (prepareMemory cfg code) = .ok env ∧
      env.allocate (Store.empty host1) = (store, imports) ∧
      Link.instantiateModule store valid imports = .ok (store', inst) ∧
      Exec.startWasm store' execLimits inst.funcAddrs[entry]! [] = some c ∧
      runAttempt cfg code codeSize method ctx storage fuel =
        outcomeOfExecution ctx storage (runInitialized cfg.wasm fuel (.next c)).1
          (runInitialized cfg.wasm fuel (.next c)).2) := by
  unfold runAttempt
  dsimp only
  split
  · left
    exact ⟨_, _, 0, _, _, rfl, Nat.zero_le _, rfl⟩
  · split
    · left
      exact ⟨_, _, 0, _, _, rfl, Nat.zero_le _, rfl⟩
    · cases hload : applyCharges (ctx.toNearState cfg storage) (loadingCharges codeSize) with
      | mk host1 loadErr =>
        dsimp only
        cases loadErr with
        | some e => left; exact ⟨host1, some e, _, _, _, rfl, Nat.le_refl _, rfl⟩
        | none =>
          dsimp only
          have hle : (if cfg.wasm.fixContractLoadingCost then host1.gas.burnt else 0) ≤
              host1.gas.burnt := by
            split
            · exact Nat.le_refl _
            · exact Nat.zero_le _
          split
          · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
          · split
            · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
            · split
              · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
              · split
                · left; exact ⟨host1, none, _, _, _, rfl, hle, rfl⟩
                · split
                  · left; exact ⟨host1, none, _, _, _, rfl, hle, rfl⟩
                  · split
                    · left; exact ⟨host1, none, _, _, _, rfl, hle, rfl⟩
                    · split
                      · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
                      · rename_i env hresolve
                        cases halloc : env.allocate (Store.empty host1) with
                        | mk store imports =>
                          dsimp only
                          split
                          · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
                          · rename_i result store' inst hinst
                            split
                            · left; exact ⟨host1, none, _, _, _, rfl, Nat.le_refl _, rfl⟩
                            · rename_i c hstart
                              right
                              exact ⟨host1, env, store, imports, _, store', inst, _, c, rfl, hresolve,
                                halloc, hinst, hstart, rfl⟩

end Wasm.Near
