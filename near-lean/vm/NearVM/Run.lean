import NearVM.Metered
import NearVM.Context
import NearVM.Outcome

/-!
# `run`: one function call

The `near_vm_runner::run` seam. Resolves the module's imports against the
metered host, finds the method, charges contract loading, runs the
interpreter one step at a time charging `regular_op_cost` per Wasm
instruction, and packs the result as a `VMOutcome`.

Per-instruction charging is currently an approximation to nearcore's
instrumentation. Independent comparisons show discrepancies even on
successful executions. Gas profiles expose host, action, and instruction
contributions so these differences can be resolved against the reference.
-/

namespace Wasm.Near

/-- Interpreter step budget. Exhaustion is explicitly incomplete execution;
this constant is not a proved bound for every protocol-valid execution. -/
def defaultFuel : Nat := 2_000_000_000

/-- Map an interpreter trap to nearcore's error. -/
def trapError (reason : SmallStep.TrapReason) (host : NearState) : FunctionCallError :=
  match host.lastError with
  | some e => .hostError e
  | none =>
    match reason with
    | .unreachable => .wasmTrap .unreachable
    | .integerDivideByZero | .integerOverflow | .invalidConversionToInteger => .wasmTrap .illegalArithmetic
    | .outOfBoundsMemory => .wasmTrap .memoryOutOfBounds
    | .outOfBoundsTable | .undefinedElement | .uninitializedElement _ => .wasmTrap .callIndirectOOB
    | .indirectCallTypeMismatch => .wasmTrap .incorrectCallIndirectSignature
    | .nullFunctionReference => .wasmTrap .indirectCallToNull
    | .host msg => .hostError (.guestPanic msg)
    | _ => .wasmTrap .genericTrap

/-- nearcore's function activation estimate: 64 fixed bytes plus the parameter
and local value sizes, charged in rounded-up eight-byte units. -/
def activationGas (opCost : Nat) (locals : Locals) : Nat :=
  let size : Value → Nat
    | .i32 _ | .f32 _ => 4
    | .v128 _ => 16
    | _ => 8
  ((64 + ((locals.params ++ locals.locals).map size).sum + 7) / 8) * opCost

def linearInstruction : Instruction → Bool
  | .memoryGrow | .memoryFill | .memoryCopy | .memoryInit _
  | .tableGrow _ | .tableFill _ | .tableCopy .. | .tableInit .. => true
  | _ => false

/-- The stepper resumes a loop's body directly on a back-edge. nearcore's
instrumentation charges the `loop` operator again on every such iteration
(`finite-wasm::gas::visit_loop`), so that implicit re-entry needs a charge. -/
def loopBackedge (thread : SmallStep.ThreadState NearState) (instr : Instruction) : Bool :=
  let targetsLoop (depth : Nat) := match thread.control[depth]? with
    | some frame => match frame.kind with | .loop => true | _ => false
    | none => false
  match instr with
  | .br depth => targetsLoop depth
  | .br_if depth =>
    match thread.locals.values.head? with
    | some (.i32 n) => n != 0 && targetsLoop depth
    | _ => false
  | .brTable targets fallback =>
    match thread.locals.values.head? with
    | some (.i32 index) => targetsLoop (targets[index.toNat]?.getD fallback)
    | _ => false
  | _ => false

/-- Operator costs are paid before executing the instruction, so `used_gas`
and observable host side effects see the charge. Fall-through has no opcode. -/
def nextInstructionGas (cfg : WasmConfig) (config : SmallStep.Config NearState) : Nat :=
  match config.expr with
  | .running thread =>
    match thread.code.head? with
      | none | some (.block ..) => 0
      | some instr =>
        if linearInstruction instr then
          let amount := match thread.locals.values.head? with
            | some (.i32 n) => n.toNat
            | _ => 0
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * amount
        else cfg.regularOpCost + (if loopBackedge thread instr then cfg.regularOpCost else 0)
  | _ => 0

def frameTransitionGas (cfg : WasmConfig) (before after : SmallStep.Config NearState) : Nat :=
  match before.expr, after.expr with
  | .running thread, .running next =>
    if next.calls.length > thread.calls.length then activationGas cfg.regularOpCost next.locals else 0
  | _, _ => 0

def chargeWasm (config : SmallStep.Config NearState) (cost : Nat) :
    SmallStep.Config NearState × Option HostError :=
  let host := config.store.wasm.host
  let (gas, error) := host.gas.burn cost
  let host := { host with gas, gasProfile := { host.gasProfile with
    wasm := host.gasProfile.wasm + (gas.burnt - host.gas.burnt) } }
  ({ config with store := { config.store with wasm := { config.store.wasm with host } } }, error)

/-- Run the stepper, charging instruction and frame costs, until the call ends
or gas runs out. Returns the final configuration and, on gas exhaustion, the
error. -/
def runMetered (cfg : WasmConfig) : Nat → SmallStep.Config NearState →
    SmallStep.Config NearState × Option FunctionCallError
  | 0, config =>
    match config.expr with
    | .done _ | .trapped _ => (config, none)
    | .running _ => (config, some (.executionIssue .fuelExhausted))
  | fuel + 1, config =>
    match config.expr with
    | .done _ => (config, none)
    | .trapped _ => (config, none)
    | .running _ =>
      let (paid, error) := chargeWasm config (nextInstructionGas cfg config)
      match error with
      | some error => (paid, some (.hostError error))
      | none =>
        match SmallStep.stepChecked? paid with
        | .error e => (paid, some (.internal e.message))
        | .ok none => (paid, some (.internal "stepper stopped in a running configuration"))
        | .ok (some (_, next)) =>
          let (next, error) := chargeWasm next (frameTransitionGas cfg paid next)
          match error with
          | some error => (next, some (.hostError error))
          | none => runMetered cfg fuel next

/-- Fuel exhaustion is an interpreter limit, not protocol gas exhaustion. -/
@[simp] theorem runMetered_zero (cfg : WasmConfig) (config : SmallStep.Config NearState)
    (h : ∃ thread, config.expr = .running thread) :
    runMetered cfg 0 config = (config, some (.executionIssue .fuelExhausted)) := by
  obtain ⟨thread, h⟩ := h
  simp [runMetered, h]

/-- A completed execution needs no further interpreter steps. -/
theorem runMetered_done (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (h : ∃ values, config.expr = .done values) :
    runMetered cfg fuel config = (config, none) := by
  obtain ⟨values, h⟩ := h
  cases fuel <;> simp [runMetered, h]

/-- The stepper preserves a terminal trap for the caller to classify. -/
theorem runMetered_trapped (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (h : ∃ reason, config.expr = .trapped reason) :
    runMetered cfg fuel config = (config, none) := by
  obtain ⟨reason, h⟩ := h
  cases fuel <;> simp [runMetered, h]

def finalStorage (ns : NearState) : List (List UInt8 × List UInt8) :=
  ns.storageKeys.filterMap fun k => (ns.storage k).map fun v => (k, v)

def logsOf (ns : NearState) : List String :=
  ns.logs.map fun l => (String.fromUTF8? ⟨l.toArray⟩).getD ""

/-- Outcome of a call that did not run: nothing burnt beyond `burnt`. -/
def VMOutcome.failedBefore (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (burnt : Nat) (e : FunctionCallError) (profile : GasProfile := {}) : VMOutcome :=
  { balance := ctx.accountBalance, storageUsage := ctx.storageUsage, returnData := .none,
    burntGas := burnt, usedGas := burnt, logs := [], storage := storage, receipts := [],
    aborted := some e, gasProfile := profile }

/-- Execute `method` of `code` under `ctx` on `storage`. `codeSize` is the
byte size of the deployed Wasm (the loading cost depends on it). -/
private def runAttempt (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (fuel : Nat := defaultFuel) : VMOutcome :=
  if method.isEmpty then
    VMOutcome.failedBefore ctx storage 0 (.methodResolveError .methodEmptyName)
  else
  let host0 := ctx.toNearState cfg storage
  -- contract loading
  let (host1, loadErr) := applyCharges host0 [
    .ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
  let gas1 := host1.gas
  match loadErr with
  | some e => VMOutcome.failedBefore ctx storage gas1.burnt (.hostError e) host1.gasProfile
  | none =>
  -- Legacy protocols discard the loading charge on method-resolution failure,
  -- but loading exhaustion still takes precedence over an absent export.
  let methodErrorGas := if cfg.wasm.fixContractLoadingCost then gas1.burnt else 0
  let methodProfile := if cfg.wasm.fixContractLoadingCost then host1.gasProfile else {}
  match code.findExport method with
  | none => VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodNotFound) methodProfile
  | some entry =>
  match code.funcSig? entry with
  | none => VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodNotFound) methodProfile
  | some sig =>
  if !(sig.params.isEmpty && sig.results.isEmpty) then
    VMOutcome.failedBefore ctx storage methodErrorGas (.methodResolveError .methodInvalidSignature) methodProfile
  else
  match resolveMetered cfg code with
  | .error imp =>
    -- The registry is not yet a complete protocol host inventory. Failure to
    -- resolve an import cannot establish that nearcore would reject it.
    VMOutcome.failedBefore ctx storage gas1.burnt
      (.executionIssue (.unsupportedHost imp)) host1.gasProfile
  | .ok env =>
  -- nearcore replaces the contract's memory declaration during preparation.
  let code := { code with memory := code.memory.map fun decl => { decl with
    pagesMin := UInt32.ofNat cfg.wasm.limits.initialMemoryPages
    pagesMax := some (UInt32.ofNat cfg.wasm.limits.maxMemoryPages) } }
  let store : Store NearState := { (code.initialStore : Store NearState) with host := host1 }
  match SmallStep.initConfig { module := code, host := env } entry store [] with
  | .error e => VMOutcome.failedBefore ctx storage gas1.burnt (.internal e.message) host1.gasProfile
  | .ok config =>
  let entryCost := match config.expr with
    | .running thread => activationGas cfg.wasm.regularOpCost thread.locals
    | _ => 0
  let (entryGas, entryError) := config.store.wasm.host.gas.burn entryCost
  let entryHost := { config.store.wasm.host with
    gas := entryGas
    gasProfile := { config.store.wasm.host.gasProfile with
      wasm := config.store.wasm.host.gasProfile.wasm + (entryGas.burnt - config.store.wasm.host.gas.burnt) } }
  let config := { config with store := { config.store with wasm := { config.store.wasm with host := entryHost } } }
  let (final, err) : SmallStep.Config NearState × Option FunctionCallError := match entryError with
    | some error => (config, some (.hostError error))
    | none => runMetered cfg.wasm fuel config
  let ns := final.store.wasm.host
  let aborted : Option FunctionCallError :=
    match err with
    | some e => some e
    | none =>
      match final.expr with
      | .trapped reason => some (trapError reason ns)
      | _ => none
  match aborted with
  | some e =>
    { balance := ctx.accountBalance, storageUsage := ctx.storageUsage, returnData := .none,
      burntGas := ns.gas.burnt, usedGas := ns.gas.burnt, logs := logsOf ns, storage := storage,
      receipts := [], aborted := some e, gasProfile := ns.gasProfile }
  | none =>
    let returnData : ReturnData :=
      match ns.returnedPromise, ns.returnData with
      | some idx, _ =>
        match returnedReceipt? ns.promises idx with
        | some r => .receiptIndex r
        | none => .none
      | none, some bytes => .value bytes
      | none, none => .none
    VMOutcome.checkPromiseHandles ctx.accountBalance ctx.storageUsage storage ns.promises
    { balance := ns.context.accountBalance, storageUsage := ns.context.storageUsage.toNat,
      returnData := returnData, burntGas := ns.gas.burnt, usedGas := ns.gas.used,
      logs := logsOf ns, storage := finalStorage ns, receipts := promisesToReceipts ns.promises,
      aborted := none, gasProfile := ns.gasProfile }

/-- The public VM boundary validates converted receipts on every exit. Raw
promise handles are checked before a successful outcome can escape `runAttempt`. -/
def run (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (fuel : Nat := defaultFuel) : VMOutcome :=
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

end Wasm.Near
