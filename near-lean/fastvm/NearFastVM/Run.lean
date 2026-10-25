import NearFastVM.Exec

/-!
# `run` with the fast engine

`NearFastVM.run` has the signature and the behaviour of `Wasm.Near.run`: it resolves the imports, validates and
instantiates the module and finds the method exactly as `Wasm.Near.runAttempt` does (the code below is that
function, with one change at the end), and then runs the instantiated function with the fast engine instead of
`runInitialized`. When the engine does not run a module (`Exit.unsupported`), or the caller fixes the interpreter
fuel, or the configuration has a free instruction (so that the fuel bound of `NearVM.Fuel` does not hold), the
specification runs instead. The specification is the oracle: `fastvm-differential` compares the two.
-/

namespace NearFastVM

open Wasm Wasm.Near

/-- Whether the specification and the engine agree on the room left: both limits must hold. -/
def gasWithinLimits (host : NearState) : Bool :=
  let g := host.gas
  decide (g.burnt ≤ g.maxBurnt ∧ g.burnt + g.promises ≤ g.prepaid)

/-- The memory of an instance, if it has one: the store address and the instance's limits. -/
def memoryOf (store : Store NearState) (inst : ModuleInst) : Option (Nat × Option Nat) :=
  inst.memAddrs[0]?.bind fun a => (store.mems[a]?).map fun m => (a, m.max)

/-- Run the Wasm function at store address `addr` (a method: no arguments) with the fast engine, from the
state `runInitialized` starts in. `none` if the engine does not run it. -/
def execute (cfg : WasmConfig) (store : Store NearState) (addr : Nat) :
    Option (Machine × Option FunctionCallError) := do
  let some (.wasm ty instIdx code) := store.funcs[addr]? | none
  guard ty.params.isEmpty
  let inst ← store.modules[instIdx]?
  guard
      (inst.memAddrs.size ≤ 1 &&
        inst.types.all fun t => !(t.params.any isRef || t.results.any isRef))
  guard (gasWithinLimits store.host)
  guard
      (inst.globalAddrs.all fun a =>
        match store.globals[a]? with
        | some g => !isRef g.type.type
        | none => false)
  let mem := memoryOf store inst
  guard (mem.isSome || inst.memAddrs.isEmpty)
  let cx : Ctx :=
    { funcs := store.funcs, tables := store.tables, inst, instIdx,
      maxDepth := execLimits.maxCallDepth, regular := cfg.regularOpCost,
      linBase := cfg.linearOpBaseCost, linUnit := cfg.linearOpUnitCost, hasMem := mem.isSome,
      memMax := (mem.bind (·.2)) }
  let entry ← compileFunc cx ty code
  let pg :=
    match mem with
    | some (a, _) => (store.mems[a]!).pages
    | none => #[]
  let gl :=
    inst.globalAddrs.foldl
      (fun gl a =>
        let b := bitsOfVal store.globals[a]!.value
        (gl.push b.toUInt32).push (b >>> 32).toUInt32)
      (#[] : Array UInt32)
  let st : Array UInt32 := Array.replicate (max 2048 entry.frameSlots) 0
  let fns : Array (Option FnCode) := (Array.replicate store.funcs.size none).set! addr (some entry)
  let host := store.host
  let lim := limOf host
  let final : Final :=
    if entry.activation.toUInt64 > lim then gasFail host 0 entry.activation pg gl
    else loop cx fns entry addr 0 0 st gl pg #[] 1 host entry.activation.toUInt64 lim
  -- the store after the run: host state, memory and the mutable globals
  let mems :=
    match mem with
    | some (a, _) => store.mems.modify a fun m => { m with pages := final.pg }
    | none => store.mems
  let globals :=
    Id.run do
      let mut globals := store.globals
      for g in [0:inst.globalAddrs.size] do
        let a := inst.globalAddrs[g]!
        let gi := globals[a]!
        if gi.type.mutable then
          globals :=
            globals.set! a { gi with value := valOfBits gi.type.type (rd final.gl (2 * g).toUSize) }
      return globals
  let store' : Store NearState :=
    { store with
      host := final.host, mems, globals }
  match final.exit with
  | .done values =>
    some (.done values store', none)
  | .trap t =>
    some (.trap t store', none)
  | .gasFail e =>
    some (.done [] store', some (.hostError e))
  | .unsupported =>
    none

/-- What `Wasm.Near.runAttempt` has when it starts the machine: the instantiated store, the entry function's
address and the machine configuration; or the outcome of a call that never ran. -/
inductive Prepared where
  | failed (outcome : VMOutcome)
  | ready (store : Store NearState) (addr : Nat) (c : Config NearState)

/-- The part of `Wasm.Near.runAttempt` before the machine runs (the same steps, in the same order). -/
def prepare (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) : Prepared :=
  if method.isEmpty then
    .failed (VMOutcome.failedBefore ctx storage 0 (.methodResolveError .methodEmptyName))
  else
    let host0 := ctx.toNearState cfg storage
    let (host1, loadErr) := applyCharges host0 (loadingCharges codeSize)
    let gas1 := host1.gas
    match loadErr with
    | some e =>
      .failed (VMOutcome.failedBefore ctx storage gas1.burnt (.hostError e) host1.gasProfile)
    | none =>
      let code := prepareMemory cfg code
      match code.validate (Features.nearcore true) with
      | .error e =>
        .failed
          (VMOutcome.failedBefore ctx storage gas1.burnt (.compilationError e.message)
            host1.gasProfile)
      | .ok valid =>
        if code.start.isSome then
          .failed
            (VMOutcome.failedBefore ctx storage gas1.burnt
              (.executionIssue (.interpreterError "start function")) host1.gasProfile)
        else
          let methodErrorGas := if cfg.wasm.fixContractLoadingCost then gas1.burnt else 0
          let methodProfile := if cfg.wasm.fixContractLoadingCost then host1.gasProfile else {}
          match code.exportFunc? method with
          | none =>
            .failed
              (VMOutcome.failedBefore ctx storage methodErrorGas
                (.methodResolveError .methodNotFound) methodProfile)
          | some entry =>
            match code.funcType? entry with
            | none =>
              .failed
                (VMOutcome.failedBefore ctx storage methodErrorGas
                  (.methodResolveError .methodNotFound) methodProfile)
            | some sig =>
              if !(sig.params.isEmpty && sig.results.isEmpty) then
                .failed
                  (VMOutcome.failedBefore ctx storage methodErrorGas
                    (.methodResolveError .methodInvalidSignature) methodProfile)
              else
                match resolveMetered cfg code with
                | .error imp =>
                  .failed
                    (VMOutcome.failedBefore ctx storage gas1.burnt
                      (.executionIssue (.unsupportedHost imp)) host1.gasProfile)
                | .ok env =>
                  let (store, imports) := env.allocate (Store.empty host1)
                  match Link.instantiateModule store valid imports with
                  | .error e =>
                    .failed
                      (VMOutcome.failedBefore ctx storage gas1.burnt (.linkError e.message)
                        host1.gasProfile)
                  | .ok (store, inst) =>
                    match Exec.startWasm store execLimits inst.funcAddrs[entry]! [] with
                    | none =>
                      .failed
                        (VMOutcome.failedBefore ctx storage gas1.burnt
                          (.executionIssue (.interpreterError "method is an imported function"))
                          host1.gasProfile)
                    | some c => .ready store inst.funcAddrs[entry]! c

/-- `Wasm.Near.runAttempt` with the fast engine. -/
def runAttempt (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Option Nat := none) :
    VMOutcome :=
  match prepare cfg code codeSize method ctx storage with
  | .failed outcome => outcome
  | .ready store addr c =>
    let slow : Unit → VMOutcome := fun _ =>
      let (final, err) := runInitialized cfg.wasm (fuel.getD (fuelFor cfg code ctx)) (.next c)
      outcomeOfExecution ctx storage final err
    if fuel.isSome || minOpCost cfg.wasm == 0 then slow ()
    else
      match execute cfg.wasm store addr with
      | some (final, err) => outcomeOfExecution ctx storage final err
      | none => slow ()

/-- `Wasm.Near.run` with the fast engine. -/
def run (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (fuel : Option Nat := none) : VMOutcome :=
  (runAttempt cfg code codeSize method ctx storage fuel).checkReceipts ctx.accountBalance
    ctx.storageUsage storage

end NearFastVM
