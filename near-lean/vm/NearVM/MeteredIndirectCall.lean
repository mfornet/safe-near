import NearVM.MeteredWasmCall

/-! Metered indirect Wasm calls derived from runtime table/type lookups. -/
namespace Wasm.Near.MeteredLogic

/-- A present function reference and matching signature determine actual entry. -/
theorem step_call_indirect_wasm (store : Store NearState) (limits : ExecLimits)
    (base args : List Value) (caller : CallFrame) (callers : List CallFrame)
    (rest : List Instr) (typeIndex tableIndex tableAddress address : Nat) (element : UInt32) (table : TableInst) (mi : ModuleInst)
    (type : FuncType) (inst : Nat) (code : Func)
    (hmodule : store.modules[caller.inst]? = some mi)
    (htableAddress : mi.tableAddrs[tableIndex]? = some tableAddress)
    (htable : store.tables[tableAddress]? = some table)
    (helement : table.elems[element.toNat]? = some (.func address))
    (htype : mi.types[typeIndex]? = some type)
    (hfunction : store.funcs[address]? = some (.wasm type inst code))
    (hargs : args.length = type.params.length)
    (hdepth : callers.length + 1 < limits.maxCallDepth) :
    Exec.step (atCode store limits ((base ++ args).toArray.push (.i32 element)) caller callers
      (.call_indirect typeIndex tableIndex :: rest)) =
      .next (wasmCallee store limits base caller callers rest type inst code args) := by
  have hp := popN_arguments base args
  rw [hargs] at hp
  simp [Exec.step, Exec.instr, Exec.enter, Exec.Effect.call, atCode,
    getElem!_def, hmodule, htableAddress, htable, helement, htype, hfunction, hp, Exec.tableOf, Exec.i32, FuncInst.type, wasmCallee, wasmLocals,
    show ¬callers.length + 1 ≥ limits.maxCallDepth by omega]

/-- Charge the indirect-call opcode and actual callee frame, preserving the
operand prefix and arbitrary caller frames without an execution premise. -/
theorem wp_call_indirect_wasm (cfg : WasmConfig) (fuel remaining : Nat) (store : Store NearState)
    (limits : ExecLimits) (base args : List Value) (caller : CallFrame)
    (callers : List CallFrame) (rest : List Instr) (typeIndex tableIndex tableAddress address : Nat) (element : UInt32) (table : TableInst)
    (mi : ModuleInst) (type : FuncType) (inst : Nat) (code : Func) (post : Post)
    (hmodule : store.modules[caller.inst]? = some mi)
    (htableAddress : mi.tableAddrs[tableIndex]? = some tableAddress)
    (htable : store.tables[tableAddress]? = some table)
    (helement : table.elems[element.toNat]? = some (.func address))
    (htype : mi.types[typeIndex]? = some type)
    (hfunction : store.funcs[address]? = some (.wasm type inst code))
    (htypes : args.map Value.type = type.params)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hcredits : store.host.gas.Credits
      (cfg.regularOpCost + (activationGas cfg.regularOpCost (wasmLocals code args) + remaining)))
    (hnext : WP cfg fuel
      (.next (wasmCallee
        (chargedStore (chargedStore store cfg.regularOpCost)
          (activationGas cfg.regularOpCost (wasmLocals code args)))
        limits base caller callers rest type inst code args)) remaining post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits ((base ++ args).toArray.push (.i32 element)) caller callers
        (.call_indirect typeIndex tableIndex :: rest)))
      (cfg.regularOpCost + (activationGas cfg.regularOpCost (wasmLocals code args) + remaining))
      post := by
  let c := atCode store limits ((base ++ args).toArray.push (.i32 element)) caller callers (.call_indirect typeIndex tableIndex :: rest)
  let op := cfg.regularOpCost
  let activation := activationGas cfg.regularOpCost (wasmLocals code args)
  let first := atCode (chargedStore store op) limits ((base ++ args).toArray.push (.i32 element)) caller callers
    (.call_indirect typeIndex tableIndex :: rest)
  let entered := wasmCallee (chargedStore store op) limits base caller callers rest type inst code args
  have hargs : args.length = type.params.length := by
    have h := congrArg List.length htypes
    simpa using h
  have hcost : nextInstructionGas cfg c = op := by
    simp [c, op, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step first = .next entered :=
    step_call_indirect_wasm (chargedStore store op) limits base args caller callers rest typeIndex tableIndex tableAddress address element table
      mi type inst code hmodule htableAddress htable helement htype hfunction hargs hdepth
  have hframe : frameTransitionGas cfg first (.next entered) = activation := by
    simp [frameTransitionGas, first, entered, wasmCallee, atCode, Config.callDepth,
      Config.locals, activation]
  have hop := Pays.chargeConfig c op (activation + remaining) hcredits
  have hfirst : (chargeConfig c op).1 = first := rfl
  have hentered : entered.store.host.gas.Credits (activation + remaining) := hop.2.2.2.2
  have hactivation := Pays.chargeWasm (.next entered) activation remaining hentered
  have hpure : Pays (.next first) (activation + remaining) (.next entered)
      (activation + remaining) := Pays.of_gas_eq rfl hentered
  apply wp_next hcredits
  · rw [hcost]
    exact Prod.ext hfirst hop.1
  · change chargeWasm (Exec.step first) (frameTransitionGas cfg first (Exec.step first)) = _
    rw [hstep, hframe]
    exact Prod.ext rfl hactivation.1
  · exact hop.2.trans (hpure.trans hactivation.2)
  · exact hnext

end Wasm.Near.MeteredLogic
