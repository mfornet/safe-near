import NearVM.MeteredRules

/-! Metered direct Wasm calls from structural function-table facts. -/
namespace Wasm.Near.MeteredLogic

/-- Parameters followed by the declared zero-initialized local variables. -/
def wasmLocals (code : Func) (args : List Value) : Array Value :=
  args.toArray ++ (code.locals.map ValType.default).toArray

/-- A newly entered function above arbitrary caller operands and frames. -/
def wasmCallee (store : Store NearState) (limits : ExecLimits) (base : List Value)
    (caller : CallFrame) (callers : List CallFrame) (rest : List Instr)
    (type : FuncType) (inst : Nat) (code : Func) (args : List Value) : Config NearState :=
  { store, limits, thread := { stack := base.toArray, frames :=
    { locals := wasmLocals code args, inst, arity := type.results.length,
      height := base.length, labels := [], code := code.body } ::
    { caller with code := rest } :: callers } }

/-- The argument suffix is popped without disturbing the caller's operands. -/
theorem popN_arguments (base args : List Value) :
    Exec.popN (base ++ args).toArray args.length = (base.toArray, args) := by
  apply Prod.ext
  · apply Array.toList_inj.mp
    simp [Exec.popN]
  · apply List.ext_getElem
    · simp [Exec.popN]
    · intro k h1 h2
      simp [Exec.popN]

/-- Direct-call execution, before charging the caller opcode or the new frame.
Only table lookups, argument arity and the actual depth limit are premises. -/
theorem step_call_wasm (store : Store NearState) (limits : ExecLimits)
    (base args : List Value) (caller : CallFrame) (callers : List CallFrame)
    (rest : List Instr) (functionIndex address : Nat) (mi : ModuleInst)
    (type : FuncType) (inst : Nat) (code : Func)
    (hmodule : store.modules[caller.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
    (hfunction : store.funcs[address]? = some (.wasm type inst code))
    (hargs : args.length = type.params.length)
    (hdepth : callers.length + 1 < limits.maxCallDepth) :
    Exec.step (atCode store limits (base ++ args).toArray caller callers
      (.call functionIndex :: rest)) =
      .next (wasmCallee store limits base caller callers rest type inst code args) := by
  have hp := popN_arguments base args
  rw [hargs] at hp
  simp [Exec.step, Exec.instr, Exec.enter, Exec.Effect.call, atCode,
    getElem!_def, hmodule, haddress, hfunction, hp, wasmCallee, wasmLocals,
    show ¬callers.length + 1 ≥ limits.maxCallDepth by omega]

/-- Calling a Wasm function pays its opcode and its actual new-frame activation
before the callee continuation. Arguments are typed, all caller operands and
frames are preserved, and locals are initialized by the interpreter itself. -/
theorem wp_call_wasm (cfg : WasmConfig) (fuel remaining : Nat) (store : Store NearState)
    (limits : ExecLimits) (base args : List Value) (caller : CallFrame)
    (callers : List CallFrame) (rest : List Instr) (functionIndex address : Nat)
    (mi : ModuleInst) (type : FuncType) (inst : Nat) (code : Func) (post : Post)
    (hmodule : store.modules[caller.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
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
      (.next (atCode store limits (base ++ args).toArray caller callers
        (.call functionIndex :: rest)))
      (cfg.regularOpCost + (activationGas cfg.regularOpCost (wasmLocals code args) + remaining))
      post := by
  let c := atCode store limits (base ++ args).toArray caller callers (.call functionIndex :: rest)
  let op := cfg.regularOpCost
  let activation := activationGas cfg.regularOpCost (wasmLocals code args)
  let first := atCode (chargedStore store op) limits (base ++ args).toArray caller callers
    (.call functionIndex :: rest)
  let entered := wasmCallee (chargedStore store op) limits base caller callers rest type inst code args
  have hargs : args.length = type.params.length := by
    have h := congrArg List.length htypes
    simpa using h
  have hcost : nextInstructionGas cfg c = op := by
    simp [c, op, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step first = .next entered :=
    step_call_wasm (chargedStore store op) limits base args caller callers rest functionIndex
      address mi type inst code hmodule haddress hfunction hargs hdepth
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

/-- Leaving a completed callee is free and restores the actual saved caller
frame, retaining its arbitrary labels, locals, suffix, and enclosing callers. -/
theorem wp_leave_wasm (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base results : List Value) (frame caller : CallFrame)
    (callers : List CallFrame) (post : Post)
    (harity : results.length = frame.arity) (hheight : frame.height = base.length)
    (hlabels : frame.labels = []) (hcredits : store.host.gas.Credits rest)
    (hnext : WP cfg fuel
      (.next (atCode store limits (base ++ results).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (base ++ results).toArray frame (caller :: callers) []))
      rest post := by
  let c := atCode store limits (base ++ results).toArray frame (caller :: callers) []
  have hz := chargeWasm_zero (.next c) (hcredits.mono (Nat.zero_le rest))
  have hc : chargeConfig c 0 = (c, none) := by
    cases he : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, he] at hz
      cases hz
      rfl
  have hcost : nextInstructionGas cfg c = 0 := rfl
  have hp := popN_arguments base results
  rw [harity] at hp
  have hstep : Exec.step c =
      .next (atCode store limits (base ++ results).toArray caller callers caller.code) := by
    simp [Exec.step, c, atCode, hlabels, Exec.leave, hp, hheight]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost, hc, hstep] at h
  simp only [Nat.zero_add] at h
  apply h hcredits
  · rfl
  · simp [frameTransitionGas, c, atCode, Config.callDepth]
    omega
  · exact hnext

end Wasm.Near.MeteredLogic
