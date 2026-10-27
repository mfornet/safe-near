import NearVM.MeteredIndirectCall

/-! Verified transfer from a resolved direct call to the identical indirect entry. -/
namespace WNear.Proofs.StateDispatchIndirect
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

theorem run_eq_direct (cfg : WasmConfig) (fuel : Nat) (s : Store NearState)
    (limits : ExecLimits) (base args : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex typeIndex tableAddress address : Nat) (element : UInt32) (table : TableInst)
    (mi : ModuleInst) (type : FuncType) (inst : Nat) (fn : Func)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[functionIndex]? = some address)
    (hta : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[element.toNat]? = some (.func address)) (hty : mi.types[typeIndex]? = some type)
    (hf : s.funcs[address]? = some (.wasm type inst fn)) (ha : args.length = type.params.length)
    (hd : callers.length + 1 < limits.maxCallDepth) (hc : s.host.gas.Credits cfg.regularOpCost) :
    runMetered cfg (fuel + 1) (.next (atCode s limits ((base ++ args).toArray.push (.i32 element)) frame callers (.call_indirect typeIndex 0 :: code))) =
      runMetered cfg (fuel + 1) (.next (atCode s limits (base ++ args).toArray frame callers (.call functionIndex :: code))) := by
  let direct := atCode s limits (base ++ args).toArray frame callers (.call functionIndex :: code)
  let indirect := atCode s limits ((base ++ args).toArray.push (.i32 element)) frame callers (.call_indirect typeIndex 0 :: code)
  let op := cfg.regularOpCost
  have cd : nextInstructionGas cfg direct = op := by simp [direct,op,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge]
  have ci : nextInstructionGas cfg indirect = op := by simp [indirect,op,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge]
  have hb := GasCounter.burn_credits s.host.gas op 0 (hc.mono (by omega))
  have chd : chargeConfig direct op = (atCode (chargedStore s op) limits (base ++ args).toArray frame callers (.call functionIndex :: code),none) :=
    by simp only [direct,chargeConfig,atCode,chargedStore,chargeHost]; exact Prod.ext rfl hb.1
  have chi : chargeConfig indirect op = (atCode (chargedStore s op) limits ((base ++ args).toArray.push (.i32 element)) frame callers (.call_indirect typeIndex 0 :: code),none) :=
    by simp only [indirect,chargeConfig,atCode,chargedStore,chargeHost]; exact Prod.ext rfl hb.1
  have sd := step_call_wasm (chargedStore s op) limits base args frame callers code functionIndex address mi type inst fn hm hi hf ha hd
  have si := step_call_indirect_wasm (chargedStore s op) limits base args frame callers code typeIndex 0 tableAddress address element table mi type inst fn hm hta ht he hty hf ha hd
  change runMetered cfg (fuel + 1) (.next indirect) = runMetered cfg (fuel + 1) (.next direct)
  simp only [runMetered,ci,cd,chi,chd,si,sd]
  simp only [frameTransitionGas,atCode,Config.callDepth,List.length_cons]

/-- This proof rule reuses an already proved concrete direct-call contract;
its conclusion executes the real table/type checked indirect opcode. -/
theorem wp_of_direct (cfg : WasmConfig) (fuel credits : Nat) (s : Store NearState)
    (limits : ExecLimits) (base args : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex typeIndex tableAddress address : Nat) (element : UInt32) (table : TableInst)
    (mi : ModuleInst) (type : FuncType) (inst : Nat) (fn : Func) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[functionIndex]? = some address)
    (hta : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[element.toNat]? = some (.func address)) (hty : mi.types[typeIndex]? = some type)
    (hf : s.funcs[address]? = some (.wasm type inst fn)) (ha : args.length = type.params.length)
    (hd : callers.length + 1 < limits.maxCallDepth) (hop : cfg.regularOpCost ≤ credits)
    (h : WP cfg (fuel + 1) (.next (atCode s limits (base ++ args).toArray frame callers (.call functionIndex :: code))) credits post) :
    WP cfg (fuel + 1) (.next (atCode s limits ((base ++ args).toArray.push (.i32 element)) frame callers (.call_indirect typeIndex 0 :: code))) credits post := by
  unfold WP at h
  have hc : s.host.gas.Credits credits := by simpa only [StepResult.host,atCode] using h.1
  have hr := run_eq_direct cfg fuel s limits base args frame callers code functionIndex typeIndex tableAddress address element table mi type inst fn hm hi hta ht he hty hf ha hd (hc.mono hop)
  unfold WP
  rw [hr]
  simpa only [Pays,StepResult.host,atCode] using h
end WNear.Proofs.StateDispatchIndirect
