import Proofs.StateDispatchLengthBody
import NearVM.MeteredWasmCall

/-! Actual typed f440 call from original initialized interface resources. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode acquired high low checked arguments returned cleaned finalStore
set_option maxRecDepth 16384

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.interface,.i32 p.input,.i32 0,.i64 0,.i64 0],inst,arity := 1,height,labels := [],code := []}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (12 * op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) := finalStore cfg (entered s cfg.regularOpCost) p

theorem Ready.charge (s : Store NearState) (amount : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra) :
    Ready (chargedStore s amount) limits frame callers p extra := by
  have pc := hr.prefixReady
  have newPrefix : StateDispatchPrefix.Ready (chargedStore s amount) limits frame callers p.toLayout 2 := {
    code := pc.code.transport s (chargedStore s amount) p.toLayout frame.inst rfl rfl rfl
    interfaceLocal := pc.interfaceLocal
    localSize := pc.localSize
    slotNe := pc.slotNe
    memory := pc.memory
    global := pc.global
    sp := pc.sp
    memoryWf := pc.memoryWf
    interfaceBound := pc.interfaceBound
    interfaceRead := pc.interfaceRead
    threadBound := pc.threadBound
    threadStatus := pc.threadStatus
    cellBound := pc.cellBound
    acquireOutBound := pc.acquireOutBound
    countAccepted := pc.countAccepted
    depth := pc.depth }
  exact ⟨hr.code.transport s (chargedStore s amount) p frame.inst extra rfl rfl rfl,newPrefix,hr.inputLocal,hr.localSize,
    hr.highBound,hr.lowBound,hr.selectBound,hr.selectedNonzero,hr.cellBound,hr.inputBound,hr.vtableBound,hr.releaseBound,hr.counterBound⟩

private theorem tail_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (99 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest)) :
    (StateDispatchLengthTail.after cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have b0 : 7 * op + (92 * op + s.host.extCosts.cost "base" + rest) ≤ 99 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest := by dsimp [op]; omega
  have b1 : 13 * op + s.host.extCosts.cost "base" + (79 * op + rest) ≤ 92 * op + s.host.extCosts.cost "base" + rest := by omega
  have b2 : 45 * op + (34 * op + rest) ≤ 79 * op + rest := by omega
  have ca := paid_credits s op 7 (92 * op + s.host.extCosts.cost "base" + rest) (hc.mono b0)
  have hostCredits : (StateDispatchLengthTail.arguments s op).host.gas.Credits
      (13 * cfg.regularOpCost + (StateDispatchLengthTail.arguments s op).host.extCosts.cost "base" + (79 * op + rest)) := by
    simpa only [StateDispatchLengthTail.arguments,paid,chargedStore,chargeHost,op] using ca.mono b1
  have ch := StateDispatchLengthGas.host_credits cfg (StateDispatchLengthTail.arguments s op) p.mi (79 * op + rest) hostCredits
  have cc := StateDispatchLengthGas.cleanup_credits (StateDispatchLengthTail.returned cfg s p) op p.memoryIndex (34 * op + rest)
    (counter p) (lowMemory p) (ch.mono b2)
  exact StateDispatchLengthGas.finish_credits (StateDispatchLengthTail.cleaned cfg s p) op p.globalIndex rest (scratch p) cc

theorem final_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (241 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest)) :
    (finalStore cfg s p).host.gas.Credits rest := by
  rw [←tail_after_eq]
  exact tail_credits cfg (checked s cfg.regularOpCost p) p rest (checked_credits cfg s p rest hc)

/-- Complete actual f440 call: twelve-unit activation, initialized lookup and
borrow, register_len dispatch, release, accepted f432, and normal return. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hr : Ready s limits (leafFrame frame.inst base.length p) ({frame with code} :: callers) p extra)
    (hi : p.mi.funcAddrs[440]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatchLength.signature frame.inst WNear.Binary.StateDispatchLength.function))
    (hc : s.host.gas.Credits (254 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p) limits
      (base ++ [Value.i64 (StateReadRegister.lengthValue s (register p))]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 164) (.next (atCode s limits (base ++ [Value.i32 p.interface,.i32 p.input]).toArray frame callers (.call 440 :: code)))
      (254 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  let result := StateReadRegister.lengthValue s (register p)
  have b0 : op + (12 * op + (241 * op + s.host.extCosts.cost "base" + rest)) ≤ 254 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest := by dsimp [op]; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; simp only [List.length_cons] at *; omega
  have c0 := (GasCounter.burn_credits s.host.gas op (12 * op + (241 * op + s.host.extCosts.cost "base" + rest)) (hc.mono b0)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (12 * op) (241 * op + s.host.extCosts.cost "base" + rest) c0).2.2.2
  have ca : active.host.gas.Credits (241 * cfg.regularOpCost + active.host.extCosts.cost "base" + rest) := by
    simpa only [active,entered,chargedStore,chargeHost,op] using c1
  have ra := (hr.charge s op limits leaf (saved :: callers) p extra).charge (chargedStore s op) (12 * op) limits leaf (saved :: callers) p extra
  have cf := final_credits cfg active p rest ca
  have rv : resultValue active op p = result := by
    rw [resultValue_eq]
    rfl
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p) limits (base ++ [Value.i64 result]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,result] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p) limits base [.i64 result] (finalFrame leaf p result) saved callers post rfl rfl rfl cf ln
  have stackEq : (base ++ [Value.i64 result]).toArray = base.toArray.push (.i64 result) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel + 1) (.next (atCode (finalStore cfg active p) limits
      (base.toArray.push (.i64 (resultValue active op p))) (finalFrame leaf p (resultValue active op p)) (saved :: callers) [])) rest post := by
    simpa only [callAfter,active,rv,stackEq] using left
  have body := wp_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] p post ra ca bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 162) (241 * op + s.host.extCosts.cost "base" + rest) s limits base [.i32 p.interface,.i32 p.input]
    frame callers code 440 address p.mi WNear.Binary.StateDispatchLength.signature frame.inst WNear.Binary.StateDispatchLength.function post hr.code.prefixCode.module hi hf rfl d1
  have ac : activationGas op (wasmLocals WNear.Binary.StateDispatchLength.function [.i32 p.interface,.i32 p.input]) = 12 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateDispatchLength.function,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i32 p.interface,Value.i32 p.input] ++ #[Value.i32 0,Value.i64 0,Value.i64 0] =
      #[Value.i32 p.interface,Value.i32 p.input,Value.i32 0,Value.i64 0,Value.i64 0] := by apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel + 1) + 162) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDispatchLength.signature frame.inst
      WNear.Binary.StateDispatchLength.function [.i32 p.interface,.i32 p.input])) (241 * op + s.host.extCosts.cost "base" + rest) post := by
    have fee : active.host.extCosts = s.host.extCosts := by simp only [active,entered,chargedStore,chargeHost]
    simpa only [fee,op,wasmCallee,wasmLocals,WNear.Binary.StateDispatchLength.function,WNear.Binary.StateDispatchLength.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono b0) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (12 * op + (241 * op + (s.host.extCosts.cost "base" + rest))) = 254 * cfg.regularOpCost + (s.host.extCosts.cost "base" + rest) by dsimp [op]; omega] using proof
end WNear.Proofs.StateDispatchLength
