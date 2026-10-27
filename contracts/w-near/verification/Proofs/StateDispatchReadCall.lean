import Proofs.StateDispatchReadBody
import NearVM.MeteredWasmCall

/-! Actual typed f435 read-register dispatcher from original resources. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode acquired checked arguments returned finalStore
set_option maxRecDepth 16384

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.interface,.i32 p.inputRegister,.i32 p.inputPointer,.i32 0,.i32 0],inst,arity := 0,height,labels := [],code := []}
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def callAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) := finalStore cfg (entered s cfg.regularOpCost) p bytes

theorem Ready.charge (s : Store NearState) (amount : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (bytes : List UInt8) (extra : Nat) (hr : Ready s limits frame callers p bytes extra) :
    Ready (chargedStore s amount) limits frame callers p bytes extra := by
  have pc := hr.prefixReady
  have newPrefix : StateDispatchPrefix.Ready (chargedStore s amount) limits frame callers p.toLayout 3 := {
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
  exact ⟨hr.code.transport s (chargedStore s amount) p frame.inst extra rfl rfl rfl,newPrefix,hr.registerLocal,hr.pointerLocal,hr.localSize,
    hr.highBound,hr.lowBound,hr.selectBound,hr.selectedNonzero,hr.cellBound,hr.registerBound,hr.pointerBound,hr.vtableBound,
    hr.registerValue,hr.payloadBound,hr.releaseBound,hr.counterBound⟩

private theorem tail_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (93 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest)) :
    (StateDispatchReadTail.after cfg s p bytes).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have b0 : 9 * op + (84 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 93 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have b1 : 15 * op + RegisterRead.readCost s.host bytes.length + (69 * op + rest) ≤ 84 * op + RegisterRead.readCost s.host bytes.length + rest := by omega
  have b2 : 42 * op + (27 * op + rest) ≤ 69 * op + rest := by omega
  let a := StateDispatchReadTail.arguments s op
  have ca := paid_credits s op 9 (84 * op + RegisterRead.readCost s.host bytes.length + rest) (hc.mono b0)
  have fee : RegisterRead.readCost a.host bytes.length = RegisterRead.readCost s.host bytes.length := by
    simp only [a,StateDispatchReadTail.arguments,RegisterRead.readCost,paid,chargedStore,chargeHost]
  have hostCredits : a.host.gas.Credits (15 * cfg.regularOpCost + RegisterRead.readCost a.host bytes.length + (69 * op + rest)) := by rw [fee]; exact ca.mono b1
  have ch := StateDispatchReadGas.host_credits cfg a p.mi (ptr p) bytes (69 * op + rest) hostCredits
  have cc := StateDispatchReadGas.cleanup_credits (StateDispatchReadTail.returned cfg s p bytes) op p.memoryIndex (27 * op + rest)
    (counter p bytes) (readMemory p bytes) (ch.mono b2)
  exact StateDispatchReadGas.finish_credits (StateDispatchReadTail.cleaned cfg s p bytes) op p.globalIndex rest (scratch p) cc

theorem final_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest)) :
    (finalStore cfg s p bytes).host.gas.Credits rest := by
  unfold finalStore
  exact tail_credits cfg (checked s cfg.regularOpCost p) p bytes rest (checked_credits cfg s p bytes rest hc)

/-- Complete actual f435 call, including its eleven-unit activation and
sequential payload copy followed by the real counter release. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (bytes : List UInt8) (address : Nat) (post : Post)
    (hr : Ready s limits (leafFrame frame.inst base.length p) ({frame with code} :: callers) p bytes extra)
    (hi : p.mi.funcAddrs[435]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatchRead.signature frame.inst WNear.Binary.StateDispatchRead.function))
    (hc : s.host.gas.Credits (249 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter cfg s p bytes) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 161) (.next (atCode s limits (base ++ [Value.i32 p.interface,.i32 p.inputRegister,.i32 p.inputPointer]).toArray frame callers (.call 435 :: code)))
      (249 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have b0 : op + (11 * op + (237 * op + RegisterRead.readCost s.host bytes.length + rest)) ≤ 249 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; simp only [List.length_cons] at *; omega
  have c0 := (GasCounter.burn_credits s.host.gas op (11 * op + (237 * op + RegisterRead.readCost s.host bytes.length + rest)) (hc.mono b0)).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (237 * op + RegisterRead.readCost s.host bytes.length + rest) c0).2.2.2
  have fee : RegisterRead.readCost active.host bytes.length = RegisterRead.readCost s.host bytes.length := by
    simp only [active,entered,RegisterRead.readCost,chargedStore,chargeHost]
  have ca : active.host.gas.Credits (237 * cfg.regularOpCost + RegisterRead.readCost active.host bytes.length + rest) := by rw [fee]; exact c1
  have ra := (hr.charge s op limits leaf (saved :: callers) p bytes extra).charge (chargedStore s op) (11 * op) limits leaf (saved :: callers) p bytes extra
  have cf := final_credits cfg active p bytes rest ca
  have ln : WP cfg fuel (.next (atCode (callAfter cfg s p bytes) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter cfg s p bytes) limits base [] (finalFrame leaf p) saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel + 1) (.next (atCode (finalStore cfg active p bytes) limits base.toArray (finalFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [callAfter,active,List.append_nil] using left
  have body := wp_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] p bytes post ra ca bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 159) (237 * op + RegisterRead.readCost s.host bytes.length + rest) s limits base [.i32 p.interface,.i32 p.inputRegister,.i32 p.inputPointer]
    frame callers code 435 address p.mi WNear.Binary.StateDispatchRead.signature frame.inst WNear.Binary.StateDispatchRead.function post hr.code.prefixCode.module hi hf rfl d1
  have ac : activationGas op (wasmLocals WNear.Binary.StateDispatchRead.function [.i32 p.interface,.i32 p.inputRegister,.i32 p.inputPointer]) = 11 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateDispatchRead.function,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i32 p.interface,Value.i32 p.inputRegister,Value.i32 p.inputPointer] ++ #[Value.i32 0,Value.i32 0] =
      #[Value.i32 p.interface,Value.i32 p.inputRegister,Value.i32 p.inputPointer,Value.i32 0,Value.i32 0] := by apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel + 1) + 159) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDispatchRead.signature frame.inst
      WNear.Binary.StateDispatchRead.function [.i32 p.interface,.i32 p.inputRegister,.i32 p.inputPointer])) (237 * op + RegisterRead.readCost s.host bytes.length + rest) post := by
    simpa only [fee,op,wasmCallee,wasmLocals,WNear.Binary.StateDispatchRead.function,WNear.Binary.StateDispatchRead.signature,
      leaf,leafFrame,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,ValType.default,arrays] using body
  have proof := cr (hc.mono b0) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (11 * op + (237 * op + (RegisterRead.readCost s.host bytes.length + rest))) = 249 * cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + rest) by dsimp [op]; omega] using proof
end WNear.Proofs.StateDispatchRead
