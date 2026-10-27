import Proofs.InterfaceSetInitializedPrefix
import Proofs.InterfaceSetReady
import Proofs.InterfaceSetTail

/-! Full actual initialized f463 setter body and its typed direct-call adapter. -/
namespace WNear.Proofs.InterfaceSetCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState WNear.Proofs.InterfaceSetPhases
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP

/-- The complete actual155-step initialized setter body. All linked callee
executions are proved; Ready contains only code, native bounds and memory data. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p)
    (hc : s.host.gas.Credits (222 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost p) limits base.toArray
      (InterfaceSetPhases.finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 155) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.body ++ code))) (222 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let gf := guardedFrame frame p
  have hsize := hr.localSize
  have hs : gf.locals[3]? = some (.i32 (scratch p)) := by
    simp [gf, guardedFrame, reservedFrame, show 3 < frame.locals.size by omega]
  have hreceiver : gf.locals[1]? = some (.i32 p.receiver) := by simpa [gf, guardedFrame, reservedFrame] using hr.receiverLocal
  have hvtable : gf.locals[2]? = some (.i32 p.vtable) := by simpa [gf, guardedFrame, reservedFrame] using hr.vtableLocal
  have hsizeG : 4 ≤ gf.locals.size := by simpa only [gf, guardedFrame, reservedFrame, Array.size_set!] using hsize
  have cA : Code (acquired s op p) p gf.inst := by
    simpa only [gf, guardedFrame, reservedFrame] using acquired_code s op p frame.inst hr.code
  have cI : Code (installed s op p) p gf.inst := by
    simpa only [gf, guardedFrame, reservedFrame] using installed_code s op p frame.inst hr.code
  have ca : (acquired s op p).host.gas.Credits (101 * op + rest) :=
    acquired_credits s op _ p (hc.mono (by dsimp [op]; omega))
  have nextTail : WP cfg fuel (.next (atCode
      (InterfaceSetTail.after (acquired s op p) op p (counter p) (acquiredMemory p) (highMemory p) (lowMemory p) (installedMemory p))
      limits base.toArray (InterfaceSetTail.finalFrame gf p (highMemory p)) callers code)) rest post := by
    simpa only [InterfaceSetTail.after, InterfaceSetTail.installed, InterfaceSetReleaseTail.after,
      InterfaceSetReleaseTail.epilogueAfter, InterfaceSetReleaseTail.released,
      InterfaceSetTail.finalFrame, InterfaceSetTail.pointerFrame, InterfaceSetReleaseTail.finalFrame,
      InterfaceSetPhases.finalStore, branched, released, installed, InterfaceSetPhases.finalFrame,
      InterfaceSetPhases.pointerFrame, gf, op] using hnext
  have tailRule := InterfaceSetTail.wp_tail cfg fuel rest (acquired s op p) limits base gf callers code p
    (counter p) (acquiredMemory p) (highMemory p) (lowMemory p) (installedMemory p)
    {p.global with value := .i32 (scratch p)} post hs hreceiver hvtable hsizeG cA
    (acquired_memory s op p hr.memory) (high_memory s op p hr.memory) (low_memory s op p hr.memory)
    hr.highReadBound hr.highWriteBound hr.lowReadBound hr.lowWriteBound hr.lowMemoryWf hr.pointerBound hr.existingEmpty
    cI (installed_global s op p hr.global) rfl (installed_memory s op p hr.memory) rfl
    hr.releaseRecordBound hr.releaseCounterBound (by have h := hr.depth; omega) ca nextTail
  have tailNext : WP cfg (fuel + 70) (.next (atCode (acquired s op p) limits base.toArray
      (nested (guardedFrame frame p) base.toArray.size code) callers InterfaceSetInitializedPrefix.tail)) (101 * op + rest) post := by
    simpa only [gf, InterfaceSetInitializedPrefix.tail] using tailRule
  have headProof := InterfaceSetInitializedPrefix.wp_prefix cfg (fuel + 70) (101 * op + rest) s limits base frame callers code p post hr
    (savedArguments_memory s op p hr.memory) (arguments_memory s op p hr.memory) (arguments_global s op p hr.global)
    (hc.mono (by dsimp [op]; omega)) tailNext
  have fe : fuel + 70 + 85 = fuel + 155 := by omega
  have ge : 121 * cfg.regularOpCost + (101 * op + rest) = 222 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge rfl headProof

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)

def leaf (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.interface, .i32 p.receiver, .i32 p.vtable, .i32 0]
   inst
   arity := 0
   height
   labels := []
   code := []}

def callAfter (s : Store NearState) (op : Nat) (p : Layout) := finalStore (entered s op) op p

/-- Typed normal463 invocation, including its opcode, activation and free return.
The initialized Ready conditions refer to the actual entered callee state. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.funcAddrs[463]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function))
    (hr : Ready (entered s cfg.regularOpCost) limits (leaf frame.inst base.length p) ({frame with code} :: callers) p)
    (hc : s.host.gas.Credits (233 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 157) (.next (atCode s limits
      (base ++ [Value.i32 p.interface, .i32 p.receiver, .i32 p.vtable]).toArray frame callers (.call 463 :: code)))
      (233 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee := leaf frame.inst base.length p
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (232 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (222 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cf := finalStore_credits (entered s op) op rest p ha.2.2.2
  have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base []
    (InterfaceSetPhases.finalFrame callee p) saved callers post rfl rfl rfl cf
  simp only [List.append_nil] at leaveRule
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  have bodyRule := wp_body cfg (fuel + 1) rest (entered s op) limits base callee (saved :: callers) [] p post hr ha.2.2.2
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (finalStore (entered s op) op p) limits base.toArray
      (InterfaceSetPhases.finalFrame callee p) (saved :: callers) [])) rest post := leaving
  have bodyProof := bodyRule bodyNext
  have fe : fuel + 1 + 155 = fuel + 156 := by omega
  have body156 : WP cfg (fuel + 156) (.next (atCode (entered s op) limits base.toArray callee (saved :: callers)
      (WNear.Binary.InterfaceSet.body ++ []))) (222 * op + rest) post := by rw [← fe]; exact bodyProof
  have callRule := wp_call_wasm cfg (fuel + 156) (222 * op + rest) s limits base
    [.i32 p.interface, .i32 p.receiver, .i32 p.vtable] frame callers code 463 address p.mi
    WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function post hm hi hf rfl
    (by have h := hr.depth; simp only [List.length_cons] at h; omega)
  have hact : activationGas op (wasmLocals WNear.Binary.InterfaceSet.function
      [.i32 p.interface, .i32 p.receiver, .i32 p.vtable]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.InterfaceSet.function, activationGas, ValType.default]
  rw [hact] at callRule
  have callPaid := callRule (hc.mono (by dsimp [op]; omega))
  have calleeNext : WP cfg (fuel + 156) (.next (wasmCallee (entered s op) limits base frame callers code
      WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function
      [.i32 p.interface, .i32 p.receiver, .i32 p.vtable])) (222 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.InterfaceSet.function, WNear.Binary.InterfaceSet.signature,
      callee, leaf, saved, atCode, ValType.default, List.map, List.append, Array.append_assoc, List.append_nil] using body156
  have result := callPaid calleeNext
  have fuelEq : fuel + 156 + 1 = fuel + 157 := by omega
  have gasEq : cfg.regularOpCost + (10 * op + (222 * op + rest)) = 233 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits
    (base ++ [Value.i32 p.interface, .i32 p.receiver, .i32 p.vtable]).toArray frame callers _ _ post fuelEq gasEq rfl result

end WNear.Proofs.InterfaceSetCall
