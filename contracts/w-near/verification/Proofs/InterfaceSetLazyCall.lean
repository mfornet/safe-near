import Proofs.InterfaceSetLazyBody
import Proofs.InterfaceSetCall

/-! Actual typed f463 call on the first-installation path. -/
namespace WNear.Proofs.InterfaceSetLazyCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceSetState WNear.Proofs.InterfaceSetLazyState
open WNear.Proofs.InterfaceSetCall (entered leaf)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def callAfter (s : Store NearState) (op : Nat) (p : Layout) (initializerAddress : Nat) :=
  InterfaceSetLazyState.finalStore (entered s op) op p initializerAddress

/-- Typed lazy normal463 invocation, including its opcode, activation and free return.
The lazy Setup conditions refer to the actual entered callee state. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (initializerAddress address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.funcAddrs[463]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function))
    (hr : Setup (entered s cfg.regularOpCost) limits (leaf frame.inst base.length p) ({frame with code} :: callers) p initializerAddress)
    (hb : Bounds p initializerAddress)
    (hc : s.host.gas.Credits (315 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p initializerAddress) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 221) (.next (atCode s limits
      (base ++ [Value.i32 p.interface, .i32 p.receiver, .i32 p.vtable]).toArray frame callers (.call 463 :: code)))
      (315 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee := leaf frame.inst base.length p
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (314 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (304 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cf := InterfaceSetLazyBody.finalStore_credits (entered s op) op rest p initializerAddress ha.2.2.2
  have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s op p initializerAddress) limits base []
    (InterfaceSetLazyState.finalFrame callee p initializerAddress) saved callers post rfl rfl rfl cf
  simp only [List.append_nil] at leaveRule
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p initializerAddress) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  have bodyRule := InterfaceSetLazyBody.wp_body cfg (fuel + 1) rest (entered s op) limits base callee (saved :: callers) [] p initializerAddress post hr hb ha.2.2.2
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (InterfaceSetLazyState.finalStore (entered s op) op p initializerAddress) limits base.toArray
      (InterfaceSetLazyState.finalFrame callee p initializerAddress) (saved :: callers) [])) rest post := leaving
  have bodyProof := bodyRule bodyNext
  have fe : fuel + 1 + 219 = fuel + 220 := by omega
  have body220 : WP cfg (fuel + 220) (.next (atCode (entered s op) limits base.toArray callee (saved :: callers)
      (WNear.Binary.InterfaceSet.body ++ []))) (304 * op + rest) post := by rw [← fe]; exact bodyProof
  have callRule := wp_call_wasm cfg (fuel + 220) (304 * op + rest) s limits base
    [.i32 p.interface, .i32 p.receiver, .i32 p.vtable] frame callers code 463 address p.mi
    WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function post hm hi hf rfl
    (by have h := hr.depth; simp only [List.length_cons] at h; omega)
  have hact : activationGas op (wasmLocals WNear.Binary.InterfaceSet.function
      [.i32 p.interface, .i32 p.receiver, .i32 p.vtable]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.InterfaceSet.function, activationGas, ValType.default]
  rw [hact] at callRule
  have callPaid := callRule (hc.mono (by dsimp [op]; omega))
  have calleeNext : WP cfg (fuel + 220) (.next (wasmCallee (entered s op) limits base frame callers code
      WNear.Binary.InterfaceSet.signature frame.inst WNear.Binary.InterfaceSet.function
      [.i32 p.interface, .i32 p.receiver, .i32 p.vtable])) (304 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.InterfaceSet.function, WNear.Binary.InterfaceSet.signature,
      callee, leaf, saved, atCode, ValType.default, List.map, List.append, Array.append_assoc, List.append_nil] using body220
  have result := callPaid calleeNext
  have fuelEq : fuel + 220 + 1 = fuel + 221 := by omega
  have gasEq : cfg.regularOpCost + (10 * op + (304 * op + rest)) = 315 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits
    (base ++ [Value.i32 p.interface, .i32 p.receiver, .i32 p.vtable]).toArray frame callers _ _ post fuelEq gasEq rfl result


end WNear.Proofs.InterfaceSetLazyCall
