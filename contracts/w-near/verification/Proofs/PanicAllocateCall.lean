import Proofs.PanicAllocateBody
import Proofs.PanicAllocateFrame

/-! Actual typed zero-size508 invocation. -/
namespace WNear.Proofs.PanicAllocateCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.PanicAllocateState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP PanicAllocateZero.calledStore

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def leaf (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.out, .i32 0, .i32 p.alignment, .i32 0]
   inst
   arity := 0
   height
   labels := []
   code := []}
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p

/-- Typed zero-size508 invocation, including its opcode, activation and free return.
The zero-size Ready conditions refer to the actual entered callee state. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.funcAddrs[508]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.PanicAllocate.signature508 frame.inst WNear.Binary.PanicAllocate.function508))
    (hr : Ready (entered s cfg.regularOpCost) limits (leaf frame.inst base.length p) ({frame with code} :: callers) p)
    (hc : s.host.gas.Credits (56 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 41) (.next (atCode s limits
      (base ++ [Value.i32 p.out, .i32 0, .i32 p.alignment]).toArray frame callers (.call 508 :: code)))
      (56 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee := leaf frame.inst base.length p
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (55 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (45 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cf := after_credits (entered s op) op rest p ha.2.2.2
  have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base []
    (afterFrame callee p) saved callers post rfl rfl rfl cf
  simp only [List.append_nil] at leaveRule
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  have bodyRule := PanicAllocateBody.wp_body cfg (fuel + 1) rest (entered s op) limits base callee (saved :: callers) [] p post hr ha.2.2.2
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after (entered s op) op p) limits base.toArray
      (afterFrame callee p) (saved :: callers) [])) rest post := leaving
  have bodyProof := bodyRule bodyNext
  have fe : fuel + 1 + 39 = fuel + 40 := by omega
  have body40 : WP cfg (fuel + 40) (.next (atCode (entered s op) limits base.toArray callee (saved :: callers)
      (WNear.Binary.PanicAllocate.body508 ++ []))) (45 * op + rest) post := by rw [← fe]; exact bodyProof
  have callRule := wp_call_wasm cfg (fuel + 40) (45 * op + rest) s limits base
    [.i32 p.out, .i32 0, .i32 p.alignment] frame callers code 508 address p.mi
    WNear.Binary.PanicAllocate.signature508 frame.inst WNear.Binary.PanicAllocate.function508 post hm hi hf rfl
    (by have h := hr.depth; simp only [List.length_cons] at h; omega)
  have hact : activationGas op (wasmLocals WNear.Binary.PanicAllocate.function508
      [.i32 p.out, .i32 0, .i32 p.alignment]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.PanicAllocate.function508, activationGas, ValType.default]
  rw [hact] at callRule
  have callPaid := callRule (hc.mono (by dsimp [op]; omega))
  have calleeNext : WP cfg (fuel + 40) (.next (wasmCallee (entered s op) limits base frame callers code
      WNear.Binary.PanicAllocate.signature508 frame.inst WNear.Binary.PanicAllocate.function508
      [.i32 p.out, .i32 0, .i32 p.alignment])) (45 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.PanicAllocate.function508, WNear.Binary.PanicAllocate.signature508,
      callee, leaf, saved, atCode, ValType.default, List.map, List.append, Array.append_assoc, List.append_nil] using body40
  have result := callPaid calleeNext
  have fuelEq : fuel + 40 + 1 = fuel + 41 := by omega
  have gasEq : cfg.regularOpCost + (10 * op + (45 * op + rest)) = 56 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits
    (base ++ [Value.i32 p.out, .i32 0, .i32 p.alignment]).toArray frame callers _ _ post fuelEq gasEq rfl result


end WNear.Proofs.PanicAllocateCall
