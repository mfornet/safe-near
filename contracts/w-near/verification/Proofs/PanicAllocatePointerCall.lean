import Proofs.PanicAllocatePointerBody

/-! Typed zero-size f503 invocation, returning its actual pointerone. -/
namespace WNear.Proofs.PanicAllocatePointerCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.PanicAllocatePointerState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP PanicAllocateZero.calledStore

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def leaf (inst height : Nat) : CallFrame :=
  {locals := #[.i32 0, .i32 1, .i32 0, .i32 0]
   inst
   arity := 1
   height
   labels := []
   code := []}
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p

/-- Actual503 call, nested508/509, nonzero guard and typed pointer return. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.funcAddrs[503]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.PanicAllocate.signature503 frame.inst WNear.Binary.PanicAllocate.function503))
    (hr : Ready (entered s cfg.regularOpCost) limits (leaf frame.inst base.length) ({frame with code} :: callers) p)
    (hc : s.host.gas.Credits (86 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits
      (base ++ [Value.i32 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 63) (.next (atCode s limits (base ++ [Value.i32 0, .i32 1]).toArray frame callers (.call 503 :: code)))
      (86 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee := leaf frame.inst base.length
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (85 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (75 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cf := after_credits (entered s op) op rest p ha.2.2.2
  have leaveRule := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [Value.i32 1]
    (finalFrame callee p) saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits
      (base ++ [Value.i32 1]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  have stackEq : (base ++ [Value.i32 1]).toArray = base.toArray.push (.i32 1) := by
    apply Array.toList_inj.mp; simp
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after (entered s op) op p) limits
      (base.toArray.push (.i32 1)) (finalFrame callee p) (saved :: callers) [])) rest post := by
    simpa only [stackEq, callAfter] using leaving
  have bodyProof := PanicAllocatePointerBody.wp_body cfg (fuel + 1) rest (entered s op) limits base callee (saved :: callers) [] p post hr ha.2.2.2 bodyNext
  have body62 : WP cfg (fuel + 62) (.next (atCode (entered s op) limits base.toArray callee (saved :: callers)
      (WNear.Binary.PanicAllocate.body503 ++ []))) (75 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using bodyProof
  have callRule := wp_call_wasm cfg (fuel + 62) (75 * op + rest) s limits base [.i32 0, .i32 1]
    frame callers code 503 address p.mi WNear.Binary.PanicAllocate.signature503 frame.inst WNear.Binary.PanicAllocate.function503 post hm hi hf rfl
    (by have h := hr.depth; simp only [List.length_cons] at h; omega)
  have hact : activationGas op (wasmLocals WNear.Binary.PanicAllocate.function503 [.i32 0, .i32 1]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.PanicAllocate.function503, activationGas, ValType.default]
  rw [hact] at callRule
  have callPaid := callRule (hc.mono (by dsimp [op]; omega))
  have calleeNext : WP cfg (fuel + 62) (.next (wasmCallee (entered s op) limits base frame callers code
      WNear.Binary.PanicAllocate.signature503 frame.inst WNear.Binary.PanicAllocate.function503 [.i32 0, .i32 1])) (75 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.PanicAllocate.function503, WNear.Binary.PanicAllocate.signature503,
      callee, leaf, saved, atCode, ValType.default] using body62
  have result := callPaid calleeNext
  have fe : fuel + 62 + 1 = fuel + 63 := by omega
  have ge : cfg.regularOpCost + (10 * op + (75 * op + rest)) = 86 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits (base ++ [Value.i32 0, .i32 1]).toArray frame callers _ _ post fe ge rfl result

end WNear.Proofs.PanicAllocatePointerCall
