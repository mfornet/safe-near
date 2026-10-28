import Proofs.DeallocateInsertBody
import Proofs.DeallocateInsertResources
import Proofs.DeallocateInsertGas
import NearVM.MeteredWasmCall

/-! Actual typed f582 activation from original native heap conditions. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
set_option maxRecDepth 16384
attribute [local irreducible] WP

def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment, .i32 0, .i32 0, .i32 0],
    inst, arity := 0, height, labels := [], code := []}

/-- The interpreter's actual typed locals satisfy the body contract after its
call and activation charges; functional memory and code remain original. -/
theorem ready_entered (s : Store NearState) (inst height op : Nat) (p : Layout)
    (hcode : Code s inst p) (hmem : s.mems[p.memoryIndex]? = some p.memory) (hn : Native p) :
    Ready (entered s op) (leafFrame inst height p) p := by
  constructor
  · exact hcode.transport s (entered s op) inst p rfl rfl
  · exact hmem
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [leafFrame]
  · exact hn


/-- Actual typed call to f582, including activation, its full113-step body,
and the free normal return to the original caller. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hcode : Code s frame.inst p) (hmem : s.mems[p.memoryIndex]? = some p.memory) (hn : Native p)
    (hi : p.mi.funcAddrs[582]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.Deallocate.coreSignature frame.inst WNear.Binary.Deallocate.coreFunction))
    (hd : callers.length + 3 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (142 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 115) (.next (atCode s limits (base ++ [Value.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment]).toArray
      frame callers (.call 582 :: code))) (142 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (129 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := callAfter_credits s op rest p hc
  have hr := ready_entered s frame.inst base.length op p hcode hmem hn
  have leaving := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [] (finalFrame leaf p) saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving leaveNext
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after active op p) limits base.toArray (finalFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [callAfter, active, List.append_nil] using left
  have body := wp_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p post hr
    (by simpa only [List.length_cons] using hd) ca bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 113) (129 * op + rest) s limits base [.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment] frame callers code 582 address p.mi
    WNear.Binary.Deallocate.coreSignature frame.inst WNear.Binary.Deallocate.coreFunction post hcode.module hi hf rfl (by omega)
  have activation : activationGas op (wasmLocals WNear.Binary.Deallocate.coreFunction [.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment]) = 12 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.Deallocate.coreFunction, ValType.default]
  rw [activation] at callRule
  have arrays : #[Value.i32 p.allocator, Value.i32 p.pointer, Value.i32 p.length, Value.i32 p.alignment] ++ #[Value.i32 0, Value.i32 0, Value.i32 0] =
      #[Value.i32 p.allocator, Value.i32 p.pointer, Value.i32 p.length, Value.i32 p.alignment, Value.i32 0, Value.i32 0, Value.i32 0] := by
    apply Array.toList_inj.mp
    simp
  have next : WP cfg ((fuel + 1) + 113) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.Deallocate.coreSignature frame.inst WNear.Binary.Deallocate.coreFunction [.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment])) (129 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.Deallocate.coreFunction, WNear.Binary.Deallocate.coreSignature,
      leaf, leafFrame, saved, atCode, List.map_cons, List.map_nil, ValType.default, List.append_nil, List.length_nil, arrays] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (12 * op + (129 * op + rest)) = 142 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.DeallocateInsert
