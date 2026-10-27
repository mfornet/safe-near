import Proofs.VectorDropPositive237Credits
import Proofs.DeallocateCoreCall

/-! Full actual f237 forwarder, with the concrete previous-free f582 path. -/
namespace WNear.Proofs.VectorDropPositive237
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- Fixed allocator arguments followed by the full concrete allocator call. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : DeallocateCore.Layout) (address582 : Nat) (post : Post)
    (hr : Ready s frame.inst p address582)
    (hp : frame.locals[0]? = some (.i32 p.pointer)) (hl : frame.locals[1]? = some (.i32 p.length))
    (ha : frame.locals[2]? = some (.i32 p.alignment)) (hd : callers.length + 3 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (235 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 194) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Deallocate.entryBody ++ code)))
      (235 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have ready := hr.paid s frame.inst op 4 p address582
  have call := DeallocateCore.wp_call cfg fuel rest (paid s op 4) limits base frame callers code p address582 post ready.code ready.memory ready.native
    ready.index582 ready.function582 hd (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) hnext
  have array : (base ++ [Value.i32 p.allocator, .i32 p.pointer, .i32 p.length, .i32 p.alignment]).toArray =
      (((base.toArray.push (.i32 1074896)).push (.i32 p.pointer)).push (.i32 p.length)).push (.i32 p.alignment) := by
    apply Array.toList_inj.mp
    simp [hr.allocator]
  have callNext : WP cfg (fuel + 190) (.next (atCode (paid s op 4) limits
      ((((base.toArray.push (.i32 1074896)).push (.i32 p.pointer)).push (.i32 p.length)).push (.i32 p.alignment)) frame callers (.call 582 :: code))) (231 * op + rest) post := by
    simpa only [array, op] using call
  have args := wp_arguments cfg (fuel + 190) (231 * op + rest) s limits base.toArray frame callers code p.pointer p.length p.alignment post hp hl ha
    (hc.mono (by dsimp [op]; omega)) callNext
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (231 * op + rest) = 235 * cfg.regularOpCost + rest by dsimp [op]; omega] using args

/-- Full actual typed f237 local call; all allocator branches are derived from
its original native heap record, with no successful invocation premise. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : DeallocateCore.Layout) (address237 address582 : Nat) (post : Post)
    (hr : Ready s frame.inst p address582)
    (hi : p.mi.funcAddrs[237]? = some address237)
    (hf : s.funcs[address237]? = some (.wasm WNear.Binary.Deallocate.entrySignature frame.inst WNear.Binary.Deallocate.entryFunction))
    (hd : callers.length + 4 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (246 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 196) (.next (atCode s limits (base ++ [Value.i32 p.pointer, .i32 p.length, .i32 p.alignment]).toArray frame callers (.call 237 :: code)))
      (246 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[Value.i32 p.pointer, .i32 p.length, .i32 p.alignment], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have r1 := hr.charge s frame.inst op p address582
  have ready := r1.charge (chargedStore s op) frame.inst (10 * op) p address582
  have ca := entered_credits s op (235 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := callAfter_credits s op rest p hc
  have leaving := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [] leaf saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving leaveNext
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after active op p) limits base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [callAfter, active, List.append_nil] using left
  have body := wp_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p address582 post ready rfl rfl rfl
    (by simpa only [List.length_cons] using hd) ca bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 194) (235 * op + rest) s limits base [.i32 p.pointer, .i32 p.length, .i32 p.alignment] frame callers code 237 address237 p.mi
    WNear.Binary.Deallocate.entrySignature frame.inst WNear.Binary.Deallocate.entryFunction post hr.code.module hi hf rfl (by omega)
  have activation : activationGas op (wasmLocals WNear.Binary.Deallocate.entryFunction [.i32 p.pointer, .i32 p.length, .i32 p.alignment]) = 10 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.Deallocate.entryFunction]
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 194) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.Deallocate.entrySignature frame.inst WNear.Binary.Deallocate.entryFunction [.i32 p.pointer, .i32 p.length, .i32 p.alignment])) (235 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.Deallocate.entryFunction, WNear.Binary.Deallocate.entrySignature,
      leaf, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_nil] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (235 * op + rest)) = 246 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.VectorDropPositive237
