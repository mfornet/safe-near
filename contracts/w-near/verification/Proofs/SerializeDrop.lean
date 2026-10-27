import Binary.SerializeHelpers
import Proofs.VectorDropPositiveCall

/-! f321 is the same vector-destructor descriptor as f68, reached by the
serializer's temporary formatted string. Its indexed call is proved explicitly. -/
namespace WNear.Proofs.SerializeDrop
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.VectorDrop WNear.Proofs.VectorDropPositive
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (q : DeallocateCore.Layout) (address68 address237 address582 : Nat) (post : Post)
    (hr : Resources s frame.inst p q address68 address237 address582)
    (address321 : Nat) (hi321 : p.mi.funcAddrs[321]? = some address321)
    (hf321 : s.funcs[address321]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68))
    (hd : callers.length + 8 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (319 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost q) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 230) (.next (atCode s limits (base ++ [Value.i32 p.vector]).toArray frame callers (.call 321 :: code)))
      (319 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[Value.i32 p.vector], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have r1 := hr.charge s frame.inst op p q address68 address237 address582
  have ready := r1.charge (chargedStore s op) frame.inst (9 * op) p q address68 address237 address582
  have ca := entered_credits s op (309 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := callAfter_credits s op rest q hc
  have leaving := wp_leave_wasm cfg fuel rest (callAfter s op q) limits base [] leaf saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op q) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving leaveNext
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (bodyAfter active op q) limits base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [callAfter, active, List.append_nil] using left
  have body := VectorDropPositive.wp_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p q address68 address237 address582 post ready rfl
    (by simpa only [List.length_cons] using hd) ca bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 228) (309 * op + rest) s limits base [.i32 p.vector] frame callers code 321 address321 p.mi
    WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68 post hr.vector.module hi321 hf321 rfl (by omega)
  have activation : activationGas op (wasmLocals WNear.Binary.VectorDrop.function68 [.i32 p.vector]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function68]
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 228) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68 [.i32 p.vector])) (309 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function68, WNear.Binary.VectorDrop.signature,
      leaf, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_nil] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (309 * op + rest)) = 319 * cfg.regularOpCost + rest by dsimp [op]; omega] using result


end WNear.Proofs.SerializeDrop
