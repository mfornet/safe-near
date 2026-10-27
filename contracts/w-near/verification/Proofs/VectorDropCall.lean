import Proofs.VectorDropEmpty
import Proofs.TotalSupply

/-! The deployed f68 empty-vector path, with both actual nested calls. -/
namespace WNear.Proofs.VectorDrop
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

structure EmptyReady (s : Store NearState) (inst : Nat) (vector : UInt32) where
  mi : ModuleInst
  index : Nat
  memory : Memory
  emptyAddress : Nat
  vectorAddress : Nat
  module : s.modules[inst]? = some mi
  memoryIndex : mi.memAddrs[0]? = some index
  memoryLookup : s.mems[index]? = some memory
  emptyIndex : mi.funcAddrs[778]? = some emptyAddress
  emptyFunction : s.funcs[emptyAddress]? = some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function778)
  vectorIndex : mi.funcAddrs[747]? = some vectorAddress
  vectorFunction : s.funcs[vectorAddress]? = some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function747)
  bound : vector.toNat + 8 ≤ memory.byteSize
  capacityZero : readI32 memory (vector.toNat + 4) = 0

def emptyBeforeVector (s : Store NearState) (op : Nat) := paid (entered (paid s op 1) op) op 1
def emptyBodyAfter (s : Store NearState) (op : Nat) := zeroAfter (emptyBeforeVector s op) op

theorem emptyBodyAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (27 * op + rest)) : (emptyBodyAfter s op).host.gas.Credits rest := by
  have c1 := paid_credits s op 1 (26 * op + rest) (hc.mono (by omega))
  have c2 := entered_credits (paid s op 1) op (16 * op + rest) (c1.mono (by omega))
  have c3 := paid_credits (entered (paid s op 1) op) op 1 (15 * op + rest) (c2.mono (by omega))
  exact zeroAfter_credits (emptyBeforeVector s op) op rest c3

/-- Both deployed f68 calls are resolved structurally; the zero-capacity header
causes the real vector guard to skip the allocator. -/
theorem wp_empty_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (r : EmptyReady s frame.inst vector) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (emptyBodyAfter s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits base.toArray frame callers (WNear.Binary.VectorDrop.body68 ++ code)))
      (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let first := paid s op 1
  let middle := entered first op
  let last := emptyBeforeVector s op
  have array : (base ++ [Value.i32 vector]).toArray = base.toArray.push (.i32 vector) := by
    apply Array.toList_inj.mp
    simp
  have c1 := paid_credits s op 1 (26 * op + rest) (hc.mono (by dsimp [op]; omega))
  have c2 := entered_credits first op (16 * op + rest) (c1.mono (by omega))
  have c3 := paid_credits middle op 1 (15 * op + rest) (c2.mono (by omega))
  have hm3 : last.modules[frame.inst]? = some r.mi := by simpa only [last, emptyBeforeVector, paid, entered, chargedStore] using r.module
  have hmem3 : last.mems[r.index]? = some r.memory := by simpa only [last, emptyBeforeVector, paid, entered, chargedStore] using r.memoryLookup
  have hf3 : last.funcs[r.vectorAddress]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747) := by
    simpa only [last, emptyBeforeVector, paid, entered, chargedStore] using r.vectorFunction
  have vectorCall := wp_call_zero cfg fuel rest last limits base frame callers code vector r.mi r.index r.vectorAddress r.memory post
    hm3 r.memoryIndex hmem3 r.vectorIndex hf3 r.bound r.capacityZero hd c3 hnext
  have vectorNext : WP cfg (fuel + 8) (.next (atCode (chargedStore middle cfg.regularOpCost) limits (base.toArray.push (.i32 vector)) frame callers (.call 747 :: code)))
      (15 * op + rest) post := by simpa only [last, emptyBeforeVector, first, middle, paid, array] using vectorCall
  have get2 := wp_local_get cfg (fuel + 8) (15 * op + rest) middle limits base.toArray frame callers (.call 747 :: code) 0 (.i32 vector) post hv (c2.mono (by dsimp [op]; omega)) vectorNext
  have hm1 : first.modules[frame.inst]? = some r.mi := by simpa only [first, paid, chargedStore] using r.module
  have hf1 : first.funcs[r.emptyAddress]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function778) := by
    simpa only [first, paid, chargedStore] using r.emptyFunction
  have emptyNext : WP cfg (fuel + 9) (.next (atCode (entered first op) limits base.toArray frame callers (.local_get 0 :: .call 747 :: code))) (16 * op + rest) post := by
    rw [show cfg.regularOpCost + (15 * op + rest) = 16 * op + rest by dsimp [op]; omega] at get2
    exact get2
  have emptyCall := wp_call_empty cfg (fuel + 9) (16 * op + rest) first limits base frame callers
    (.local_get 0 :: .call 747 :: code) vector r.mi r.emptyAddress post hm1 r.emptyIndex hf1 hd (c1.mono (by omega)) emptyNext
  have emptyGetNext : WP cfg (fuel + 11) (.next (atCode (chargedStore s cfg.regularOpCost) limits (base.toArray.push (.i32 vector)) frame callers
      (.call 778 :: .local_get 0 :: .call 747 :: code))) (26 * op + rest) post := by
    rw [show 10 * cfg.regularOpCost + (16 * op + rest) = 26 * op + rest by dsimp [op]; omega] at emptyCall
    simpa only [first, paid, array, Nat.add_assoc, Nat.reduceAdd] using emptyCall
  have get1 := wp_local_get cfg (fuel + 11) (26 * op + rest) s limits base.toArray frame callers
    (.call 778 :: .local_get 0 :: .call 747 :: code) 0 (.i32 vector) post hv (hc.mono (by dsimp [op]; omega)) emptyGetNext
  simpa only [WNear.Binary.VectorDrop.body68, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (26 * op + rest) = 27 * cfg.regularOpCost + rest by dsimp [op]; omega] using get1



def emptyCallAfter (s : Store NearState) (op : Nat) := emptyBodyAfter (entered s op) op

theorem emptyCallAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (37 * op + rest)) : (emptyCallAfter s op).host.gas.Credits rest := by
  exact emptyBodyAfter_credits (entered s op) op rest (entered_credits s op (27 * op + rest) (hc.mono (by omega)))

/-- Actual f68 local call on an empty vector; the caller's complete stack,
frame and continuation are recovered after both nested destructor calls. -/
theorem wp_call_empty_vector (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (r : EmptyReady s frame.inst vector) (address : Nat) (post : Post)
    (hfi : r.mi.funcAddrs[68]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68))
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (37 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (emptyCallAfter s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 14) (.next (atCode s limits (base ++ [Value.i32 vector]).toArray frame callers (.call 68 :: code)))
      (37 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let callee : CallFrame := {locals := #[Value.i32 vector], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have ready : EmptyReady active callee.inst vector :=
    {r with
      module := by simpa only [active, entered, chargedStore, callee] using r.module
      memoryLookup := by simpa only [active, entered, chargedStore] using r.memoryLookup
      emptyFunction := by simpa only [active, entered, chargedStore, callee] using r.emptyFunction
      vectorFunction := by simpa only [active, entered, chargedStore, callee] using r.vectorFunction}
  have ca := entered_credits s op (27 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := emptyCallAfter_credits s op rest hc
  have leaving := wp_leave_wasm cfg fuel rest (emptyCallAfter s op) limits base [] callee saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (emptyCallAfter s op) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving leaveNext
  have body := wp_empty_body cfg (fuel + 1) rest active limits base callee (saved :: callers) [] vector ready post rfl (by simpa only [List.length_cons] using hd) ca
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (emptyBodyAfter active op) limits base.toArray callee (saved :: callers) [])) rest post := by
    simpa only [emptyCallAfter, active, List.append_nil] using left
  have doneBody := body bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 12) (27 * op + rest) s limits base [.i32 vector] frame callers code 68 address r.mi
    WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68 post r.module hfi hf rfl (by omega)
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function68 [.i32 vector]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function68]
  rw [ha] at callRule
  have callNext : WP cfg ((fuel + 1) + 12) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68 [.i32 vector])) (27 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function68, WNear.Binary.VectorDrop.signature,
      callee, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_nil] using doneBody
  have result := callRule (hc.mono (by dsimp [op]; omega)) callNext
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (27 * op + rest)) = 37 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

/-- The empty-capacity specialization discharges the actual getter call site.
The nonempty specialization is not claimed here. -/
theorem empty_calleeContract (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (vector : UInt32) (r : EmptyReady s frame.inst vector) (address : Nat)
    (hi : r.mi.funcAddrs[68]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function68))
    (hd : 2 < limits.maxCallDepth) :
    TotalSupply.CalleeContract cfg limits frame 68 [.i32 vector] s (emptyCallAfter s cfg.regularOpCost) (37 * cfg.regularOpCost) 14 := by
  constructor
  · intro rest hc
    exact emptyCallAfter_credits s cfg.regularOpCost rest hc
  · intro fuel rest code post hc hnext
    exact wp_call_empty_vector cfg fuel rest s limits [] frame [] code vector r address post hi hf hd hc hnext

end WNear.Proofs.VectorDrop
