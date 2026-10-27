import Binary.VectorDrop
import Proofs.StorePairCallerState
import NearVM.MeteredWasmCall
import NearVM.MeteredNumericRules
import NearVM.MeteredControlRules
import NearVM.MeteredScalarRules
import NearVM.MeteredI32MemoryRules

/-! The real empty destructor and the zero-capacity vector branch. These proofs
skip allocator code by the executed capacity test, not by a callee hypothesis. -/
namespace WNear.Proofs.VectorDrop
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (10 * op + rest)) : (entered s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (9 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9 * op) rest c

/-- f778 is actually empty; only the call and activation are paid. -/
theorem wp_call_empty (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[778]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function778))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (10 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (entered s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits (base ++ [Value.i32 value]).toArray frame callers (.call 778 :: code)))
      (10 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame := {locals := #[Value.i32 value], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have cf := entered_credits s op rest hc
  have leaving := wp_leave_wasm cfg fuel rest (entered s op) limits base [] callee saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (entered s op) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have left := leaving (by simpa only [List.append_nil] using leaveNext)
  have callRule := wp_call_wasm cfg (fuel + 1) rest s limits base [.i32 value] frame callers code 778 address mi
    WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function778 post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function778 [.i32 value]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function778]
  rw [ha] at callRule
  have callNext : WP cfg (fuel + 1) (.next (wasmCallee (entered s op) limits base frame callers code
      WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function778 [.i32 value])) rest post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function778, WNear.Binary.VectorDrop.signature,
      callee, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_nil] using left
  have result := callRule (hc.mono (by dsimp [op]; omega)) callNext
  simpa only [Nat.add_assoc, Nat.reduceAdd, show cfg.regularOpCost + (9 * op + rest) = 10 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

def capacityFrame (frame : CallFrame) (capacity : UInt32) := {frame with locals := frame.locals.set! 1 (.i32 capacity)}

/-- The actual five-opcode vector guard reads its header and takes the branch
when capacity is zero. No pointer read or deallocation call is executed. -/
theorem wp_zero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hz : readI32 memory (vector.toNat + 4) = 0)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (capacityFrame frame 0) callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.VectorDrop.vectorGuard ++ WNear.Binary.VectorDrop.vectorTail))) (5 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let updated := capacityFrame frame 0
  let blocked := emptyBlockFrame frame stack.size code
  let newblocked := emptyBlockFrame updated stack.size code
  have br := wp_br_if_block_nonzero cfg fuel rest (paid s op 4) limits stack updated callers code
    WNear.Binary.VectorDrop.vectorTail 1 post (by decide) (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) hnext
  have eqz := wp_i32_eqz cfg (fuel + 1) (op + rest) (paid s op 3) limits stack newblocked callers
    (.br_if 0 :: WNear.Binary.VectorDrop.vectorTail) 0 post (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) br
  have tee := wp_local_tee cfg (fuel + 2) (2 * op + rest) (paid s op 2) limits stack blocked callers
    (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) 1 (.i32 0) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega)))
  have teeNext : WP cfg (fuel + 2) (.next (atCode (paid s op 3) limits (stack.push (.i32 0))
      {blocked with locals := blocked.locals.set! 1 (.i32 0)} callers (.i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail))) (2 * op + rest) post := by
    rw [show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at eqz
    simpa only [newblocked, updated, blocked, emptyBlockFrame, capacityFrame] using eqz
  have teed := tee teeNext
  have hm1 : (paid s op 1).modules[blocked.inst]? = some mi := by simpa only [paid, chargedStore, blocked, emptyBlockFrame] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 3) (3 * op + rest) (paid s op 1) limits stack blocked callers
    (.local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) {align := 2, offset := 4} vector mi index memory post
    hm1 hi hmem1 (by omega) (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have loadNext : WP cfg (fuel + 3) (.next (atCode (paid s op 2) limits (stack.push (.i32 (readI32 memory (vector.toNat + 4)))) blocked callers
      (.local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail))) (3 * op + rest) post := by
    rw [show cfg.regularOpCost + (2 * op + rest) = 3 * op + rest by dsimp [op]; omega] at teed
    simpa only [hz] using teed
  have loaded := load loadNext
  have get := wp_local_get cfg (fuel + 4) (4 * op + rest) s limits stack blocked callers
    (.load .i32 none {align := 2, offset := 4} :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: WNear.Binary.VectorDrop.vectorTail) 0 (.i32 vector) post hv (hc.mono (by dsimp [op]; omega))
  rw [show cfg.regularOpCost + (3 * op + rest) = 4 * op + rest by dsimp [op]; omega] at loaded
  have got := get loaded
  simpa only [WNear.Binary.VectorDrop.vectorGuard, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (4 * op + rest) = 5 * cfg.regularOpCost + rest by dsimp [op]; omega] using got

theorem wp_zero_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hv : frame.locals[0]? = some (.i32 vector))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hz : readI32 memory (vector.toNat + 4) = 0)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (capacityFrame frame 0) callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers (WNear.Binary.VectorDrop.body747 ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have body := wp_zero_guard cfg fuel rest s limits stack frame callers code vector mi index memory post hv hm hi hmem hb hz hc hnext
  have block := wp_block_empty cfg (fuel + 5) (5 * cfg.regularOpCost + rest) s limits stack frame callers
    (WNear.Binary.VectorDrop.vectorGuard ++ WNear.Binary.VectorDrop.vectorTail) code post hc body
  simpa only [WNear.Binary.VectorDrop.body747, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using block


def zeroAfter (s : Store NearState) (op : Nat) := paid (entered s op) op 5

theorem zeroAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (15 * op + rest)) : (zeroAfter s op).host.gas.Credits rest := by
  exact paid_credits (entered s op) op 5 rest (entered_credits s op (5 * op + rest) (hc.mono (by omega)))

/-- The complete actual f747 call on a zero-capacity vector header. -/
theorem wp_call_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[747]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747))
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hz : readI32 memory (vector.toNat + 4) = 0)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (zeroAfter s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits (base ++ [Value.i32 vector]).toArray frame callers (.call 747 :: code)))
      (15 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let callee : CallFrame := {locals := #[Value.i32 vector, Value.i32 0], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let updated := capacityFrame callee 0
  let saved := {frame with code}
  have ca := entered_credits s op (5 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := zeroAfter_credits s op rest hc
  have leaving := wp_leave_wasm cfg fuel rest (zeroAfter s op) limits base [] updated saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (zeroAfter s op) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op, List.append_nil] using hnext
  have left := leaving leaveNext
  have hm' : active.modules[callee.inst]? = some mi := by simpa only [active, entered, chargedStore, callee] using hm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have body := wp_zero_body cfg (fuel + 1) rest active limits base.toArray callee (saved :: callers) [] vector mi index memory post
    rfl hm' hi hmem' hb hz ca
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (paid active op 5) limits base.toArray (capacityFrame callee 0) (saved :: callers) [])) rest post := by
    simpa only [zeroAfter, active, updated, List.append_nil] using left
  have doneBody := body bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 6) (5 * op + rest) s limits base [.i32 vector] frame callers code 747 address mi
    WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747 post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function747 [.i32 vector]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function747, ValType.default]
  rw [ha] at callRule
  have arrays : #[Value.i32 vector] ++ #[Value.i32 0] = #[Value.i32 vector, Value.i32 0] := by
    apply Array.toList_inj.mp
    simp
  have callNext : WP cfg ((fuel + 1) + 6) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747 [.i32 vector])) (5 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function747, WNear.Binary.VectorDrop.signature,
      callee, saved, atCode, List.map_cons, List.map_nil, ValType.default, List.append_nil, List.length_nil, arrays] using doneBody
  have result := callRule (hc.mono (by dsimp [op]; omega)) callNext
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (5 * op + rest)) = 15 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.VectorDrop
