import Proofs.VectorDropPrefix

/-! Typed, real nested calls leading to the remaining allocator call. These
prefix contracts stop before invoking f237 and assume no deallocator result. -/
namespace WNear.Proofs.VectorDrop
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def tripleEntry (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def tripleFrame (inst height : Nat) (a b c : UInt32) : CallFrame :=
  {locals := #[.i32 a, .i32 b, .i32 c], inst, arity := 0, height, labels := [], code := []}
def vectorFrame (inst height : Nat) (vector : UInt32) : CallFrame :=
  {locals := #[.i32 vector, .i32 0], inst, arity := 0, height, labels := [], code := []}

theorem tripleEntry_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11 * op + rest)) : (tripleEntry s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (10 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10 * op) rest c

/-- The actual f311 call enters its typed frame, loads its three parameters,
and stops at the actual f237 call. The explicit return remains after it. -/
theorem wp_call_forward_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b c : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[311]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function311))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (14 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid (tripleEntry s cfg.regularOpCost) cfg.regularOpCost 3) limits
      (base ++ [Value.i32 a, .i32 b, .i32 c]).toArray (tripleFrame frame.inst base.length a b c)
      ({frame with code} :: callers) [.call 237, .return])) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits (base ++ [Value.i32 a, .i32 b, .i32 c]).toArray frame callers (.call 311 :: code)))
      (14 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let leaf := tripleFrame frame.inst base.length a b c
  have ca := tripleEntry_credits s op (3 * op + rest) (hc.mono (by dsimp [op]; omega))
  have argsArray : (base ++ [Value.i32 a, .i32 b, .i32 c]).toArray = ((base.toArray.push (.i32 a)).push (.i32 b)).push (.i32 c) := by
    apply Array.toList_inj.mp
    simp
  have bodyNext : WP cfg fuel (.next (atCode (paid (tripleEntry s op) op 3) limits
      (((base.toArray.push (.i32 a)).push (.i32 b)).push (.i32 c)) leaf ({frame with code} :: callers) [.call 237, .return])) rest post := by
    simpa only [argsArray, leaf, op] using hnext
  have body := wp_forward_prefix cfg fuel rest (tripleEntry s op) limits base.toArray leaf ({frame with code} :: callers) a b c post rfl rfl rfl ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 3) (3 * op + rest) s limits base [.i32 a, .i32 b, .i32 c] frame callers code 311 address mi
    WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function311 post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function311 [.i32 a, .i32 b, .i32 c]) = 10 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function311]
  rw [ha] at callRule
  have next : WP cfg (fuel + 3) (.next (wasmCallee (tripleEntry s op) limits base frame callers code
      WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function311 [.i32 a, .i32 b, .i32 c])) (3 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function311, WNear.Binary.VectorDrop.tripleSignature,
      leaf, tripleFrame, atCode, List.map_nil, Array.append_empty, List.length_nil] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (3 * op + rest)) = 14 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

/-- Actual f777 activation and positive branch, stopping at its f311 call. -/
theorem wp_call_capacity_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a capacity alignment : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[777]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function777))
    (hn : capacity ≠ 0) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid (tripleEntry s cfg.regularOpCost) cfg.regularOpCost 6) limits
      (base ++ [Value.i32 a, .i32 capacity, .i32 alignment]).toArray
      (emptyBlockFrame (tripleFrame frame.inst base.length a capacity alignment) base.toArray.size [])
      ({frame with code} :: callers) [.call 311])) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits (base ++ [Value.i32 a, .i32 capacity, .i32 alignment]).toArray frame callers (.call 777 :: code)))
      (17 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let leaf := tripleFrame frame.inst base.length a capacity alignment
  have ca := tripleEntry_credits s op (6 * op + rest) (hc.mono (by dsimp [op]; omega))
  have argsArray : (base ++ [Value.i32 a, .i32 capacity, .i32 alignment]).toArray = ((base.toArray.push (.i32 a)).push (.i32 capacity)).push (.i32 alignment) := by
    apply Array.toList_inj.mp
    simp
  have bodyNext : WP cfg fuel (.next (atCode (paid (tripleEntry s op) op 6) limits
      (((base.toArray.push (.i32 a)).push (.i32 capacity)).push (.i32 alignment))
      (emptyBlockFrame leaf base.toArray.size []) ({frame with code} :: callers) [.call 311])) rest post := by
    simpa only [argsArray, leaf, op] using hnext
  have body := wp_capacity_prefix cfg fuel rest (tripleEntry s op) limits base.toArray leaf ({frame with code} :: callers) [] a capacity alignment post
    rfl rfl rfl hn ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 7) (6 * op + rest) s limits base [.i32 a, .i32 capacity, .i32 alignment] frame callers code 777 address mi
    WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function777 post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function777 [.i32 a, .i32 capacity, .i32 alignment]) = 10 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function777]
  rw [ha] at callRule
  have next : WP cfg (fuel + 7) (.next (wasmCallee (tripleEntry s op) limits base frame callers code
      WNear.Binary.VectorDrop.tripleSignature frame.inst WNear.Binary.VectorDrop.function777 [.i32 a, .i32 capacity, .i32 alignment])) (6 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function777, WNear.Binary.VectorDrop.tripleSignature,
      leaf, tripleFrame, atCode, List.map_nil, Array.append_empty, List.length_nil, List.append_nil] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (6 * op + rest)) = 17 * cfg.regularOpCost + rest by dsimp [op]; omega] using result



/-- Actual f747 activation, header check and pointer load on positive capacity.
The next machine instruction is the installed f777 call. -/
theorem wp_call_vector_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (vector : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[747]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747))
    (hb : vector.toNat + 8 ≤ memory.byteSize) (hn : readI32 memory (vector.toNat + 4) ≠ 0)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (19 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid (entered s cfg.regularOpCost) cfg.regularOpCost 9) limits
      (base ++ [Value.i32 (readI32 memory vector.toNat), .i32 (readI32 memory (vector.toNat + 4)), .i32 1]).toArray
      (emptyBlockFrame (capacityFrame (vectorFrame frame.inst base.length vector) (readI32 memory (vector.toNat + 4))) base.toArray.size [])
      ({frame with code} :: callers) [.call 777])) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits (base ++ [Value.i32 vector]).toArray frame callers (.call 747 :: code)))
      (19 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := vectorFrame frame.inst base.length vector
  have ca := entered_credits s op (9 * op + rest) (hc.mono (by dsimp [op]; omega))
  have argsArray : (base ++ [Value.i32 (readI32 memory vector.toNat), .i32 (readI32 memory (vector.toNat + 4)), .i32 1]).toArray =
      ((base.toArray.push (.i32 (readI32 memory vector.toNat))).push (.i32 (readI32 memory (vector.toNat + 4)))).push (.i32 1) := by
    apply Array.toList_inj.mp
    simp
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf, vectorFrame] using hm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have bodyNext : WP cfg fuel (.next (atCode (paid active op 9) limits
      (((base.toArray.push (.i32 (readI32 memory vector.toNat))).push (.i32 (readI32 memory (vector.toNat + 4)))).push (.i32 1))
      (emptyBlockFrame (capacityFrame leaf (readI32 memory (vector.toNat + 4))) base.toArray.size []) ({frame with code} :: callers) [.call 777])) rest post := by
    simpa only [argsArray, active, leaf, op] using hnext
  have body := wp_vector_prefix cfg fuel rest active limits base.toArray leaf ({frame with code} :: callers) [] vector mi index memory post
    rfl (by simp [leaf, vectorFrame]) hm' hi hmem' hb hn ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 10) (9 * op + rest) s limits base [.i32 vector] frame callers code 747 address mi
    WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747 post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.VectorDrop.function747 [.i32 vector]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.VectorDrop.function747, ValType.default]
  rw [ha] at callRule
  have arrays : #[Value.i32 vector] ++ #[Value.i32 0] = #[Value.i32 vector, Value.i32 0] := by
    apply Array.toList_inj.mp
    simp
  have next : WP cfg (fuel + 10) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.VectorDrop.signature frame.inst WNear.Binary.VectorDrop.function747 [.i32 vector])) (9 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.VectorDrop.function747, WNear.Binary.VectorDrop.signature,
      leaf, vectorFrame, atCode, List.map_cons, List.map_nil, ValType.default, List.append_nil, List.length_nil, arrays] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (9 * op + rest)) = 19 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.VectorDrop
