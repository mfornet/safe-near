import Proofs.SerializeFormatterPrefix
import NearVM.MeteredWasmCall

/-! Actual typed formatter calls through the argument reads, before f902. -/
namespace WNear.Proofs.SerializeFormatter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def leafFrame (inst height : Nat) (pointer context : UInt32) : CallFrame :=
  {locals := #[.i32 pointer, .i32 context], inst, arity := 1, height, labels := [], code := []}

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (10 * op + rest)) : (entered s op).host.gas.Credits rest :=
  StorePair.charged_credits (chargedStore s op) (9 * op) rest
    (StorePair.charged_credits s op (9 * op + rest) (hc.mono (by omega)))

/-- The actual f901 call reaches f902 with both memory-decoded U128 words,
flagone and the original context. f902 is not assumed to execute successfully. -/
theorem wp_call_u128_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer context : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[901]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function))
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hb : pointer.toNat + 16 ≤ memory.byteSize)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (18 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid (entered s cfg.regularOpCost) cfg.regularOpCost 8) limits
      (base ++ [Value.i64 (readI64 memory pointer.toNat), .i64 (readI64 memory (pointer.toNat+8)), .i32 1, .i32 context]).toArray
      (leafFrame frame.inst base.length pointer context) ({frame with code} :: callers) [.call 902])) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits (base ++ [Value.i32 pointer, .i32 context]).toArray frame callers (.call 901 :: code)))
      (18 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length pointer context
  have ca := entered_credits s op (8 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf, leafFrame] using hm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have array : (base ++ [Value.i64 (readI64 memory pointer.toNat), .i64 (readI64 memory (pointer.toNat+8)), .i32 1, .i32 context]).toArray =
      (((base.toArray.push (.i64 (readI64 memory pointer.toNat))).push (.i64 (readI64 memory (pointer.toNat+8)))).push (.i32 1)).push (.i32 context) := by
    apply Array.toList_inj.mp
    simp
  have bodyNext : WP cfg fuel (.next (atCode (paid active op 8) limits
      ((((base.toArray.push (.i64 (readI64 memory pointer.toNat))).push (.i64 (readI64 memory (pointer.toNat+8)))).push (.i32 1)).push (.i32 context))
      leaf ({frame with code} :: callers) [.call 902])) rest post := by
    simpa only [array, active, leaf, op] using hnext
  have body := wp_u128_prefix cfg fuel rest active limits base.toArray leaf ({frame with code} :: callers) [.call 902] pointer context mi index memory post
    rfl rfl hm' hi hmem' hwidth hb ca bodyNext
  have rule := wp_call_wasm cfg (fuel + 8) (8 * op + rest) s limits base [.i32 pointer, .i32 context] frame callers code 901 address mi
    WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.SerializeFormatter.u128Function [.i32 pointer, .i32 context]) = 9 * op := by simp [activationGas, wasmLocals, WNear.Binary.SerializeFormatter.u128Function]
  rw [ha] at rule
  have next : WP cfg (fuel + 8) (.next (wasmCallee active limits base frame callers code WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function [.i32 pointer, .i32 context])) (8 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.SerializeFormatter.u128Function, WNear.Binary.SerializeFormatter.u128Body,
      WNear.Binary.SerializeFormatter.signature, leaf, leafFrame, atCode, List.map_nil, Array.append_empty, List.length_cons, List.length_nil, Nat.reduceAdd] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd, show cfg.regularOpCost + (9 * op + (8 * op + rest)) = 18 * cfg.regularOpCost + rest by dsimp [op]; omega] using result


def boxDecimalAfter (s : Store NearState) (op : Nat) := paid (entered (paid s op 3) op) op 8

/-- Complete f353 body prefix through the actual nested f901 call, stopping
before f902's decimal conversion. Both pointers are read from original memory. -/
theorem wp_box_body_to_decimal (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (box context : UInt32) (mi : ModuleInst) (index address901 : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 box)) (hcxt : frame.locals[1]? = some (.i32 context))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[901]? = some address901)
    (hf : s.funcs[address901]? = some (.wasm WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function))
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hb : box.toNat + 4 ≤ memory.byteSize)
    (hdata : (readI32 memory box.toNat).toNat + 16 ≤ memory.byteSize) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (21 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (boxDecimalAfter s cfg.regularOpCost) limits
      (base ++ [Value.i64 (readI64 memory (readI32 memory box.toNat).toNat),
        .i64 (readI64 memory ((readI32 memory box.toNat).toNat+8)), .i32 1, .i32 context]).toArray
      (leafFrame frame.inst base.length (readI32 memory box.toNat) context) ({frame with code} :: callers) [.call 902])) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits base.toArray frame callers (WNear.Binary.SerializeFormatter.boxBody ++ code)))
      (21 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pointer := readI32 memory box.toNat
  have hm3 : (paid s op 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hf3 : (paid s op 3).funcs[address901]? = some (.wasm WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function) := by
    simpa only [paid, chargedStore] using hf
  have call := wp_call_u128_prefix cfg fuel rest (paid s op 3) limits base frame callers code pointer context mi index address901 memory post hm3 hi hmem3 hfi hf3 hwidth hdata hd
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have array : (base ++ [Value.i32 pointer, .i32 context]).toArray = (base.toArray.push (.i32 pointer)).push (.i32 context) := by
    apply Array.toList_inj.mp
    simp
  have boxNext : WP cfg (fuel + 9) (.next (atCode (paid s op 3) limits ((base.toArray.push (.i32 (readI32 memory box.toNat))).push (.i32 context)) frame callers (.call 901 :: code)))
      (18 * op + rest) post := by simpa only [array, pointer] using call
  have boxRule := wp_box_prefix cfg (fuel + 9) (18 * op + rest) s limits base.toArray frame callers (.call 901 :: code) box context mi index memory post hp hcxt hm hi hmem hb
    (hc.mono (by dsimp [op]; omega)) boxNext
  simpa only [WNear.Binary.SerializeFormatter.boxBody, List.append_assoc, List.singleton_append, Nat.add_assoc, Nat.reduceAdd,
    show 3 * cfg.regularOpCost + (18 * op + rest) = 21 * cfg.regularOpCost + rest by dsimp [op]; omega] using boxRule

/-- The table-selected f353 call and real f901 adapter preserve the model's
original U128 words until the actual f902 call. No formatter or allocator
execution result occurs in the premises. -/
theorem wp_call_box_to_decimal (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (box context : UInt32) (mi : ModuleInst) (index address353 address901 : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hi353 : mi.funcAddrs[353]? = some address353)
    (hf353 : s.funcs[address353]? = some (.wasm WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.boxFunction))
    (hi901 : mi.funcAddrs[901]? = some address901)
    (hf901 : s.funcs[address901]? = some (.wasm WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.u128Function))
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hb : box.toNat + 4 ≤ memory.byteSize)
    (hdata : (readI32 memory box.toNat).toNat + 16 ≤ memory.byteSize) (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (31 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (boxDecimalAfter (entered s cfg.regularOpCost) cfg.regularOpCost) limits
      (base ++ [Value.i64 (readI64 memory (readI32 memory box.toNat).toNat),
        .i64 (readI64 memory ((readI32 memory box.toNat).toNat+8)), .i32 1, .i32 context]).toArray
      (leafFrame frame.inst base.length (readI32 memory box.toNat) context)
      (leafFrame frame.inst base.length box context :: {frame with code} :: callers) [.call 902])) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits (base ++ [Value.i32 box, .i32 context]).toArray frame callers (.call 353 :: code)))
      (31 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length box context
  have ca := entered_credits s op (21 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf, leafFrame] using hm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have hf' : active.funcs[address901]? = some (.wasm WNear.Binary.SerializeFormatter.signature leaf.inst WNear.Binary.SerializeFormatter.u128Function) := by
    simpa only [active, entered, chargedStore, leaf, leafFrame] using hf901
  have bodyNext : WP cfg fuel (.next (atCode (boxDecimalAfter active op) limits
      (base ++ [Value.i64 (readI64 memory (readI32 memory box.toNat).toNat),
        .i64 (readI64 memory ((readI32 memory box.toNat).toNat+8)), .i32 1, .i32 context]).toArray
      (leafFrame leaf.inst base.length (readI32 memory box.toNat) context) ({leaf with code := []} :: {frame with code} :: callers) [.call 902])) rest post := by
    simpa only [active, leaf, leafFrame] using hnext
  have body := wp_box_body_to_decimal cfg fuel rest active limits base leaf ({frame with code} :: callers) [] box context mi index address901 memory post
    rfl rfl hm' hi hmem' hi901 hf' hwidth hb hdata (by simpa only [List.length_cons] using hd) ca bodyNext
  have rule := wp_call_wasm cfg (fuel + 12) (21 * op + rest) s limits base [.i32 box, .i32 context] frame callers code 353 address353 mi
    WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.boxFunction post hm hi353 hf353 rfl (by omega)
  have ha : activationGas op (wasmLocals WNear.Binary.SerializeFormatter.boxFunction [.i32 box, .i32 context]) = 9 * op := by simp [activationGas, wasmLocals, WNear.Binary.SerializeFormatter.boxFunction]
  rw [ha] at rule
  have next : WP cfg (fuel + 12) (.next (wasmCallee active limits base frame callers code WNear.Binary.SerializeFormatter.signature frame.inst WNear.Binary.SerializeFormatter.boxFunction [.i32 box, .i32 context])) (21 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.SerializeFormatter.boxFunction, WNear.Binary.SerializeFormatter.signature, leaf, leafFrame, atCode,
      List.map_nil, Array.append_empty, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd, show cfg.regularOpCost + (9 * op + (21 * op + rest)) = 31 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.SerializeFormatter
