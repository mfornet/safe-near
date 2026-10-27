import Binary.DeallocateList
import NearVM.MeteredBitRules
import Proofs.ValueReturnLazyReturn
import Proofs.ValueReturnOuterBody

/-! Actual accepted header-size leaf f576, with an initial native header bound. -/
namespace WNear.Proofs.DeallocateListSize
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP readI32

def endWord (memory : Memory) (pointer : UInt32) := readI32 memory pointer.toNat &&& 4294967292
def size (memory : Memory) (pointer : UInt32) := endWord memory pointer - pointer + 4294967288

theorem size_nat (memory : Memory) (pointer : UInt32)
    (h : pointer.toNat + 8 ≤ (endWord memory pointer).toNat) :
    (size memory pointer).toNat = (endWord memory pointer).toNat - pointer.toNat - 8 := by
  rw [size, UInt32.toNat_add, UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat]
  have he := UInt32.toNat_lt (endWord memory pointer)
  have hp := UInt32.toNat_lt pointer
  omega

theorem size_guard (memory : Memory) (pointer : UInt32)
    (h : pointer.toNat + 8 ≤ (endWord memory pointer).toNat) :
    Numeric.irelop32 .gt_u (size memory pointer) (endWord memory pointer) = false := by
  change decide (endWord memory pointer < size memory pointer) = false
  simp only [decide_eq_false_iff_not]
  rw [UInt32.lt_iff_toNat_lt, size_nat memory pointer h]
  omega

/-- Five actual tail instructions end in the callee's explicit return. -/
theorem wp_return_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (result endpoint : UInt32) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 result)) (h1 : frame.locals[1]? = some (.i32 endpoint))
    (hguard : Numeric.irelop32 .gt_u result endpoint = false)
    (ha : frame.arity = 1) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (base ++ [Value.i32 result]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits (base.toArray.push (.i32 result)) frame (caller :: callers)
      [.local_get 1, .i32_relop .gt_u, .br_if 0, .local_get 0, .return])) (5 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest (paid s op 4) limits base [.i32 result]
    frame caller callers [] post (by simpa only [List.length_cons, List.length_nil] using ha.symm) hh
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) hnext
  have stackEq : (base ++ [Value.i32 result]).toArray = base.toArray.push (.i32 result) := by apply Array.toList_inj.mp; simp
  have retNext : WP cfg (fuel + 1) (.next (atCode (paid s op 4) limits
      (base.toArray.push (.i32 result)) frame (caller :: callers) [.return])) (op + rest) post := by
    simpa only [stackEq, op] using ret
  have get := wp_local_get cfg (fuel + 1) (op + rest) (paid s op 3) limits base.toArray frame (caller :: callers)
    [.return] 0 (.i32 result) post h0 (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) retNext
  have branch := wp_br_if_zero cfg (fuel + 2) (op + (op + rest)) (paid s op 2) limits base.toArray frame (caller :: callers)
    [.local_get 0, .return] 0 post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) get
  have relNext : WP cfg (fuel + 3) (.next (atCode (paid s op 2) limits
      (base.toArray.push (.i32 (Numeric.bool (Numeric.irelop32 .gt_u result endpoint)))) frame (caller :: callers)
      [.br_if 0, .local_get 0, .return])) (op + (op + (op + rest))) post := by
    simpa [hguard, Numeric.bool, op, Nat.add_assoc] using branch
  have rel := wp_i32_relop cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 1) limits base.toArray frame (caller :: callers)
    [.br_if 0, .local_get 0, .return] .gt_u result endpoint post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) relNext
  have get1 := wp_local_get cfg (fuel + 4) (op + (op + (op + (op + rest)))) s limits (base.toArray.push (.i32 result))
    frame (caller :: callers) [.i32_relop .gt_u, .br_if 0, .local_get 0, .return] 1 (.i32 endpoint) post h1
    (hc.mono (by dsimp [op]; omega)) rel
  have ge : cfg.regularOpCost + (op + (op + (op + (op + rest)))) = 5 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits (base.toArray.push (.i32 result)) frame (caller :: callers) _ _ post rfl ge rfl get1

/-- Complete accepted f576, with native initial-header bounds selecting its
normal return instead of the allocator assertion failure. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (hn : 2 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 4 ≤ memory.byteSize)
    (hsize : pointer.toNat + 8 ≤ (endWord memory pointer).toNat)
    (ha : frame.arity = 1) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 15) limits
      (base ++ [Value.i32 (size memory pointer)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 16) (.next (atCode s limits base.toArray frame (caller :: callers)
      WNear.Binary.DeallocateList.sizeBody)) (15 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let endpoint := endWord memory pointer
  let result := size memory pointer
  let bf := emptyBlockFrame frame base.toArray.size WNear.Binary.DeallocateList.sizePanic
  let f1 := {bf with locals := bf.locals.set! 1 (.i32 endpoint)}
  let f2 := {f1 with locals := f1.locals.set! 0 (.i32 result)}
  let tc : List Instr := [.local_get 1, .i32_relop .gt_u, .br_if 0, .local_get 0, .return]
  have hn0 : 0 < frame.locals.size := by omega
  have hn1 : 1 < frame.locals.size := by omega
  have h0 : f2.locals[0]? = some (.i32 result) := by simp [f2, f1, bf, emptyBlockFrame, hn0]
  have h1 : f2.locals[1]? = some (.i32 endpoint) := by simp [f2, f1, bf, emptyBlockFrame, hn1]
  have hp1 : f1.locals[0]? = some (.i32 pointer) := by simpa [f1, bf, emptyBlockFrame] using hp
  have hnxt : WP cfg fuel (.next (atCode (paid (paid s op 10) op 5) limits
      (base ++ [Value.i32 result]).toArray caller callers caller.code)) rest post := by
    simpa only [paid, op, result] using hnext
  have ret := wp_return_tail cfg fuel rest (paid s op 10) limits base f2 caller callers result endpoint post h0 h1
    (size_guard memory pointer hsize) ha hh (paid_credits s op 10 _ (hc.mono (by dsimp [op]; omega))) hnxt
  have tee0 := wp_local_tee cfg (fuel + 5) (5 * op + rest) (paid s op 9) limits base.toArray f1 (caller :: callers)
    tc 0 (.i32 result) post (paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))) ret
  have add := wp_i32_add cfg (fuel + 6) (op + (5 * op + rest)) (paid s op 8) limits base.toArray f1 (caller :: callers)
    (.local_tee 0 :: tc) (endpoint - pointer) 4294967288 post
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) tee0
  have con := wp_i32_const cfg (fuel + 7) (op + (op + (5 * op + rest))) (paid s op 7) limits
    (base.toArray.push (.i32 (endpoint - pointer))) f1 (caller :: callers) (.i32_binop .add :: .local_tee 0 :: tc)
    4294967288 post (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) add
  have sub := wp_i32_sub cfg (fuel + 8) (op + (op + (op + (5 * op + rest)))) (paid s op 6) limits base.toArray f1
    (caller :: callers) (.i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc) endpoint pointer post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) con
  have get := wp_local_get cfg (fuel + 9) (op + (op + (op + (op + (5 * op + rest))))) (paid s op 5) limits
    (base.toArray.push (.i32 endpoint)) f1 (caller :: callers)
    (.i32_binop .sub :: .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc) 0 (.i32 pointer) post hp1
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) sub
  have tee1 := wp_local_tee cfg (fuel + 10) (op + (op + (op + (op + (op + (5 * op + rest)))))) (paid s op 4) limits base.toArray bf
    (caller :: callers) (.local_get 0 :: .i32_binop .sub :: .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc)
    1 (.i32 endpoint) post (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) get
  have andNext : WP cfg (fuel + 11) (.next (atCode (paid s op 4) limits
      (base.toArray.push (.i32 (readI32 memory pointer.toNat &&& 4294967292))) bf (caller :: callers)
      (.local_tee 1 :: .local_get 0 :: .i32_binop .sub :: .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc)))
      (op + (op + (op + (op + (op + (op + (5 * op + rest))))))) post := by
    simpa only [endpoint, endWord, tc, op] using tee1
  have and := wp_i32_and cfg (fuel + 11) (op + (op + (op + (op + (op + (op + (5 * op + rest))))))) (paid s op 3)
    limits base.toArray bf (caller :: callers) (.local_tee 1 :: .local_get 0 :: .i32_binop .sub :: .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc)
    (readI32 memory pointer.toNat) 4294967292 post (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) andNext
  have mask := wp_i32_const cfg (fuel + 12) (op + (op + (op + (op + (op + (op + (op + (5 * op + rest)))))))) (paid s op 2)
    limits (base.toArray.push (.i32 (readI32 memory pointer.toNat))) bf (caller :: callers)
    (.i32_binop .and :: .local_tee 1 :: .local_get 0 :: .i32_binop .sub :: .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc)
    4294967292 post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) and
  have hm1 : (paid s op 1).modules[bf.inst]? = some mi := by simpa only [paid, chargedStore, bf, emptyBlockFrame] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 13) (op + (op + (op + (op + (op + (op + (op + (op + (5 * op + rest))))))))) (paid s op 1)
    limits base.toArray bf (caller :: callers) (.i32_const 4294967292 :: .i32_binop .and :: .local_tee 1 :: .local_get 0 :: .i32_binop .sub ::
      .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc) {align := 2, offset := 0} pointer mi index memory post hm1 hi hmem1
    (by simpa using hb) (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) mask
  have head := wp_local_get cfg (fuel + 14) (op + (op + (op + (op + (op + (op + (op + (op + (op + (5 * op + rest)))))))))) s limits base.toArray bf
    (caller :: callers) (.load .i32 none {align := 2, offset := 0} :: .i32_const 4294967292 :: .i32_binop .and :: .local_tee 1 :: .local_get 0 :: .i32_binop .sub ::
      .i32_const 4294967288 :: .i32_binop .add :: .local_tee 0 :: tc) 0 (.i32 pointer) post hp
    (hc.mono (by dsimp [op]; omega)) load
  have inside : WP cfg (fuel + 15) (.next (atCode s limits base.toArray bf (caller :: callers)
      WNear.Binary.DeallocateList.sizePrefix)) (15 * op + rest) post := by
    have ge : cfg.regularOpCost + (op + (op + (op + (op + (op + (op + (op + (op + (op + (5 * op + rest)))))))))) = 15 * op + rest := by dsimp [op]; omega
    simpa only [ge, tc, WNear.Binary.DeallocateList.sizePrefix] using head
  have block := wp_block_empty cfg (fuel + 15) (15 * op + rest) s limits base.toArray frame (caller :: callers)
    WNear.Binary.DeallocateList.sizePrefix WNear.Binary.DeallocateList.sizePanic post hc inside
  simpa only [WNear.Binary.DeallocateList.sizeBody, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, op] using block

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def after (s : Store NearState) (op : Nat) := paid (entered s op) op 15

theorem after_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (25 * op + rest)) : (after s op).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (9 * op + (15 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (9 * op) (15 * op + rest) hop
  exact paid_credits (entered s op) op 15 rest ca

/-- Real typed576call, with the native size returned by the actual explicit
return. Its assertion branch and853are bypassed by initial arithmetic data. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hfi : mi.funcAddrs[576]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction))
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : pointer.toNat + 4 ≤ memory.byteSize)
    (hsize : pointer.toNat + 8 ≤ (endWord memory pointer).toNat)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (25 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost) limits
      (base ++ [Value.i32 (size memory pointer)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 17) (.next (atCode s limits (base ++ [Value.i32 pointer]).toArray frame callers (.call 576 :: code)))
      (25 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[.i32 pointer, .i32 0], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have hop := StorePair.charged_credits s op (9 * op + (15 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (15 * op + rest) := StorePair.charged_credits (chargedStore s op) (9 * op) (15 * op + rest) hop
  have hmA : active.modules[leaf.inst]? = some mi := by simpa only [active, entered, chargedStore, leaf] using hm
  have hmemA : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have bodyNext : WP cfg fuel (.next (atCode (paid active op 15) limits
      (base ++ [Value.i32 (size memory pointer)]).toArray saved callers saved.code)) rest post := by
    simpa only [after, active, saved, atCode, op] using hnext
  have body := wp_body cfg fuel rest active limits base leaf saved callers pointer mi index memory post
    rfl (by simp [leaf]) hmA hi hmemA hb hsize rfl rfl ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 16) (15 * op + rest) s limits base [.i32 pointer]
    frame callers code 576 address mi WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction post hm hfi hf rfl hd
  have hact : activationGas op (wasmLocals WNear.Binary.DeallocateList.sizeFunction [.i32 pointer]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.DeallocateList.sizeFunction, ValType.default]
  rw [hact] at callRule
  have bodyCast : WP cfg (fuel + 16) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction [.i32 pointer])) (15 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.DeallocateList.sizeSignature, WNear.Binary.DeallocateList.sizeFunction,
      atCode, leaf, saved, ValType.default] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) bodyCast
  have ge : cfg.regularOpCost + (9 * op + (15 * op + rest)) = 25 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits (base ++ [Value.i32 pointer]).toArray frame callers _ _ post rfl ge rfl result

end WNear.Proofs.DeallocateListSize
