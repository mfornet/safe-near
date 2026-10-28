import Proofs.DeallocateInsertHead
import Proofs.DeallocatePrevious

/-! Actual previous-allocated guard falls through both conditional branches. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic Deallocate DeallocateCore
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

theorem wp_previous_allocated_flag (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[5]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 1 ≤ memory.byteSize)
    (hallocated : readByteWord memory pointer.toNat &&& 1 ≠ 0)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack
      frame callers
      ([.local_get 5,.load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},
        .i32_const 1,.i32_binop .and,.i32_eqz,.br_if 1] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  let f := frame
  have hm1 : (paid s cfg.regularOpCost 1).modules[f.inst]? = some mi := by simpa only [paid,chargedStore,f,emptyBlockFrame] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack f callers _ 5 (.i32 pointer) post hp (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load8_unsigned cfg (fuel + 4) _ (paid s cfg.regularOpCost 1) limits stack f callers _
    {align := 0,offset := 0} pointer mi index memory post hm1 hi m1 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 2) limits _ f callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_and cfg (fuel + 2) _ (paid s cfg.regularOpCost 3) limits stack f callers _ (readByteWord memory (pointer.toNat + 0)) 1 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  simp only [Nat.add_zero]
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 4) limits stack f callers _ (readByteWord memory pointer.toNat &&&1) post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  have hz:Numeric.bool ((readByteWord memory pointer.toNat &&&1)==0)=0:=by simp only[Numeric.bool,beq_iff_eq,hallocated,↓reduceIte]
  have r:=wp_br_if_zero cfg fuel rest (paid s cfg.regularOpCost 5) limits stack frame callers code 1 post
    (paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))) hnext
  simpa only[f,hz,paid,List.append_eq,List.cons_append,List.nil_append] using r

theorem wp_previous_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer address value : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[1]? = some (.i32 pointer)) (hs : 6 ≤ frame.locals.size)
    (hcalc : pointer + 4294967292 = address) (hvalue : previous memory address = value)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address.toNat + 4 ≤ memory.byteSize)
    (hnz : value ≠ 0) (hv : value.toNat + 1 ≤ memory.byteSize)
    (hallocated : readByteWord memory value.toNat &&& 1 ≠ 0)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 15) limits stack
      (previousFrame frame value) callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits stack
      frame callers
      (WNear.Binary.Deallocate.previousGuard++code))) (15 * cfg.regularOpCost + rest) post := by
  let nested := frame
  let updated := previousFrame frame value
  have h5 : 5 < frame.locals.size := by omega
  have hl : updated.locals[5]? = some (.i32 value) := by
    simp only [updated,previousFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h5]
  have hm9 : (paid s cfg.regularOpCost 9).modules[updated.inst]? = some mi := by simpa only [paid,chargedStore,updated,previousFrame] using hm
  have m9 : (paid s cfg.regularOpCost 9).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (paid (paid s cfg.regularOpCost 9) cfg.regularOpCost 6) limits stack updated callers code)) rest post := by
    simpa only [ValueReturnBorrow.paid_add,updated] using hnext
  have tail := wp_previous_allocated_flag cfg fuel rest (paid s cfg.regularOpCost 9) limits stack updated callers code
    value mi index memory post hl hm9 hi m9 hv hallocated (paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))) hn
  have hm3 : (paid s cfg.regularOpCost 3).modules[nested.inst]? = some mi := by simpa only [paid,chargedStore,nested,emptyBlockFrame] using hm
  have m3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have wordNext : WP cfg (fuel + 6) (.next (atCode (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 6) limits stack
      (previousFrame nested (previous memory address)) callers
      ([.local_get 5,.load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},.i32_const 1,.i32_binop .and,.i32_eqz,.br_if 1]++code)))
      (6 * cfg.regularOpCost + rest) post := by
    simpa only [ValueReturnBorrow.paid_add,hvalue,updated,nested,previousFrame,emptyBlockFrame,
      List.append_nil] using tail
  have word := wp_previous_word cfg (fuel + 6) (6 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 3) limits stack nested callers _ address mi index memory post
    hm3 hi m3 hb (by rw [hvalue]; exact hnz) (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))) wordNext
  have next : WP cfg (fuel + 12) (.next (atCode (paid s cfg.regularOpCost 3) limits (stack.push (.i32 address)) nested callers
      ([.load .i32 none {align := 2,offset := 0},.i32_const 4294967292,.i32_binop .and,.local_tee 5,.i32_eqz,.br_if 0] ++
      ([.local_get 5,.load .i32 (some {bits := 8,signed := false}) {align := 0,offset := 0},.i32_const 1,.i32_binop .and,.i32_eqz,.br_if 1]++code))))
      (12 * cfg.regularOpCost + rest) post := by
    simpa only [Nat.add_assoc,Nat.reduceAdd,show 6 * cfg.regularOpCost + (6 * cfg.regularOpCost + rest) = 12 * cfg.regularOpCost + rest by omega] using word
  have r := wp_previous_address cfg (fuel + 12) (12 * cfg.regularOpCost + rest) s limits stack nested callers _ pointer address post hp hcalc
    (hc.mono (by omega)) next
  simpa only [WNear.Binary.Deallocate.previousGuard,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3 * cfg.regularOpCost + (12 * cfg.regularOpCost + rest) = 15 * cfg.regularOpCost + rest by omega] using r

end WNear.Proofs.DeallocateInsert
