import Proofs.ValueReturnOuter

/-! Actual parameterized record-copy and pointer-selection instructions for SDK dispatch. -/
namespace WNear.Proofs.StateDispatchBorrow
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 writeI32
set_option maxRecDepth 16384

theorem wp_copy_record_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratchSlot pointerSlot : Nat) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[scratchSlot]? = some (.i32 scratch)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 12 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI32 (paid s cfg.regularOpCost 5) index (scratch.toNat + 8) memory (readI32 memory scratch.toNat))
      limits stack {frame with locals := frame.locals.set! pointerSlot (.i32 (readI32 memory scratch.toNat))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get scratchSlot, .local_get scratchSlot, .load .i32 none {align := 2, offset := 0},
        .local_tee pointerSlot, .store .i32 none {align := 2, offset := 8}] ++ code))) (5 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ scratchSlot (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ scratchSlot (.i32 scratch) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := 0} scratch mi index memory post hm2 hi hmem2 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ pointerSlot (.i32 (readI32 memory scratch.toNat)) post
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 4) limits stack
    {frame with locals := frame.locals.set! pointerSlot (.i32 (readI32 memory scratch.toNat))} callers code
    {align := 2, offset := 8} scratch (readI32 memory scratch.toNat) mi index memory post hm4 hi hmem4 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext


theorem wp_select_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointerSlot : Nat) (location ptr : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[pointerSlot]? = some (.i32 ptr)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : ptr.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((stack.push (.i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0))).push (.i32 location))
      frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get pointerSlot, .i32_const 0, .local_get pointerSlot, .load .i32 none {align := 2, offset := 0},
        .select none, .i32_const location] ++ code))) (6 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hconst := wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 5) limits
    (stack.push (.i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0))) frame callers code location post
    (paid_credits s cfg.regularOpCost 5 (cfg.regularOpCost + rest) (hc.mono (by omega))) hnext
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack frame callers _ pointerSlot (.i32 ptr) post hl (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ pointerSlot (.i32 ptr) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 3) limits _ frame callers _
    {align := 2, offset := 0} ptr mi index memory post hm3 hi hmem3 (by simpa using hb)
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_select cfg (fuel + 1) _ (paid s cfg.regularOpCost 4) limits stack frame callers _
    (.i32 ptr) (.i32 0) (readI32 memory ptr.toNat) post
  · apply paid_credits; exact hc.mono (by omega)
  · have selected : (if readI32 memory ptr.toNat ≠ 0 then Value.i32 ptr else .i32 0) = .i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0) := by split <;> rfl
    simpa only [selected, List.append, paid] using hconst


/-- Actual f440 argument loads derive receiver, register and vtable element
from the current memory, without semantic read or execution callbacks. -/
theorem wp_length_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell input : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[1]? = some (.i32 input)) (hn : 0 < frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hinput : input.toNat + 8 ≤ memory.byteSize)
    (hvtable : (readI32 memory (cell.toNat + 4)).toNat + 20 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (readI64 memory input.toNat)]).toArray.push
        (.i32 (readI32 memory ((readI32 memory (cell.toNat + 4)).toNat + 16))))
      {frame with locals := frame.locals.set! 0 (.i32 cell)} callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers
      ([.local_tee 0,.load .i32 none {align := 2,offset := 0},.local_get 1,.load .i64 none {align := 3,offset := 0},
        .local_get 0,.load .i32 none {align := 2,offset := 4},.load .i32 none {align := 2,offset := 16}] ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := {frame with locals := frame.locals.set! 0 (.i32 cell)}
  have hs' : f.locals[1]? = some (.i32 input) := by simpa [f] using hs
  have hp : f.locals[0]? = some (.i32 cell) := by simp [f,hn]
  have hm' (n : Nat) : (paid s op n).modules[f.inst]? = some mi := by
    have hr := congrArg (fun t : Store NearState => t.modules[frame.inst]?) (StorePairCaller.paid_resources s op n)
    simpa only [f] using hr.trans hm
  have mem' (n : Nat) : (paid s op n).mems[index]? = some memory := by
    have hr := congrArg (fun t : Store NearState => t.mems[index]?) (StorePairCaller.paid_resources s op n)
    exact hr.trans hmem
  have stackEq : ((base ++ [Value.i32 (readI32 memory cell.toNat),.i64 (readI64 memory input.toNat)]).toArray) =
      ((base.toArray.push (.i32 (readI32 memory cell.toNat))).push (.i64 (readI64 memory input.toNat))) := by
    apply Array.toList_inj.mp; simp
  have lastNext : WP cfg fuel (.next (atCode (paid s op 7) limits
      (((base.toArray.push (.i32 (readI32 memory cell.toNat))).push (.i64 (readI64 memory input.toNat))).push
        (.i32 (readI32 memory ((readI32 memory (cell.toNat + 4)).toNat + 16)))) f callers code)) rest post := by
    simpa only [stackEq,op,f] using hnext
  have last := wp_i32_load cfg fuel rest (paid s op 6) limits
    ((base.toArray.push (.i32 (readI32 memory cell.toNat))).push (.i64 (readI64 memory input.toNat))) f callers code
    {align := 2,offset := 16} (readI32 memory (cell.toNat + 4)) mi index memory post (hm' 6) hi (mem' 6)
    hvtable (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) lastNext
  have prev := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 5) limits
    ((base.toArray.push (.i32 (readI32 memory cell.toNat))).push (.i64 (readI64 memory input.toNat))) f callers
    (.load .i32 none {align := 2,offset := 16} :: code) {align := 2,offset := 4} cell mi index memory post
    (hm' 5) hi (mem' 5) (by omega) (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) last
  have get0 := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 4) limits
    ((base.toArray.push (.i32 (readI32 memory cell.toNat))).push (.i64 (readI64 memory input.toNat))) f callers
    (.load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 16} :: code) 0 (.i32 cell) post hp
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) prev
  have load64 := wp_i64_load cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 3) limits
    (base.toArray.push (.i32 (readI32 memory cell.toNat))) f callers
    (.local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 16} :: code)
    {align := 3,offset := 0} input mi index memory post (hm' 3) hi (mem' 3) (by simpa using hinput)
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) get0
  have get1 := wp_local_get cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 2) limits
    (base.toArray.push (.i32 (readI32 memory cell.toNat))) f callers
    (.load .i64 none {align := 3,offset := 0} :: .local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 16} :: code)
    1 (.i32 input) post hs' (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) load64
  have load32 := wp_i32_load cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 1) limits base.toArray f callers
    (.local_get 1 :: .load .i64 none {align := 3,offset := 0} :: .local_get 0 :: .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 16} :: code)
    {align := 2,offset := 0} cell mi index memory post (hm' 1) hi (mem' 1) (by change cell.toNat + 0 + 4 ≤ memory.byteSize; omega)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) get1
  have first := wp_local_tee cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) s limits base.toArray frame callers
    (.load .i32 none {align := 2,offset := 0} :: .local_get 1 :: .load .i64 none {align := 3,offset := 0} :: .local_get 0 ::
      .load .i32 none {align := 2,offset := 4} :: .load .i32 none {align := 2,offset := 16} :: code)
    0 (.i32 cell) post (hc.mono (by dsimp [op]; omega)) load32
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (op + (op + (op + (op + (op + rest)))))) = 7 * cfg.regularOpCost + rest by dsimp [op]; omega] using first

end WNear.Proofs.StateDispatchBorrow
