import Proofs.DeallocateCoreState
import NearVM.MeteredSelectionRules

/-! Actual post-unlink coalescing tail, checked over arbitrary current memory. -/
namespace WNear.Proofs.DeallocateCoreTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP atCode readI32 writeI32
theorem wp_size_previous (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[5]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hfi : mi.funcAddrs[576]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction))
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : pointer.toNat + 4 ≤ memory.byteSize) (hs : pointer.toNat + 8 ≤ (DeallocateListSize.endWord memory pointer).toNat)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (Deallocate.sized s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 19) (.next (atCode s limits base.toArray frame callers ([.local_get 5, .call 576, .drop] ++ code)))
      (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have afterCall := DeallocateListSize.after_credits (paid s op 1) op (op + rest)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have dropNext : WP cfg fuel (.next (atCode (chargedStore (DeallocateListSize.after (paid s op 1) op) cfg.regularOpCost)
      limits base.toArray frame callers code)) rest post := by simpa only [Deallocate.sized,paid,op] using hnext
  have drop := wp_drop cfg fuel rest (DeallocateListSize.after (paid s op 1) op) limits base.toArray frame callers code
    (.i32 (DeallocateListSize.size memory pointer)) post afterCall dropNext
  have stackEq : (base ++ [Value.i32 (DeallocateListSize.size memory pointer)]).toArray = base.toArray.push (.i32 (DeallocateListSize.size memory pointer)) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel + 1) (.next (atCode (DeallocateListSize.after (paid s op 1) op) limits
      (base ++ [Value.i32 (DeallocateListSize.size memory pointer)]).toArray frame callers (.drop :: code))) (op + rest) post := by simpa only [stackEq,op] using drop
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hf1 : (paid s op 1).funcs[address]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction) := by simpa only [paid,chargedStore] using hf
  have m1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have call := DeallocateListSize.wp_call cfg (fuel + 1) (op + rest) (paid s op 1) limits base frame callers (.drop :: code)
    pointer mi address index memory post hm1 hfi hf1 hi m1 hb hs hd (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) callNext
  have argEq : (base ++ [Value.i32 pointer]).toArray = base.toArray.push (.i32 pointer) := by apply Array.toList_inj.mp; simp
  have next : WP cfg (fuel + 18) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 pointer)) frame callers (.call 576 :: .drop :: code)))
      (26 * cfg.regularOpCost + rest) post := by
    simpa only [argEq,Nat.add_assoc,Nat.reduceAdd,show 25 * cfg.regularOpCost + (op + rest) = 26 * cfg.regularOpCost + rest by dsimp [op]; omega] using call
  have get := wp_local_get cfg (fuel + 18) (26 * cfg.regularOpCost + rest) s limits base.toArray frame callers (.call 576 :: .drop :: code) 5 (.i32 pointer) post hp (hc.mono (by omega)) next
  simpa only [List.append_eq,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (26 * cfg.regularOpCost + rest) = 27 * cfg.regularOpCost + rest by omega] using get



def propagateWrites : Expr := [.local_get 5, .local_get 5, .load .i32 none {align := 2, offset := 0},
  .i32_const 2, .i32_binop .or, .store .i32 none {align := 2, offset := 0}]

/-- Zero flag bit2 branches over the propagation writes, after a real byte load. -/
theorem wp_flag_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[2]? = some (.i32 header))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : header.toNat + 1 ≤ memory.byteSize)
    (hz : readByteWord memory header.toNat &&& 2 = 0)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers (.block .empty WNear.Binary.Deallocate.propagateFlag :: code)))
      (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let blocked := emptyBlockFrame frame stack.size code
  have hm1 : (paid s op 1).modules[blocked.inst]? = some mi := by simpa only [paid, chargedStore, blocked, emptyBlockFrame] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 5) limits stack frame callers code propagateWrites 1 post (by decide)
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) hnext
  have guard : WP cfg (fuel + 6) (.next (atCode s limits stack blocked callers WNear.Binary.Deallocate.propagateFlag)) (6 * op + rest) post := by
    rw [show 6 * op + rest = cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
    apply wp_local_get cfg (fuel + 5) _ s limits stack blocked callers _ 2 (.i32 header) post hp (hc.mono (by dsimp [op]; omega))
    rw [show 5 * op + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
    apply wp_i32_load8_unsigned cfg (fuel + 4) _ (paid s op 1) limits stack blocked callers _ {align := 0, offset := 0} header mi index memory post hm1 hi hmem1 (by simpa using hb)
    · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
    rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
    apply wp_i32_const cfg (fuel + 3) _ (paid s op 2) limits _ blocked callers _ 2 post
    · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
    rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
    apply wp_i32_and cfg (fuel + 2) _ (paid s op 3) limits stack blocked callers _ (readByteWord memory (header.toNat + 0)) 2 post
    · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
    simp only [Nat.add_zero, hz]
    rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
    apply wp_i32_eqz cfg (fuel + 1) _ (paid s op 4) limits stack blocked callers _ 0 post
    · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
    · simpa only [propagateWrites, blocked, paid, Numeric.bool, beq_self_eq_true, ite_true] using branch
  have block := wp_block_empty cfg (fuel + 6) (6 * op + rest) s limits stack frame callers WNear.Binary.Deallocate.propagateFlag code post hc guard
  simpa only [Nat.add_assoc, Nat.reduceAdd] using block


def restoredFrame (frame : CallFrame) (value : UInt32) := {frame with locals := frame.locals.set! 2 (.i32 value)}
def installed (s : Store NearState) (op index : Nat) (memory : Memory) (allocator oldHead : UInt32) :=
  storeI32 (paid s op 3) index allocator.toNat memory oldHead

/-- Actual three-opcode head installation over arbitrary current memory. -/
theorem wp_install (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (allocator oldHead : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[0]? = some (.i32 allocator)) (hv : frame.locals[2]? = some (.i32 oldHead))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : allocator.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (installed s cfg.regularOpCost index memory allocator oldHead) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.installHead ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 allocator) post ha (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s op 1) limits _ frame callers _ 2 (.i32 oldHead) post hv
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align := 2, offset := 0} allocator oldHead mi index memory post hm2 hi hmem2 (by simpa using hb)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- Restore the saved head, branch out of both real blocks, and execute the
head write. The discarded insertion branch is never executed. -/
theorem wp_restore_install (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (allocator oldHead : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[0]? = some (.i32 allocator)) (hv : frame.locals[4]? = some (.i32 oldHead)) (hs : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : allocator.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 6) index allocator.toNat memory oldHead) limits stack (restoredFrame frame oldHead) callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size (WNear.Binary.Deallocate.installHead ++ code)) stack.size WNear.Binary.Deallocate.insertHead)
      callers [.local_get 4, .local_set 2, .br 1])) (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let updated := restoredFrame frame oldHead
  let nested := emptyBlockFrame (emptyBlockFrame frame stack.size (WNear.Binary.Deallocate.installHead ++ code)) stack.size WNear.Binary.Deallocate.insertHead
  let newNested := emptyBlockFrame (emptyBlockFrame updated stack.size (WNear.Binary.Deallocate.installHead ++ code)) stack.size WNear.Binary.Deallocate.insertHead
  have ha' : updated.locals[0]? = some (.i32 allocator) := by simpa [updated, restoredFrame] using ha
  have hv' : updated.locals[2]? = some (.i32 oldHead) := by simp [updated, restoredFrame, show 2 < frame.locals.size by omega]
  have hm3 : (paid s op 3).modules[updated.inst]? = some mi := by simpa only [paid, chargedStore, updated, restoredFrame] using hm
  have hmem3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have installNext : WP cfg fuel (.next (atCode (installed (paid s op 3) op index memory allocator oldHead) limits stack updated callers code)) rest post := by
    simpa only [installed, ValueReturnBorrow.paid_add, Nat.reduceAdd, updated] using hnext
  have install := wp_install cfg fuel rest (paid s op 3) limits stack updated callers code allocator oldHead mi index memory post ha' hv' hm3 hi hmem3 hb
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) installNext
  have br := wp_br_two_blocks cfg (fuel + 3) (3 * op + rest) (paid s op 2) limits stack updated callers
    (WNear.Binary.Deallocate.installHead ++ code) WNear.Binary.Deallocate.insertHead [] post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) install
  have setRule := wp_local_set cfg (fuel + 4) (4 * op + rest) (paid s op 1) limits stack nested callers [.br 1] 2 (.i32 oldHead) post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have setNext : WP cfg (fuel + 4) (.next (atCode (paid s op 2) limits stack {nested with locals := nested.locals.set! 2 (.i32 oldHead)} callers [.br 1])) (4 * op + rest) post := by
    simpa only [newNested, nested, updated, restoredFrame, emptyBlockFrame,
      show cfg.regularOpCost + (3 * op + rest) = 4 * op + rest by dsimp [op]; omega] using br
  have set := setRule setNext
  rw [show cfg.regularOpCost + (4 * op + rest) = 5 * op + rest by dsimp [op]; omega] at set
  have get := wp_local_get cfg (fuel + 5) (5 * op + rest) s limits stack nested callers [.local_set 2, .br 1] 4 (.i32 oldHead) post hv
    (hc.mono (by dsimp [op]; omega)) set
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (5 * op + rest) = 6 * cfg.regularOpCost + rest by dsimp [op]; omega] using get


def tailCode : Expr := [.block .empty WNear.Binary.Deallocate.propagateFlag, .local_get 5, .call 576, .drop, .local_get 4, .local_set 2, .br 1]
def after (s : Store NearState) (op index : Nat) (memory : Memory) (allocator oldHead : UInt32) :=
  storeI32 (paid (Deallocate.sized (paid s op 6) op) op 6) index allocator.toNat memory oldHead

theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (allocator oldHead : UInt32)
    (hc : s.host.gas.Credits (39 * op + rest)) : (after s op index memory allocator oldHead).host.gas.Credits rest := by
  have c1 := paid_credits s op 6 (33 * op + rest) (hc.mono (by omega))
  have c2 := Deallocate.sized_credits (paid s op 6) op (6 * op + rest) (c1.mono (by omega))
  exact paid_credits (Deallocate.sized (paid s op 6) op) op 6 rest c2

/-- Complete post-f575 coalescing tail: the zero flag skips propagation, the
actual f576 result is discarded, both blocks are exited, and the old allocator
head is written back. All memory hypotheses concern the actual current memory. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : DeallocateCore.Layout) (memory : Memory) (post : Post)
    (hcode : DeallocateCore.Code s frame.inst p)
    (hmem : s.mems[p.memoryIndex]? = some memory)
    (ha : frame.locals[0]? = some (.i32 p.allocator)) (hh : frame.locals[2]? = some (.i32 p.header))
    (ho : frame.locals[4]? = some (.i32 (DeallocateCore.oldHead p))) (hp : frame.locals[5]? = some (.i32 p.previous))
    (hs : 3 ≤ frame.locals.size)
    (hb : p.header.toNat + 1 ≤ memory.byteSize) (hz : readByteWord memory p.header.toNat &&& 2 = 0)
    (hpb : p.previous.toNat + 4 ≤ memory.byteSize)
    (hsize : p.previous.toNat + 8 ≤ (DeallocateListSize.endWord memory p.previous).toNat)
    (hab : p.allocator.toNat + 4 ≤ memory.byteSize) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (39 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p.memoryIndex memory p.allocator (DeallocateCore.oldHead p)) limits base.toArray
      (restoredFrame frame (DeallocateCore.oldHead p)) callers code)) rest post) :
    WP cfg (fuel + 32) (.next (atCode s limits base.toArray
      (emptyBlockFrame (emptyBlockFrame frame base.toArray.size (WNear.Binary.Deallocate.installHead ++ code)) base.toArray.size WNear.Binary.Deallocate.insertHead)
      callers tailCode)) (39 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let nested := emptyBlockFrame (emptyBlockFrame frame base.toArray.size (WNear.Binary.Deallocate.installHead ++ code)) base.toArray.size WNear.Binary.Deallocate.insertHead
  let sized := Deallocate.sized (paid s op 6) op
  have c1 := paid_credits s op 6 (33 * op + rest) (hc.mono (by dsimp [op]; omega))
  have c2 := Deallocate.sized_credits (paid s op 6) op (6 * op + rest) (c1.mono (by omega))
  have hm2 : sized.modules[frame.inst]? = some p.mi := by
    simpa only [sized, Deallocate.sized, DeallocateListSize.after, DeallocateListSize.entered, paid, chargedStore] using hcode.module
  have hmem2 : sized.mems[p.memoryIndex]? = some memory := by
    simpa only [sized, Deallocate.sized, DeallocateListSize.after, DeallocateListSize.entered, paid, chargedStore] using hmem
  have restoreNext : WP cfg fuel (.next (atCode (storeI32 (paid sized op 6) p.memoryIndex p.allocator.toNat memory (DeallocateCore.oldHead p)) limits base.toArray
      (restoredFrame frame (DeallocateCore.oldHead p)) callers code)) rest post := by
    simpa only [after, sized] using hnext
  have restore := wp_restore_install cfg fuel rest sized limits base.toArray frame callers code p.allocator (DeallocateCore.oldHead p) p.mi p.memoryIndex memory post
    ha ho hs hm2 hcode.memoryIndex hmem2 hab c2 restoreNext
  have hm1 : (paid s op 6).modules[nested.inst]? = some p.mi := by simpa only [paid, chargedStore, nested, emptyBlockFrame] using hcode.module
  have hf1 : (paid s op 6).funcs[p.address576]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature nested.inst WNear.Binary.DeallocateList.sizeFunction) := by
    simpa only [paid, chargedStore, nested, emptyBlockFrame] using hcode.function576
  have hmem1 : (paid s op 6).mems[p.memoryIndex]? = some memory := by simpa only [paid, chargedStore] using hmem
  have sizeNext : WP cfg (fuel + 6) (.next (atCode (Deallocate.sized (paid s op 6) op) limits base.toArray nested callers [.local_get 4, .local_set 2, .br 1])) (6 * op + rest) post := by
    simpa only [nested] using restore
  have sizeCall := wp_size_previous cfg (fuel + 6) (6 * op + rest) (paid s op 6) limits base nested callers [.local_get 4, .local_set 2, .br 1]
    p.previous p.mi p.address576 p.memoryIndex memory post hp hm1 hcode.index576 hf1 hcode.memoryIndex hmem1 hpb hsize hd (c1.mono (by dsimp [op]; omega)) sizeNext
  have flagNext : WP cfg (fuel + 25) (.next (atCode (paid s op 6) limits base.toArray nested callers
      [.local_get 5, .call 576, .drop, .local_get 4, .local_set 2, .br 1])) (33 * op + rest) post := by
    simpa only [List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
      show 27 * cfg.regularOpCost + (6 * op + rest) = 33 * op + rest by dsimp [op]; omega] using sizeCall
  have flag := wp_flag_zero cfg (fuel + 25) (33 * op + rest) s limits base.toArray nested callers
    [.local_get 5, .call 576, .drop, .local_get 4, .local_set 2, .br 1] p.header p.mi p.memoryIndex memory post hh
    hcode.module hcode.memoryIndex hmem hb hz (hc.mono (by dsimp [op]; omega)) flagNext
  simpa only [tailCode, Nat.add_assoc, Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (33 * op + rest) = 39 * cfg.regularOpCost + rest by dsimp [op]; omega] using flag
end WNear.Proofs.DeallocateCoreTail
