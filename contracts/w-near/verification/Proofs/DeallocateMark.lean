import Proofs.DeallocateArguments
import Proofs.ValueReturnBorrow
import NearVM.MeteredBitRules
import NearVM.MeteredI32MemoryRules

/-! Exact header mark and link initialization of the actual allocator f582. -/
namespace WNear.Proofs.Deallocate
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def header (pointer : UInt32) : UInt32 := pointer + 4294967288
def markedWord (memory : Memory) (pointer : UInt32) := readI32 memory (header pointer).toNat &&& 4294967294
def markedMemory (memory : Memory) (pointer : UInt32) := writeI32 memory (header pointer).toNat (markedWord memory pointer)
def markedStore (s : Store NearState) (op index : Nat) (memory : Memory) (pointer : UInt32) :=
  storeI32 (paid s op 9) index (header pointer).toNat memory (markedWord memory pointer)
def markedFrame (frame : CallFrame) (pointer : UInt32) := {frame with locals := frame.locals.set! 2 (.i32 (header pointer))}

/-- Compute the actual wrapping header address and keep a store operand. -/
theorem wp_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (post : Post)
    (hp : frame.locals[1]? = some (.i32 pointer))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits (stack.push (.i32 (header pointer)))
      (markedFrame frame pointer) callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 1,.i32_const 4294967288,.i32_binop .add,.local_tee 2] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 1 (.i32 pointer) post hp (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 4294967288 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ pointer 4294967288 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  have r := wp_local_tee cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 2 (.i32 (header pointer))
    post (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))) hnext
  simpa only [header,markedFrame,paid,List.append_eq,List.cons_append,List.nil_append] using r

def markTailStore (s : Store NearState) (op index : Nat) (memory : Memory) (address : UInt32) :=
  storeI32 (paid s op 5) index address.toNat memory (readI32 memory address.toNat &&& 4294967294)

def andStore (s : Store NearState) (op index : Nat) (memory : Memory) (address word mask : UInt32) :=
  storeI32 (paid s op 3) index address.toNat memory (word &&& mask)

/-- Generic three-opcode AND/store capsule with a separately supplied loaded word. -/
theorem wp_and_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address word mask : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (andStore s cfg.regularOpCost index memory address word mask)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits ((stack.push (.i32 address)).push (.i32 word)) frame callers
      ([.i32_const mask,.i32_binop .and,.store .i32 none {align := 2,offset := 0}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits _ frame callers _ mask post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_and cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ word mask post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have r := wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2,offset := 0} address (word &&& mask) mi index memory post hm2 hi m2 (by simpa using hb)
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega)))
  have hn : WP cfg fuel (.next (atCode (storeI32 (chargedStore (paid s cfg.regularOpCost 2) cfg.regularOpCost)
      index (address.toNat + 0) memory (word &&& mask)) limits stack frame callers code)) rest post := by
    simpa only [andStore,paid,Nat.add_zero] using hnext
  have res := r hn
  simpa only [paid,List.append_eq,List.cons_append,List.nil_append] using res

/-- Clear the allocated header bit through the real load/and/store sequence. -/
theorem wp_mark_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[2]? = some (.i32 address))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (markTailStore s cfg.regularOpCost index memory address)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits (stack.push (.i32 address)) frame callers
      ([.local_get 2,.load .i32 none {align := 2,offset := 0},.i32_const 4294967294,.i32_binop .and,
        .store .i32 none {align := 2,offset := 0}] ++ code))) (5 * cfg.regularOpCost + rest) post := by
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (andStore (paid s cfg.regularOpCost 2) cfg.regularOpCost index memory
      address (readI32 memory address.toNat) 4294967294) limits stack frame callers code)) rest post := by
    simpa only [andStore,markTailStore,ValueReturnBorrow.paid_add] using hnext
  have tail := wp_and_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    address (readI32 memory address.toNat) 4294967294 mi index memory post hm2 hi m2 hb
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hn
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits _ frame callers _ 2 (.i32 address) post hp (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  have r := wp_i32_load cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits (stack.push (.i32 address)) frame callers
    ([.i32_const 4294967294,.i32_binop .and,.store .i32 none {align := 2,offset := 0}] ++ code)
    {align := 2,offset := 0} address mi index memory post hm1 hi m1 (by simpa using hb)
    (paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega)))
  have nxt : WP cfg (fuel + 3) (.next (atCode (chargedStore (paid s cfg.regularOpCost 1) cfg.regularOpCost) limits
      ((stack.push (.i32 address)).push (.i32 (readI32 memory (address.toNat + 0))))
      frame callers ([.i32_const 4294967294,.i32_binop .and,.store .i32 none {align := 2,offset := 0}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by simpa only [paid,Nat.add_zero] using tail
  have result := r nxt
  simpa only [List.append_eq,List.cons_append,List.nil_append,paid] using result

/-- The actual nine instructions mark the freed block and save its header. -/
theorem wp_mark (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[1]? = some (.i32 pointer)) (hsize : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : (header pointer).toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (markedStore s cfg.regularOpCost index memory pointer)
      limits stack (markedFrame frame pointer) callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits stack frame callers
      (WNear.Binary.Deallocate.markFree ++ code))) (9 * cfg.regularOpCost + rest) post := by
  have h2 : 2 < frame.locals.size := by omega
  have hl : (markedFrame frame pointer).locals[2]? = some (.i32 (header pointer)) := by
    simp only [markedFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h2]
  have hm4 : (paid s cfg.regularOpCost 4).modules[(markedFrame frame pointer).inst]? = some mi := by simpa only [paid,chargedStore,markedFrame] using hm
  have m4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hc4 := paid_credits s cfg.regularOpCost 4 (5 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have hn : WP cfg fuel (.next (atCode (markTailStore (paid s cfg.regularOpCost 4) cfg.regularOpCost index memory (header pointer))
      limits stack (markedFrame frame pointer) callers code)) rest post := by
    simpa only [markTailStore,markedStore,markedWord,ValueReturnBorrow.paid_add] using hnext
  have tail := wp_mark_tail cfg fuel rest (paid s cfg.regularOpCost 4) limits stack (markedFrame frame pointer) callers code (header pointer) mi index memory post hl hm4 hi m4 hb hc4 hn
  have r := wp_header cfg (fuel + 5) (5 * cfg.regularOpCost + rest) s limits stack frame callers _ pointer post hp
    (hc.mono (by omega)) tail
  simpa only [WNear.Binary.Deallocate.markFree,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (5 * cfg.regularOpCost + rest) = 9 * cfg.regularOpCost + rest by omega] using r

/-- Save the allocator's current list head before changing the freed block. -/
theorem wp_save_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (allocator : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ha : frame.locals[0]? = some (.i32 allocator))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : allocator.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      {frame with locals := frame.locals.set! 4 (.i32 (readI32 memory allocator.toNat))} callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.saveHead ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 allocator) post ha (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 2,offset := 0} allocator mi index memory post hm1 hi m1 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have r := wp_local_set cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code 4
    (.i32 (readI32 memory allocator.toNat)) post (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext
  simpa only [paid,Nat.add_zero,List.append_eq,List.cons_append,List.nil_append] using r

def zeroStore (s : Store NearState) (op index : Nat) (memory : Memory) (pointer : UInt32) :=
  storeI32 (paid s op 3) index pointer.toNat memory 0

/-- The freed block's first list link is explicitly initialized to zero. -/
theorem wp_zero_link (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[1]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (zeroStore s cfg.regularOpCost index memory pointer)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.zeroLink ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 1 (.i32 pointer) post hp (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2,offset := 0} pointer 0 mi index memory post hm2 hi m2 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · simpa only [zeroStore,paid,Nat.add_zero] using hnext

end WNear.Proofs.Deallocate
