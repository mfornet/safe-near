import Proofs.DeallocatePrevious
import Proofs.DeallocateAlignNative
import Proofs.DeallocateListSize

/-! Actual get/call/drop phases of f582, including both complete callees. -/
namespace WNear.Proofs.Deallocate
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def aligned (s : Store NearState) (op : Nat) := paid (DeallocateAlign.after570 (paid s op 1) op) op 1
def sized (s : Store NearState) (op : Nat) := paid (DeallocateListSize.after (paid s op 1) op) op 1

theorem aligned_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (43 * op + rest)) :
    (aligned s op).host.gas.Credits rest := by
  apply paid_credits (DeallocateAlign.after570 (paid s op 1) op) op 1 rest
  simpa only [Nat.one_mul] using DeallocateAlign.after570_credits (paid s op 1) op (op + rest) (paid_credits s op 1 _ (hc.mono (by omega)))

theorem sized_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (27 * op + rest)) :
    (sized s op).host.gas.Credits rest := by
  apply paid_credits (DeallocateListSize.after (paid s op 1) op) op 1 rest
  simpa only [Nat.one_mul] using DeallocateListSize.after_credits (paid s op 1) op (op + rest) (paid_credits s op 1 _ (hc.mono (by omega)))

/-- The real alignment result is computed and discarded before touching the heap. -/
theorem wp_align_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (length : UInt32) (mi : ModuleInst) (address568 address570 : Nat) (post : Post)
    (hl : frame.locals[2]? = some (.i32 length))
    (hm : s.modules[frame.inst]? = some mi) (hi568 : mi.funcAddrs[568]? = some address568)
    (hf568 : s.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi570 : mi.funcAddrs[570]? = some address570)
    (hf570 : s.funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570))
    (hn : length.toNat + 4 < 2 ^ 32) (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (43 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (aligned s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 27) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Deallocate.alignCall ++ code)))
      (43 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hs := DeallocateAlign.checks570 length hn
  have afterCall := DeallocateAlign.after570_credits (paid s op 1) op (op + rest)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have dropNext : WP cfg fuel (.next (atCode (chargedStore (DeallocateAlign.after570 (paid s op 1) op) cfg.regularOpCost)
      limits base.toArray frame callers code)) rest post := by simpa only [aligned,paid,op] using hnext
  have drop := wp_drop cfg fuel rest (DeallocateAlign.after570 (paid s op 1) op) limits base.toArray frame callers code
    (.i32 (DeallocateAlign.quotient length 4)) post afterCall dropNext
  have stackEq : (base ++ [Value.i32 (DeallocateAlign.quotient length 4)]).toArray = base.toArray.push (.i32 (DeallocateAlign.quotient length 4)) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel + 1) (.next (atCode (DeallocateAlign.after570 (paid s op 1) op) limits
      (base ++ [Value.i32 (DeallocateAlign.quotient length 4)]).toArray frame callers (.drop :: code))) (op + rest) post := by
    simpa only [stackEq,op] using drop
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have f568 : (paid s op 1).funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568) := by simpa only [paid,chargedStore] using hf568
  have f570 : (paid s op 1).funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570) := by simpa only [paid,chargedStore] using hf570
  have call := DeallocateAlign.wp_call570 cfg (fuel + 1) (op + rest) (paid s op 1) limits base frame callers (.drop :: code)
    length mi address568 address570 post hm1 hi568 f568 hi570 f570 hs.1 hs.2 hd
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) callNext
  have argEq : (base ++ [Value.i32 length]).toArray = base.toArray.push (.i32 length) := by apply Array.toList_inj.mp; simp
  have next : WP cfg (fuel + 26) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 length)) frame callers (.call 570 :: .drop :: code)))
      (42 * cfg.regularOpCost + rest) post := by
    simpa only [argEq,Nat.add_assoc,Nat.reduceAdd,show 41 * cfg.regularOpCost + (op + rest) = 42 * cfg.regularOpCost + rest by dsimp [op]; omega] using call
  have get := wp_local_get cfg (fuel + 26) (42 * cfg.regularOpCost + rest) s limits base.toArray frame callers (.call 570 :: .drop :: code) 2 (.i32 length) post hl (hc.mono (by omega)) next
  simpa only [WNear.Binary.Deallocate.alignCall,List.append_eq,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (42 * cfg.regularOpCost + rest) = 43 * cfg.regularOpCost + rest by omega] using get

/-- The actual size helper is checked, returned, and discarded. -/
theorem wp_size_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[2]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hfi : mi.funcAddrs[576]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction))
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : pointer.toNat + 4 ≤ memory.byteSize) (hs : pointer.toNat + 8 ≤ (DeallocateListSize.endWord memory pointer).toNat)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (sized s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 19) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Deallocate.sizeCall ++ code)))
      (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have afterCall := DeallocateListSize.after_credits (paid s op 1) op (op + rest)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have dropNext : WP cfg fuel (.next (atCode (chargedStore (DeallocateListSize.after (paid s op 1) op) cfg.regularOpCost)
      limits base.toArray frame callers code)) rest post := by simpa only [sized,paid,op] using hnext
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
  have get := wp_local_get cfg (fuel + 18) (26 * cfg.regularOpCost + rest) s limits base.toArray frame callers (.call 576 :: .drop :: code) 2 (.i32 pointer) post hp (hc.mono (by omega)) next
  simpa only [WNear.Binary.Deallocate.sizeCall,List.append_eq,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (26 * cfg.regularOpCost + rest) = 27 * cfg.regularOpCost + rest by omega] using get

end WNear.Proofs.Deallocate
