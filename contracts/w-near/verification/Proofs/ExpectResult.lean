import Proofs.ExpectResultState
import NearVM.MeteredControlRules
import Proofs.StorePair

/-! Actual accepted execution of deployed Result::expect f158. -/
namespace WNear.Proofs.ExpectResult
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.ExpectResultState
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

theorem wp_prologue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 5) index (.i32 (sp - 16))) limits stack
      {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have h1 := paid_credits s cfg.regularOpCost 1 (4 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h2 := paid_credits s cfg.regularOpCost 2 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h3 := paid_credits s cfg.regularOpCost 3 (2 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h4 := paid_credits s cfg.regularOpCost 4 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg4 : (paid s cfg.regularOpCost 4).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  have hget := wp_global_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0] ++ code)
    0 index mi global post hmodule hindex hglobal h0
  rw [hsp] at hget
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply hget
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
    (by simpa only [paid, show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega] using h1)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_sub cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits stack frame callers _ sp 16 post
    (by simpa only [paid, show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega] using h2)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ 3 (.i32 (sp - 16)) post
    (by simpa only [paid, show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega] using h3)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 4) limits stack {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))} callers code 0 index mi (.i32 (sp - 16)) global post
    hm4 hindex hg4
  · simpa only [paid] using h4
  · simpa only [paid] using hnext

theorem wp_restore (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (scratch : UInt32) (post : Post)
    (hscratch : frame.locals[3]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 16))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg3 : (paid s cfg.regularOpCost 3).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 3 (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
  · apply paid_credits s cfg.regularOpCost 1
    exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ scratch 16 post
  · apply paid_credits s cfg.regularOpCost 2
    exact hc.mono (by omega)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 0 index mi (.i32 (scratch + 16)) global post
    hm3 hindex hg3
  · apply paid_credits s cfg.regularOpCost 3
    exact hc.mono (by omega)
  · simpa only [paid] using hnext


/-- The actual discriminant test exits its zero-result block before the
panic tail. The discarded instructions need no execution contract. -/
theorem wp_tagCheck (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hbound : source.toNat + 4 ≤ memory.byteSize) (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.ExpectResult.tagCheck ++ WNear.Binary.ExpectResult.panicTail)))
      (5 * cfg.regularOpCost + rest) post := by
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by
    simpa only [paid, chargedStore] using hmodule
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmemory
  have hcondition : Numeric.bool (readI32 memory source.toNat != 1) ≠ 0 := by
    simp [Numeric.bool, htag]
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack
    (emptyBlockFrame frame stack.size code) callers _ 1 (.i32 source) post hsource (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1)
    limits _ (emptyBlockFrame frame stack.size code) callers _ {align := 2, offset := 0}
    source mi index memory post hm1 hindex hmem1 (by simpa using hbound)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _
    (emptyBlockFrame frame stack.size code) callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_ne cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack
    (emptyBlockFrame frame stack.size code) callers _ (readI32 memory source.toNat) 1 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 4) limits stack frame callers
    code WNear.Binary.ExpectResult.panicTail _ post hcondition
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  · exact hnext

/-- The first payload copy reads its whole i64 before writing output. -/
theorem wp_copyLow (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hsourceBound : source.toNat + 12 ≤ memory.byteSize) (houtBound : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI64 (paid s cfg.regularOpCost 4) index out.toNat memory (lowWord memory source.toNat))
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (WNear.Binary.ExpectResult.copyLow ++ code))) (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 out) post hout (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := 4} source mi index memory post hm2 hindex hmem2 (by change source.toNat + 4 + 8 ≤ memory.byteSize; omega)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 2, offset := 0} out (lowWord memory source.toNat) mi index memory post hm3 hindex hmem3
    (by simpa using houtBound)
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · exact hnext

/-- The second payload copy reads from the memory supplied after the first
write. Its source and destination may overlap arbitrarily. -/
theorem wp_copyHigh (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hsourcePlus : (source + 12).toNat = source.toNat + 12)
    (houtPlus : (out + 8).toNat = out.toNat + 8)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize) (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI32 (paid s cfg.regularOpCost 8) index (out.toNat + 8) memory
        (readI32 memory (source.toNat + 12))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers
      (WNear.Binary.ExpectResult.copyHigh ++ code))) (8 * cfg.regularOpCost + rest) post := by
  have hm6 : (paid s cfg.regularOpCost 6).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm7 : (paid s cfg.regularOpCost 7).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem7 : (paid s cfg.regularOpCost 7).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 7) (7 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 out) post hout (hc.mono (by omega))
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 6) (6 * cfg.regularOpCost + rest) _ limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 5) (5 * cfg.regularOpCost + rest) _ limits stack frame callers _ out 8 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 12 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ source 12 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 6) limits _ frame callers _
    {align := 2, offset := 0} (source + 12) mi index memory post hm6 hindex hmem6
    (by change (source + 12).toNat + 0 + 4 ≤ memory.byteSize; rw [hsourcePlus]; omega)
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 7) limits stack frame callers code
    {align := 2, offset := 0} (out + 8) (readI32 memory ((source + 12).toNat + 0)) mi index memory post hm7 hindex hmem7
    (by change (out + 8).toNat + 0 + 4 ≤ memory.byteSize; rw [houtPlus]; omega)
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  · simpa only [paid, hsourcePlus, houtPlus, Nat.add_zero] using hnext

/-- The sole local update on the accepted branch stores the wrapping saved
stack pointer. The other locals and all caller labels are retained. -/
def afterFrame (frame : CallFrame) (sp : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))}

/-- Actual accepted body from an arbitrary active caller context. No contract
for the discarded panic call is assumed. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (sp out source : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst)
    (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hsize : 4 ≤ frame.locals.size) (hmodule : s.modules[frame.inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory)
      limits stack (afterFrame frame sp) callers code)) rest post) :
    WP cfg (fuel + 27) (.next (atCode s limits stack frame callers
      (WNear.Binary.ExpectResult.body ++ code))) (26 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let frame' := afterFrame frame sp
  have hscratch : frame'.locals[3]? = some (.i32 (sp - 16)) := by
    simp [frame', afterFrame, show 3 < frame.locals.size by omega]
  have hout' : frame'.locals[0]? = some (.i32 out) := by
    simpa [frame', afterFrame] using hout
  have hsource' : frame'.locals[1]? = some (.i32 source) := by
    simpa [frame', afterFrame] using hsource
  have houtPlus : (out + 8).toNat = out.toNat + 8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hsourcePlus : (source + 12).toNat = source.toNat + 12 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have h0 : s.host.gas.Credits (5 * op + (21 * op + rest)) := hc.mono (by dsimp [op]; omega)
  have hr : (reserved s op globalIndex sp).host.gas.Credits (5 * op + (16 * op + rest)) := by
    have h := paid_credits s op 5 (21 * op + rest) h0
    simpa only [reserved, setGlobal, show 5 * op + (16 * op + rest) = 21 * op + rest by omega] using h
  have ht : (checked s op globalIndex sp).host.gas.Credits (4 * op + (12 * op + rest)) := by
    have h := paid_credits (reserved s op globalIndex sp) op 5 (16 * op + rest) hr
    simpa only [checked, show 4 * op + (12 * op + rest) = 16 * op + rest by omega] using h
  have hl : (lowStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits
      (8 * op + (4 * op + rest)) := by
    have h := paid_credits (checked s op globalIndex sp) op 4 (12 * op + rest) ht
    simpa only [lowStore, storeI64, show 8 * op + (4 * op + rest) = 12 * op + rest by omega] using h
  have hh : (highStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits
      (4 * op + rest) := by
    have h := paid_credits (lowStore s op globalIndex memoryIndex sp out source memory) op 8 (4 * op + rest) hl
    simpa only [highStore, storeI32] using h
  have hgr : (reserved s op globalIndex sp).globals[globalIndex]? =
      some {global with value := .i32 (sp - 16)} := by
    simp [reserved, setGlobal, paid, chargedStore, Array.getElem?_modify, hglobal]
  have hgh : (highStore s op globalIndex memoryIndex sp out source memory).globals[globalIndex]? =
      some {global with value := .i32 (sp - 16)} := by
    simpa only [highStore, lowStore, checked, storeI32, storeI64, paid, chargedStore] using hgr
  have hmr : (reserved s op globalIndex sp).modules[frame'.inst]? = some mi := by
    simpa only [reserved, setGlobal, paid, chargedStore, frame', afterFrame] using hmodule
  have hmt : (checked s op globalIndex sp).modules[frame'.inst]? = some mi := by
    simpa only [checked, paid, chargedStore] using hmr
  have hml : (lowStore s op globalIndex memoryIndex sp out source memory).modules[frame'.inst]? = some mi := by
    simpa only [lowStore, storeI64, paid, chargedStore] using hmt
  have hmh : (highStore s op globalIndex memoryIndex sp out source memory).modules[frame'.inst]? = some mi := by
    simpa only [highStore, storeI32, paid, chargedStore] using hml
  have hmemr : (reserved s op globalIndex sp).mems[memoryIndex]? = some memory := by
    simpa only [reserved, setGlobal, paid, chargedStore] using hmemory
  have hmemt : (checked s op globalIndex sp).mems[memoryIndex]? = some memory := by
    simpa only [checked, paid, chargedStore] using hmemr
  have hmeml : (lowStore s op globalIndex memoryIndex sp out source memory).mems[memoryIndex]? =
      some (lowMemory memory out.toNat source.toNat) := by
    apply storeI64_memory
    simpa only [paid, chargedStore] using hmemt
  have hbLow : out.toNat + 8 ≤ memory.byteSize := by omega
  have hlowSpec := writeI64_spec memory out.toNat (lowWord memory source.toNat) hwf hbLow
  have hlowSize : (lowMemory memory out.toNat source.toNat).byteSize = memory.byteSize := hlowSpec.2.1
  have hbSourceLow : source.toNat + 12 ≤ memory.byteSize := by omega
  have hbSourceHigh : source.toNat + 16 ≤ (lowMemory memory out.toNat source.toNat).byteSize := by
    rw [hlowSize]; exact hsourceBound
  have hbOutHigh : out.toNat + 12 ≤ (lowMemory memory out.toNat source.toNat).byteSize := by
    rw [hlowSize]; exact houtBound
  have hrestore := wp_restore cfg fuel rest
    (highStore s op globalIndex memoryIndex sp out source memory) limits stack frame' callers code
    mi globalIndex {global with value := .i32 (sp - 16)} (sp - 16) post
    hscratch hmh hglobalIndex hgh hh
  have htail : WP cfg (fuel + 4) (.next (atCode
      (highStore s op globalIndex memoryIndex sp out source memory) limits stack frame' callers
      (WNear.Binary.ExpectResult.epilogue ++ code))) (4 * op + rest) post := by
    apply hrestore
    simpa only [UInt32.sub_add_cancel, finalStore, frame', afterFrame] using hnext
  have hhigh := wp_copyHigh cfg (fuel + 4) (4 * op + rest)
    (lowStore s op globalIndex memoryIndex sp out source memory) limits stack frame' callers
    (WNear.Binary.ExpectResult.epilogue ++ code) out source mi memoryIndex
    (lowMemory memory out.toNat source.toNat) post hout' hsource' hml hmemoryIndex hmeml
    hsourcePlus houtPlus hbSourceHigh hbOutHigh hl htail
  have hhigh' : WP cfg (fuel + 12) (.next (atCode
      (lowStore s op globalIndex memoryIndex sp out source memory) limits stack frame' callers
      ((WNear.Binary.ExpectResult.copyHigh ++ WNear.Binary.ExpectResult.epilogue) ++ code)))
      (12 * op + rest) post := by
    convert hhigh using 1 <;> first | omega | simp only [List.append_assoc]
  have hlow := wp_copyLow cfg (fuel + 12) (12 * op + rest) (checked s op globalIndex sp)
    limits stack frame' callers ((WNear.Binary.ExpectResult.copyHigh ++ WNear.Binary.ExpectResult.epilogue) ++ code)
    out source mi memoryIndex memory post hout' hsource' hmt hmemoryIndex hmemt hbSourceLow hbLow ht hhigh'
  have hlow' : WP cfg (fuel + 16) (.next (atCode (checked s op globalIndex sp) limits stack frame' callers
      ((WNear.Binary.ExpectResult.copyLow ++ WNear.Binary.ExpectResult.copyHigh ++
        WNear.Binary.ExpectResult.epilogue) ++ code))) (16 * op + rest) post := by
    convert hlow using 1 <;> first | omega | simp only [List.append_assoc]
  have htest := wp_tagCheck cfg (fuel + 16) (16 * op + rest) (reserved s op globalIndex sp)
    limits stack frame' callers ((WNear.Binary.ExpectResult.copyLow ++ WNear.Binary.ExpectResult.copyHigh ++
      WNear.Binary.ExpectResult.epilogue) ++ code) source mi memoryIndex memory post
    hsource' hmr hmemoryIndex hmemr (by omega) htag hr hlow'
  rw [show fuel + 16 + 5 = fuel + 21 by omega,
    show 5 * cfg.regularOpCost + (16 * op + rest) = 21 * op + rest by dsimp [op]; omega] at htest
  have hblock := wp_block_empty cfg (fuel + 21) (21 * op + rest) (reserved s op globalIndex sp)
    limits stack frame' callers (WNear.Binary.ExpectResult.tagCheck ++ WNear.Binary.ExpectResult.panicTail)
    ((WNear.Binary.ExpectResult.copyLow ++ WNear.Binary.ExpectResult.copyHigh ++
      WNear.Binary.ExpectResult.epilogue) ++ code) post (hr.mono (by omega)) htest
  have hentry := wp_prologue cfg (fuel + 22) (21 * op + rest) s limits stack frame callers
    (.block .empty (WNear.Binary.ExpectResult.tagCheck ++ WNear.Binary.ExpectResult.panicTail) ::
      ((WNear.Binary.ExpectResult.copyLow ++ WNear.Binary.ExpectResult.copyHigh ++
        WNear.Binary.ExpectResult.epilogue) ++ code)) mi globalIndex global sp post
    hmodule hglobalIndex hglobal hsp h0 hblock
  convert hentry using 1 <;> first | omega | simp only [WNear.Binary.ExpectResult.body,
    WNear.Binary.ExpectResult.prologue, List.append_assoc, List.cons_append, List.nil_append]

/-- The accepted f158 active frame returns void after twenty-seven body
steps (one free block entry) and one free frame leave. -/
theorem wp_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest)) :
    WP cfg 28 (.next (atCode s limits #[]
      (WNear.Proofs.StorePair.voidFrame #[.i32 out, .i32 source, .i32 location, .i32 0] inst)
      [] WNear.Binary.ExpectResult.body)) (26 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory) ∧
        error = none) := by
  let locals : Array Value := #[.i32 out, .i32 source, .i32 location, .i32 0]
  let frame := WNear.Proofs.StorePair.voidFrame locals inst
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory) ∧
    error = none
  have hg := (finalStore_gas s cfg.regularOpCost globalIndex memoryIndex rest sp out source memory hc).2.2
  have hfinish := WNear.Proofs.StorePair.wp_finish_void cfg 0 rest
    (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory) limits
    (locals.set! 3 (.i32 (sp - 16))) inst post hg ⟨rfl, rfl, rfl⟩
  exact wp_body cfg 1 rest s limits #[] frame [] [] sp out source mi globalIndex memoryIndex
    global memory post rfl rfl (by simp [frame, locals, WNear.Proofs.StorePair.voidFrame]) hmodule hglobalIndex hglobal hsp hmemoryIndex hmemory
    hwf hwidth houtBound hsourceBound htag hc hfinish

/-- Adequacy is an actual normal-return equation for the deployed body, with
no premise asserting successful execution of any instruction or callee. -/
theorem run_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest)) :
    runMetered cfg 28 (.next (atCode s limits #[]
      (WNear.Proofs.StorePair.voidFrame #[.i32 out, .i32 source, .i32 location, .i32 0] inst)
      [] WNear.Binary.ExpectResult.body)) =
      (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  obtain ⟨_, hp, _⟩ :=
    (wp_return cfg rest s limits inst sp out source location mi globalIndex memoryIndex global memory
      hmodule hglobalIndex hglobal hsp hmemoryIndex hmemory hwf hwidth houtBound hsourceBound htag hc).result
  exact Prod.ext hp.2.1 hp.2.2

end WNear.Proofs.ExpectResult
