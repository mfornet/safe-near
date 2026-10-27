import Binary.StateRead
import Proofs.StorePairCaller
import Proofs.ValueReturnBorrow
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredControlRules

/-! Actual guard and sequential copy capsules for deployed f498. -/
namespace WNear.Proofs.StateReadResult
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64

def lowMemory (memory : Memory) (out source : UInt32) := writeI64 memory out.toNat (readI64 memory source.toNat)
def finalMemory (memory : Memory) (out source : UInt32) :=
  writeI32 (lowMemory memory out source) (out + 8).toNat (readI32 (lowMemory memory out source) (source + 8).toNat)
def lowStore (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI64 (paid s op 4) index out.toNat memory (readI64 memory source.toNat)
def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI32 (paid s op 8) index (out + 8).toNat memory (readI32 memory (source + 8).toNat)
def after (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  highStore (lowStore (paid s op 3) op index memory out source) op index (lowMemory memory out source) out source

/-- A present result tag skips the actual panic suffix through its real load. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[1]? = some (.i32 source)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : source.toNat + 4 ≤ memory.byteSize) (htag : readI32 memory source.toNat ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.StateRead.resultGuard ++ WNear.Binary.StateRead.resultPanic) :: code)))
      (3 * cfg.regularOpCost + rest) post := by
  let bf := emptyBlockFrame frame stack.size code
  apply wp_block_empty cfg (fuel + 3) _ s limits stack frame callers _ code post hc
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack bf callers _ 1 (.i32 source) post hs (hc.mono (by omega))
  have hm1 : (paid s cfg.regularOpCost 1).modules[bf.inst]? = some mi := by simpa only [paid,chargedStore,bf,emptyBlockFrame] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack bf callers _
    {align := 2,offset := 0} source mi index memory post hm1 hi m1 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have r := wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    WNear.Binary.StateRead.resultPanic (readI32 memory source.toNat) post htag
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext
  simpa only [bf,paid,Nat.add_zero,List.append_eq,List.cons_append,List.nil_append] using r

/-- The low eight bytes are loaded before the first output write. -/
theorem wp_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hob : out.toNat + 8 ≤ memory.byteSize) (hsb : source.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers (WNear.Binary.StateRead.resultLow ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 0 (.i32 out) post ho (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1 (.i32 source) post hs
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits (stack.push (.i32 out)) frame callers _
    {align := 2,offset := 0} source mi index memory post hm2 hi m2 (by simpa using hsb)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (storeI64 (chargedStore (paid s cfg.regularOpCost 3) cfg.regularOpCost) index
      (out.toNat + 0) memory (readI64 memory source.toNat)) limits stack frame callers code)) rest post := by
    simpa only [lowStore,paid,Nat.add_zero] using hnext
  have r := wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 2,offset := 0} out (readI64 memory source.toNat) mi index memory post hm3 hi m3 (by simpa using hob)
    (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))) hn
  simpa only [paid,Nat.add_zero,List.append_eq,List.cons_append,List.nil_append] using r

/-- Calculate both actual wrapping addresses without touching linear memory. -/
theorem wp_high_addresses (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((stack.push (.i32 (out + 8))).push (.i32 (source + 8))) frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 0,.i32_const 8,.i32_binop .add,.local_get 1,.i32_const 8,.i32_binop .add] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack frame callers _ 0 (.i32 out) post ho (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 3) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ out 8 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 1 (.i32 source) post hs
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 4) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  have r := wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 5) limits (stack.push (.i32 (out + 8))) frame callers code source 8 post
    (paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))) hnext
  simpa only [paid,List.append_eq,List.cons_append,List.nil_append] using r

def copyWordStore (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  storeI32 (paid s op 2) index out.toNat memory (readI32 memory source.toNat)

/-- The last read observes the memory after the preceding i64 write. -/
theorem wp_copy_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hob : out.toNat + 4 ≤ memory.byteSize) (hsb : source.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copyWordStore s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits ((stack.push (.i32 out)).push (.i32 source)) frame callers
      ([.load .i32 none {align := 2,offset := 0},.store .i32 none {align := 2,offset := 0}] ++ code)))
      (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ s limits (stack.push (.i32 out)) frame callers _
    {align := 2,offset := 0} source mi index memory post hm hi hmem (by simpa using hsb) (hc.mono (by omega))
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (storeI32 (chargedStore (paid s cfg.regularOpCost 1) cfg.regularOpCost) index
      (out.toNat + 0) memory (readI32 memory source.toNat)) limits stack frame callers code)) rest post := by
    simpa only [copyWordStore,paid,Nat.add_zero] using hnext
  have r := wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code
    {align := 2,offset := 0} out (readI32 memory source.toNat) mi index memory post hm1 hi m1 (by simpa using hob)
    (paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))) hn
  simpa only [paid,Nat.add_zero,List.append_eq,List.cons_append,List.nil_append] using r

/-- All eight actual high-word instructions, with no non-aliasing premise. -/
theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hob : (out + 8).toNat + 4 ≤ memory.byteSize) (hsb : (source + 8).toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers (WNear.Binary.StateRead.resultHigh ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  have hm6 : (paid s cfg.regularOpCost 6).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have m6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hn : WP cfg fuel (.next (atCode (copyWordStore (paid s cfg.regularOpCost 6) cfg.regularOpCost index memory (out + 8) (source + 8))
      limits stack frame callers code)) rest post := by
    simpa only [copyWordStore,highStore,ValueReturnBorrow.paid_add] using hnext
  have tail := wp_copy_word cfg fuel rest (paid s cfg.regularOpCost 6) limits stack frame callers code (out + 8) (source + 8) mi index memory post hm6 hi m6 hob hsb
    (paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))) hn
  have r := wp_high_addresses cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack frame callers _ out source post ho hs (hc.mono (by omega)) tail
  simpa only [WNear.Binary.StateRead.resultHigh,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (2 * cfg.regularOpCost + rest) = 8 * cfg.regularOpCost + rest by omega] using r

end WNear.Proofs.StateReadResult
