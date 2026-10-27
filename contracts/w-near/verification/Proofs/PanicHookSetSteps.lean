import Binary.PanicHookSet
import Proofs.ValueReturnLazyReturn
import NearVM.MeteredI32MemoryRules

/-! Small actual instruction capsules for the first panic-hook installation. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

/-- Load a fixed native address and save the word in a local. -/
theorem wp_load_save (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address slot : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      {frame with locals := frame.locals.set! slot (.i32 (readI32 memory address))} callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.i32_const 0, .load .i32 none {align := 2, offset := address}, .local_set slot] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 2, offset := address} 0 mi index memory post hm1 hi hmem1 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  simpa only [paid, UInt32.toNat_zero, Nat.zero_add, List.append_eq, List.cons_append, List.nil_append] using wp_local_set cfg fuel rest (paid s cfg.regularOpCost 2)
    limits stack frame callers code slot (.i32 (readI32 memory address)) post
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext

def stored (s : Store NearState) (op index address : Nat) (memory : Memory) (value : UInt32) :=
  storeI32 (paid s op 3) index address memory value

/-- Store one original local through the actual const0 address operand. -/
theorem wp_store_local (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address slot : Nat) (value : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 value)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory) (hb : address + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (stored s cfg.regularOpCost index address memory value)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.i32_const 0, .local_get slot, .store .i32 none {align := 2, offset := address}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ slot (.i32 value) post hl
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset := address} 0 value mi index memory post hm2 hi hmem2 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · simpa only [stored, paid, UInt32.toNat_zero, Nat.zero_add] using hnext

/-- Store a constant through the same actual three-opcode address sequence. -/
theorem wp_store_const (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address : Nat) (value : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (stored s cfg.regularOpCost index address memory value)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.i32_const 0, .i32_const value, .store .i32 none {align := 2, offset := address}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ value post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset := address} 0 value mi index memory post hm2 hi hmem2 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · simpa only [stored, paid, UInt32.toNat_zero, Nat.zero_add] using hnext

/-- A zero local falls through the actual conditional branch at any depth. -/
theorem wp_local_branch_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot depth : Nat) (post : Post) (hl : frame.locals[slot]? = some (.i32 0))
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers ([.local_get slot, .br_if depth] ++ code)))
      (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ s limits stack frame callers _ slot (.i32 0) post hl (hc.mono (by omega))
  apply wp_br_if_zero cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code depth post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact hnext

/-- A zero fixed memory word exits an empty block, skipping its slow suffix. -/
theorem wp_memory_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (slow code : List Instr) (address : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address + 4 ≤ memory.byteSize)
    (hz : readI32 memory address = 0)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      (.block .empty ([.i32_const 0, .load .i32 none {align := 2, offset := address}, .i32_eqz, .br_if 0] ++ slow) :: code)))
      (4 * cfg.regularOpCost + rest) post := by
  let bf := emptyBlockFrame frame stack.size code
  apply wp_block_empty cfg (fuel + 4) _ s limits stack frame callers _ code post hc
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ s limits stack bf callers _ 0 post (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits stack bf callers _
    {align := 2, offset := address} 0 mi index memory post hm hi hmem (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  simp only [UInt32.toNat_zero, Nat.zero_add, hz]
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits stack bf callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  have rule := wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 3)
    limits stack frame callers code slow 1 post (by decide)
    (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))) hnext
  simpa only [bf, Numeric.bool, beq_self_eq_true, ite_true, paid, List.append_eq, List.cons_append, List.nil_append] using rule

/-- The old-vtable local zero skips the actual destructor block. -/
theorem wp_local_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (slow code : List Instr) (slot : Nat) (post : Post)
    (hz : frame.locals[slot]? = some (.i32 0))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (.block .empty ([.local_get slot, .i32_eqz, .br_if 0] ++ slow) :: code)))
      (3 * cfg.regularOpCost + rest) post := by
  let bf := emptyBlockFrame frame stack.size code
  apply wp_block_empty cfg (fuel + 3) _ s limits stack frame callers _ code post hc
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack bf callers _ slot (.i32 0) post hz (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack bf callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have rule := wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2)
    limits stack frame callers code slow 1 post (by decide)
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext
  simpa only [bf, Numeric.bool, beq_self_eq_true, ite_true, paid, List.append_eq, List.cons_append, List.nil_append] using rule

end WNear.Proofs.PanicHookSet
