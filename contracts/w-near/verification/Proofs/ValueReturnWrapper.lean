import Binary.ValueReturnWrapper
import Proofs.ValueReturnBorrow
import NearVM.MeteredI32MemoryRules

/-! Actual slice preparation around f456 in deployed f545. -/
namespace WNear.Proofs.ValueReturnWrapper
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

def lengthStore (s : Store NearState) (op index : Nat) (scratch length : UInt32) (memory : Memory) : Store NearState :=
  storeI32 (paid s op 3) index (scratch.toNat + 12) memory length

def sliceMemory (memory : Memory) (scratch pointer length : UInt32) : Memory :=
  writeI32 (writeI32 memory (scratch.toNat + 12) length) (scratch.toNat + 8) pointer

def sliceStore (s : Store NearState) (op index : Nat) (scratch pointer length : UInt32) (memory : Memory) : Store NearState :=
  storeI32 (paid (lengthStore s op index scratch length memory) op 3) index (scratch.toNat + 8)
    (writeI32 memory (scratch.toNat + 12) length) pointer

theorem wp_save_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch value : UInt32) (slot offset : Nat) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch)) (hvalue : frame.locals[slot]? = some (.i32 value))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : scratch.toNat + offset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 3) index
      (scratch.toNat + offset) memory value) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get slot, .store .i32 none {align := 2, offset}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (2 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have h1 := paid_credits s cfg.regularOpCost 1 (cfg.regularOpCost + (cfg.regularOpCost + rest)) (hc.mono (by omega))
  have h2 := paid_credits s cfg.regularOpCost 2 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := hmodule
  have hmem : (paid s cfg.regularOpCost 2).mems[index]? = some memory := hmemory
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hscratch h0
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits _ frame callers _ slot (.i32 value) post hvalue h1
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset} scratch value mi index memory post hm hindex hmem hbound h2
  exact hnext

theorem wp_save_slice (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch pointer length : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch)) (hptr : frame.locals[0]? = some (.i32 pointer))
    (hlen : frame.locals[1]? = some (.i32 length))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hspan : scratch.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (sliceStore s cfg.regularOpCost index scratch pointer length memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnWrapper.saveSlice ++ code))) (6 * cfg.regularOpCost + rest) post := by
  let first := lengthStore s cfg.regularOpCost index scratch length memory
  let written := writeI32 memory (scratch.toNat + 12) length
  have hfirst : first.host.gas.Credits (3 * cfg.regularOpCost + rest) := by
    exact paid_credits s cfg.regularOpCost 3 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm : first.modules[frame.inst]? = some mi := hmodule
  have hmem : first.mems[index]? = some written :=
    storeI32_memory (paid s cfg.regularOpCost 3) index (scratch.toNat + 12) memory length hmemory
  have hsize : written.byteSize = memory.byteSize :=
    (writeI32_spec memory (scratch.toNat + 12) length hwf (by omega)).2.1
  have hb : scratch.toNat + 8 + 4 ≤ written.byteSize := by rw [hsize]; omega
  have second := wp_save_word cfg fuel rest first limits stack frame callers code scratch pointer 0 8 mi index written
    post hscratch hptr hm hindex hmem hb hfirst hnext
  have hb0 : scratch.toNat + 12 + 4 ≤ memory.byteSize := by omega
  have hc0 : s.host.gas.Credits (3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have firstRule := wp_save_word cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.local_get 2, .local_get 0, .store .i32 none {align := 2, offset := 8}] ++ code)
    scratch length 1 12 mi index memory post hscratch hlen hmodule hindex hmemory hb0 hc0
  have joined := firstRule second
  have budget : 3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 6 * cfg.regularOpCost + rest := by omega
  rw [budget] at joined
  simpa only [WNear.Binary.ValueReturnWrapper.saveSlice, List.append, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using joined

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 1055020)).push (.i32 (scratch + 8))) frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnWrapper.arguments ++ code))) (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ s limits stack frame callers _ 1055020 post (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 2 (.i32 scratch) post hscratch
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  apply wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 3) limits (stack.push (.i32 1055020)) frame callers code scratch 8 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · exact hnext

theorem sliceStore_memory (s : Store NearState) (op index : Nat) (scratch pointer length : UInt32)
    (memory : Memory) (hmemory : s.mems[index]? = some memory) :
    (sliceStore s op index scratch pointer length memory).mems[index]? = some (sliceMemory memory scratch pointer length) := by
  have first := storeI32_memory (paid s op 3) index (scratch.toNat + 12) memory length hmemory
  have hm : (paid (lengthStore s op index scratch length memory) op 3).mems[index]? =
      some (writeI32 memory (scratch.toNat + 12) length) := first
  exact storeI32_memory _ index (scratch.toNat + 8) _ pointer hm

theorem sliceStore_credits (s : Store NearState) (op index : Nat) (scratch pointer length : UInt32)
    (memory : Memory) (rest : Nat) (hc : s.host.gas.Credits (6 * op + rest)) :
    (sliceStore s op index scratch pointer length memory).host.gas.Credits rest := by
  have hfirst : (lengthStore s op index scratch length memory).host.gas.Credits (3 * op + rest) :=
    paid_credits s op 3 (3 * op + rest) (hc.mono (by omega))
  exact paid_credits (lengthStore s op index scratch length memory) op 3 rest hfirst

end WNear.Proofs.ValueReturnWrapper
