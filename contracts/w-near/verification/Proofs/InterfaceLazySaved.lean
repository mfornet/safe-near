import Proofs.InterfaceLazyBody
import Proofs.InterfaceSetBody

/-! The lazy initializer saves the old status and payload in its actual scratch
record before deciding whether destruction is required. -/
namespace WNear.Proofs.InterfaceLazySaved
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

def savedHigh (s : Store NearState) (op index : Nat) (scratch oldHigh : UInt32) (memory : Memory) :=
  storeI32 (paid s op 7) index ((scratch + 16) + 12).toNat memory oldHigh

theorem wp_save_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch oldHigh : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hh : frame.locals[4]? = some (.i32 oldHigh))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : ((scratch + 16) + 12).toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (savedHigh s cfg.regularOpCost index scratch oldHigh memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      ([.local_get 2, .i32_const 16, .i32_binop .add, .i32_const 12, .i32_binop .add,
        .local_get 4, .store .i32 none {align := 2, offset := 0}] ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  have hm6 : (paid s cfg.regularOpCost 6).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) (6 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hs
  · exact hc.mono (by omega)
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 5) (5 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits _ frame callers _ 16 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits stack frame callers _ scratch 16 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 3) limits _ frame callers _ 12 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 4) limits stack frame callers _ (scratch + 16) 12 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 5) limits _ frame callers _ 4 (.i32 oldHigh) post hh
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 6) limits stack frame callers code {align := 2, offset := 0} ((scratch + 16) + 12) oldHigh mi index memory post hm6 hi hmem6 hb
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  · exact hnext

def savedLow (s : Store NearState) (op index : Nat) (scratch : UInt32) (oldLow : UInt64) (memory : Memory) :=
  storeI64 (paid s op 3) index (scratch.toNat + 20) memory oldLow

theorem wp_save_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (oldLow : UInt64) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hl : frame.locals[3]? = some (.i64 oldLow))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : scratch.toNat + 28 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (savedLow s cfg.regularOpCost index scratch oldLow memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get 3, .store .i64 none {align := 2, offset := 20}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hs
  · exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits _ frame callers _ 3 (.i64 oldLow) post hl
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code {align := 2, offset := 20} scratch oldLow mi index memory post hm hi hmem (by omega)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

def highMemory (memory : Memory) (scratch oldHigh : UInt32) :=
  writeI32 memory ((scratch + 16) + 12).toNat oldHigh

def statusMemory (memory : Memory) (scratch oldStatus oldHigh : UInt32) :=
  writeI32 (highMemory memory scratch oldHigh) (scratch.toNat + 16) oldStatus

def savedStore (s : Store NearState) (op index : Nat) (scratch oldStatus oldHigh : UInt32)
    (oldLow : UInt64) (memory : Memory) :=
  savedLow (InterfaceSetBody.storeWord (savedHigh s op index scratch oldHigh memory)
    op index 16 scratch oldStatus (highMemory memory scratch oldHigh)) op index scratch oldLow
    (statusMemory memory scratch oldStatus oldHigh)

attribute [local irreducible] savedHigh savedLow highMemory statusMemory

/-- The complete thirteen-instruction save phase in its deployed order. The
three writes remain sequential, so the statement also covers aliasing addresses. -/
theorem wp_save (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch oldStatus oldHigh : UInt32) (oldLow : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hh : frame.locals[4]? = some (.i32 oldHigh))
    (hl : frame.locals[3]? = some (.i64 oldLow)) (hst : frame.locals[1]? = some (.i32 oldStatus))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hb : ((scratch + 16) + 12).toNat + 4 ≤ memory.byteSize)
    (hb2 : scratch.toNat + 20 ≤ (highMemory memory scratch oldHigh).byteSize)
    (hb3 : scratch.toNat + 28 ≤ (statusMemory memory scratch oldStatus oldHigh).byteSize)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (savedStore s cfg.regularOpCost index scratch oldStatus oldHigh oldLow memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.saveOld ++ code))) (13 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let high := savedHigh s op index scratch oldHigh memory
  let status := InterfaceSetBody.storeWord high op index 16 scratch oldStatus (highMemory memory scratch oldHigh)
  have highCredits : high.host.gas.Credits (6 * op + rest) := by
    simpa only [high, savedHigh, storeI32] using paid_credits s op 7 (6 * op + rest) (hc.mono (by dsimp [op]; omega))
  have statusCredits : status.host.gas.Credits (3 * op + rest) :=
    paid_credits high op 3 _ (highCredits.mono (by omega))
  have hmHigh : high.modules[frame.inst]? = some mi := by
    simpa only [high, savedHigh, storeI32_modules, paid, chargedStore] using hm
  have hmStatus : status.modules[frame.inst]? = some mi := by
    simpa only [status, InterfaceSetBody.storeWord, storeI32_modules, paid, chargedStore] using hmHigh
  have hmPaid : (paid s op 7).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have memHigh : high.mems[index]? = some (highMemory memory scratch oldHigh) := by
    simpa only [high, savedHigh, highMemory] using storeI32_memory (paid s op 7) index ((scratch + 16) + 12).toNat memory oldHigh hmPaid
  have hmHighPaid : (paid high op 3).mems[index]? = some (highMemory memory scratch oldHigh) := by simpa only [paid, chargedStore] using memHigh
  have memStatus : status.mems[index]? = some (statusMemory memory scratch oldStatus oldHigh) := by
    simpa only [status, InterfaceSetBody.storeWord, statusMemory] using storeI32_memory (paid high op 3) index (scratch.toNat + 16) (highMemory memory scratch oldHigh) oldStatus hmHighPaid
  have low := wp_save_low cfg fuel rest status limits stack frame callers code scratch oldLow mi index
    (statusMemory memory scratch oldStatus oldHigh) post hs hl hmStatus hi memStatus hb3 statusCredits hnext
  have hmidCredits : high.host.gas.Credits (3 * cfg.regularOpCost + (3 * op + rest)) := by
    simpa only [op, show 3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 6 * cfg.regularOpCost + rest by omega] using highCredits
  have middle := InterfaceSetBody.wp_store_word cfg (fuel + 3) (3 * op + rest) high limits stack frame callers
    ([.local_get 2, .local_get 3, .store .i64 none {align := 2, offset := 20}] ++ code)
    2 1 16 scratch oldStatus mi index (highMemory memory scratch oldHigh) post hs hst hmHigh hi memHigh hb2
    hmidCredits
  have low' : WP cfg (fuel + 3) (.next (atCode
      (InterfaceSetBody.storeWord high cfg.regularOpCost index 16 scratch oldStatus (highMemory memory scratch oldHigh))
      limits stack frame callers ([.local_get 2, .local_get 3, .store .i64 none {align := 2, offset := 20}] ++ code)))
      (3 * op + rest) post := by
    simpa only [status, op] using low
  have middleDone := middle low'
  have next : WP cfg (fuel + 6) (.next (atCode high limits stack frame callers
      ([.local_get 2, .local_get 1, .store .i32 none {align := 2, offset := 16},
        .local_get 2, .local_get 3, .store .i64 none {align := 2, offset := 20}] ++ code))) (6 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append,
      show 3 * cfg.regularOpCost + (3 * op + rest) = 6 * op + rest by dsimp [op]; omega] using middleDone
  have result := wp_save_high cfg (fuel + 6) (6 * op + rest) s limits stack frame callers _ scratch oldHigh mi index memory post
    hs hh hm hi hmem hb (hc.mono (by dsimp [op]; omega)) next
  have gas : 7 * cfg.regularOpCost + (6 * op + rest) = 13 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, WNear.Binary.InterfaceLazy.saveOld,
    List.cons_append, List.nil_append] using result

end WNear.Proofs.InterfaceLazySaved
