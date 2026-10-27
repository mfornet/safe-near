import NearVM.MeteredI32MemoryRules
import Binary.Allocate
import Proofs.StorePairCallerState
import Proofs.StorePairAddresses
import NearVM.MeteredBitRules

/-! The actual final allocation commit in f580: set the in-use bit and expose
header+8. These rules preserve arbitrary operands, frames and continuations. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def markedMemory (memory : Memory) (header : UInt32) :=
  writeI32 memory header.toNat (readI32 memory header.toNat ||| 1)
def markedStore (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :=
  storeI32 (paid s op 6) index header.toNat memory (readI32 memory header.toNat ||| 1)
def resultFrame (frame : CallFrame) (header : UInt32) :=
  {frame with locals := frame.locals.set! 5 (.i32 (header + 8))}
def committed (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :=
  paid (markedStore s op index memory header) op 4

/-- The deployed six-instruction allocation mark writes the actual header word. -/
theorem wp_mark (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : header.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (markedStore s cfg.regularOpCost index memory header)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      (WNear.Binary.Allocate.markAllocated ++ code))) (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hm5 : (paid s op 5).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ s limits stack frame callers _ 9 (.i32 header) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 1) limits _ frame callers _ 9 (.i32 header) post hl
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+3) _ (paid s op 2) limits (stack.push (.i32 header)) frame callers _
    {align:=2,offset:=0} header mi index memory post hm2 hi hmem2 (by simpa using hb)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 3) limits _ frame callers _ 1 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_or cfg (fuel+1) _ (paid s op 4) limits (stack.push (.i32 header)) frame callers _ (readI32 memory header.toNat) 1 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 5) limits stack frame callers code
    {align:=2,offset:=0} header (readI32 memory header.toNat ||| 1) mi index memory post hm5 hi hmem5 (by simpa using hb)
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- The actual pointer calculation follows the mark without any memory read. -/
theorem wp_result_pointer (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (header : UInt32) (post : Post) (hl : frame.locals[9]? = some (.i32 header))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack (resultFrame frame header) callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      (WNear.Binary.Allocate.resultPointer ++ code))) (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 9 (.i32 header) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 1) limits _ frame callers _ 8 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel+1) _ (paid s op 2) limits stack frame callers _ header 8 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  apply wp_local_set cfg fuel rest (paid s op 3) limits stack frame callers code 5 (.i32 (header+8)) post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- Complete actual ten-opcode commit, assuming only the original header span. -/
theorem wp_commit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : header.toNat+4 ≤ memory.byteSize) (hc : s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (committed s cfg.regularOpCost index memory header)
      limits stack (resultFrame frame header) callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.commit ++ code)))
      (10*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have cm : (markedStore s op index memory header).host.gas.Credits (4*op+rest) := by
    unfold markedStore
    rw [storeI32_host]
    exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  have tail := wp_result_pointer cfg fuel rest (markedStore s op index memory header) limits stack frame callers code header post hl cm hnext
  have head := wp_mark cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (WNear.Binary.Allocate.resultPointer ++ code) header mi index memory post hl hm hi hmem hb
    (hc.mono (by dsimp [op]; omega)) tail
  have cost : 6*cfg.regularOpCost+(4*op+rest)=10*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at head
  simpa only [WNear.Binary.Allocate.commit,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using head

theorem committed_memory (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32)
    (hm : s.mems[index]? = some memory) :
    (committed s op index memory header).mems[index]? = some (markedMemory memory header) := by
  have hm6 : (paid s op 6).mems[index]? = some memory := by simpa only [paid,chargedStore] using hm
  have h := storeI32_memory (paid s op 6) index header.toNat memory (readI32 memory header.toNat ||| 1) hm6
  change (markedStore s op index memory header).mems[index]? = some (markedMemory memory header)
  exact h

theorem committed_resources (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    {committed s op index memory header with host := s.host,mems := s.mems} = s := by
  cases s
  rfl

theorem committed_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (header : UInt32)
    (hc : s.host.gas.Credits (10*op+rest)) :
    (committed s op index memory header).host.gas.Credits rest := by
  have cm : (markedStore s op index memory header).host.gas.Credits (4*op+rest) := by
    unfold markedStore
    rw [storeI32_host]
    exact paid_credits s op 6 _ (hc.mono (by omega))
  exact paid_credits (markedStore s op index memory header) op 4 rest cm
end WNear.Proofs.Allocate
