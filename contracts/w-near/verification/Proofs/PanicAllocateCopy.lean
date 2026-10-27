import Binary.PanicAllocate
import Proofs.InterfaceSetBody
import Proofs.ValueReturnOuterBody

/-! Scalar memory-copy capsules used by the actual allocation wrappers. -/
namespace WNear.Proofs.PanicAllocateCopy
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
attribute [local irreducible] WP readI32 writeI32

def copyStore (s : Store NearState) (op index sourceOffset targetOffset : Nat)
    (source target : UInt32) (memory : Memory) :=
  storeI32 (paid s op 4) index (target.toNat + targetOffset) memory (readI32 memory (source.toNat + sourceOffset))

/-- Four real instructions, preserving their arbitrary sequential aliasing. -/
theorem wp_copy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sourceSlot targetSlot sourceOffset targetOffset : Nat)
    (source target : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[sourceSlot]? = some (.i32 source)) (ht : frame.locals[targetSlot]? = some (.i32 target))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hbS : source.toNat + sourceOffset + 4 ≤ memory.byteSize)
    (hbT : target.toNat + targetOffset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copyStore s cfg.regularOpCost index sourceOffset targetOffset source target memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get targetSlot, .local_get sourceSlot, .load .i32 none {align := 2, offset := sourceOffset},
        .store .i32 none {align := 2, offset := targetOffset}] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm3 : (paid s op 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem3 : (paid s op 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have storeRule := wp_i32_store cfg fuel rest (paid s op 3) limits stack frame callers code
    {align := 2, offset := targetOffset} target (readI32 memory (source.toNat + sourceOffset)) mi index memory post
    hm3 hi hmem3 hbT (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega)))
  have storeNext : WP cfg fuel (.next (atCode
      (storeI32 (chargedStore (paid s op 3) op) index (target.toNat + targetOffset) memory
        (readI32 memory (source.toNat + sourceOffset))) limits stack frame callers code)) rest post := hnext
  have storing := storeRule storeNext
  have loadRule := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 2) limits (stack.push (.i32 target)) frame callers
    (.store .i32 none {align := 2, offset := targetOffset} :: code) {align := 2, offset := sourceOffset} source mi index memory post
    hm2 hi hmem2 hbS (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) storing
  have hsrc := wp_local_get cfg (fuel + 2) (op + (op + rest)) (paid s op 1) limits (stack.push (.i32 target)) frame callers
    (.load .i32 none {align := 2, offset := sourceOffset} :: .store .i32 none {align := 2, offset := targetOffset} :: code)
    sourceSlot (.i32 source) post hs (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) loadRule
  have result := wp_local_get cfg (fuel + 3) (op + (op + (op + rest))) s limits stack frame callers
    (.local_get sourceSlot :: .load .i32 none {align := 2, offset := sourceOffset} ::
      .store .i32 none {align := 2, offset := targetOffset} :: code) targetSlot (.i32 target) post ht
    (hc.mono (by dsimp [op]; omega)) hsrc
  have ge : cfg.regularOpCost + (op + (op + (op + rest))) = 4 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post rfl ge rfl result

theorem copyStore_credits (s : Store NearState) (op index sourceOffset targetOffset rest : Nat)
    (source target : UInt32) (memory : Memory) (hc : s.host.gas.Credits (4 * op + rest)) :
    (copyStore s op index sourceOffset targetOffset source target memory).host.gas.Credits rest :=
  paid_credits s op 4 rest hc

end WNear.Proofs.PanicAllocateCopy
