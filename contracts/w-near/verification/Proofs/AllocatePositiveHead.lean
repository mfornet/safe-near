import Proofs.AllocatePositiveState

/-! The actual post-search allocator-head write reads the sequential final heap. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def updateFrom (s : Store NearState) (op index : Nat) (memory : Memory) (allocator scratch : UInt32) :=
  storeI32 (paid s op 4) index allocator.toNat memory (readI32 memory (scratch.toNat+12))

theorem wp_update_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (allocator scratch : UInt32) (post : Post)
    (ha : frame.locals[0]?=some (.i32 allocator)) (hs : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : allocator.toNat+4≤memory.byteSize) (hw : scratch.toNat+16≤memory.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (updateFrom s cfg.regularOpCost index memory allocator scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.AllocatePositive.updateHead++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have hm3 : (paid s op 3).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have mm2 : (paid s op 2).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have mm3 : (paid s op 3).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  unfold WNear.Binary.AllocatePositive.updateHead
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 0 (.i32 allocator) post ha (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+2) _ (paid s op 1) limits _ frame callers _ 3 (.i32 scratch) post hs
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+1) _ (paid s op 2) limits (stack.push (.i32 allocator)) frame callers _
    {align:=2,offset:=12} scratch mi index memory post hm2 hi mm2 (by change scratch.toNat+12+4≤memory.byteSize; omega)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=2,offset:=0}
    allocator (readI32 memory (scratch.toNat+12)) mi index memory post hm3 hi mm3 (by simpa only [Nat.add_zero] using hb)
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [updateFrom,paid,op,Nat.add_zero] using hnext
end WNear.Proofs.AllocatePositive
