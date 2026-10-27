import NearVM.MeteredBitRules
import NearVM.MeteredI32MemoryRules
import Proofs.StorePairCaller
import Proofs.ValueReturnBorrow
import Proofs.PanicAllocateReadback

/-! Exact sequential low-bit clearing at the end of the deployed unlink helper. -/
namespace WNear.Proofs.DeallocateMaskStore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def maskStore (s : Store NearState) (op index : Nat) (memory : Memory)
    (pointer value mask : UInt32) (offset : Nat) :=
  storeI32 (paid s op 3) index (pointer.toNat + offset) memory (value &&& mask)

/-- A small pre-store capsule prevents unfolding earlier heap writes. -/
theorem wp_mask_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer value mask : UInt32) (offset : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + offset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (maskStore s cfg.regularOpCost index memory pointer value mask offset)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits ((stack.push (.i32 pointer)).push (.i32 value)) frame callers
      ([.i32_const mask, .i32_binop .and, .store .i32 none {align := 2, offset}] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits _ frame callers _ mask post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_and cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ value mask post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have mem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have rule := wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset} pointer (value &&& mask) mi index memory post hm2 hi mem2 hb
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega)))
  have next : WP cfg fuel (.next (atCode (storeI32 (chargedStore (paid s cfg.regularOpCost 2) cfg.regularOpCost)
      index (pointer.toNat + offset) memory (value &&& mask)) limits stack frame callers code)) rest post := by
    simpa only [maskStore, paid] using hnext
  have result := rule next
  simpa only [paid, List.append_eq, List.cons_append, List.nil_append] using result

end WNear.Proofs.DeallocateMaskStore
