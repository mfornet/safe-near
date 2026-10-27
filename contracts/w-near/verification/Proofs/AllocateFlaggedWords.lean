import Binary.AllocateFlagged
import Proofs.AllocateFlaggedState
import Proofs.AllocateFlaggedBranch
import Proofs.AllocateControlWords

/-! The actual flags-two old-header clear and new-header flag write. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def clearStore (s : Store NearState) (op index : Nat) (memory : Memory) (head word : UInt32) :=
  storeI32 (paid s op 5) index head.toNat memory (word &&& 4294967293)
def flagStore (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :=
  storeI32 (paid s op 6) index header.toNat memory (readI32 memory header.toNat ||| 2)

theorem wp_mark_new (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (header : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[9]? = some (.i32 header)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : header.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (flagStore s cfg.regularOpCost index memory header)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateFlagged.markNew ++ code))) (6 * cfg.regularOpCost + rest) post := by
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
  apply wp_i32_const cfg (fuel+2) _ (paid s op 3) limits _ frame callers _ 2 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_or cfg (fuel+1) _ (paid s op 4) limits (stack.push (.i32 header)) frame callers _ (readI32 memory header.toNat) 2 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 5) limits stack frame callers code
    {align:=2,offset:=0} header (readI32 memory header.toNat ||| 2) mi index memory post hm5 hi hmem5 (by simpa using hb)
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext


theorem wp_clear_old (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head word : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hh : frame.locals[1]?=some (.i32 head)) (hw : frame.locals[2]?=some (.i32 word))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : head.toNat+4≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (clearStore s cfg.regularOpCost index memory head word) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateFlagged.clearOld++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have hm4 : (paid s op 4).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have mem4 : (paid s op 4).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ s limits stack frame callers _ 1 (.i32 head) post hh (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ (paid s op 1) limits (stack.push (.i32 head)) frame callers _ 2 (.i32 word) post hw
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 2) limits _ frame callers _ 4294967293 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+1) _ (paid s op 3) limits (stack.push (.i32 head)) frame callers _ word 4294967293 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid s op 4) limits stack frame callers code {align:=2,offset:=0}
    head (word &&& 4294967293) mi index memory post hm4 hi mem4 (by simpa only [Nat.add_zero] using hb)
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [clearStore,paid,op,Nat.add_zero] using hnext
end WNear.Proofs.AllocateFlagged
