import Binary.StateDecodeSlices
import Proofs.StorePairCallerState
import NearVM.MeteredControlRules
import NearVM.MeteredNumericRules

/-! Accepted unsigned slice split: its real branch skips the panic-only calls. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (drop : Bool) (len split : UInt32) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 len)) (h3 : frame.locals[3]?=some (.i32 split))
    (hn : split.toNat≤len.toNat) (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.StateDecodeSlices.guard++WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855))::code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  have hle : split≤len := by change split.toNat≤len.toNat;exact hn
  have test : Numeric.bool (Numeric.irelop32 .ge_u len split)≠0 := by
    simp [Numeric.irelop32,Numeric.bool,hle]
  have br := wp_br_if_block_nonzero cfg fuel rest (paid s op 3) limits stack frame callers code
    (WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855)) (Numeric.bool (Numeric.irelop32 .ge_u len split)) post test
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 2) limits stack bf callers
    (.br_if 0::WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855)) .ge_u len split post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) br
  have gs := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 len)) bf callers
    (.i32_relop .ge_u::.br_if 0::WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855)) 3 (.i32 split) post h3
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) rel
  have gl := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack bf callers
    (.local_get 3::.i32_relop .ge_u::.br_if 0::WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855)) 2 (.i32 len) post h2
    (hc.mono (by dsimp [op];omega)) gs
  have ce : cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest := by dsimp [op];omega
  have inside : WP cfg (fuel+4) (.next (atCode s limits stack bf callers
      (WNear.Binary.StateDecodeSlices.guard++WNear.Binary.StateDecodeSlices.panic (if drop then 868 else 855))))
      (4*cfg.regularOpCost+rest) post := by
    simpa only [ce,WNear.Binary.StateDecodeSlices.guard,List.cons_append,List.nil_append] using gl
  exact wp_block_empty cfg (fuel+4) _ s limits stack frame callers _ code post hc inside
end WNear.Proofs.StateDecodeSlices
