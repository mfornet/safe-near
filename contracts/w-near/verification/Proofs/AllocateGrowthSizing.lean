import Binary.AllocateGrowth
import NearVM.MeteredBitRules
import NearVM.MeteredLoopRules
import NearVM.MeteredSelectionRules
import Proofs.StorePairCallerState

/-! Actual original-data sizing guards and maximum calculation of f577. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def alignPlus (alignment : UInt32) := alignment+64
def scaledAlign (alignment : UInt32) := alignPlus alignment <<< (3 : UInt32)
def chosenSize (units alignment : UInt32) :=
  if Numeric.bool (Numeric.irelop32 .gt_u units (scaledAlign alignment))≠0 then units else scaledAlign alignment
def paddedSize (units alignment : UInt32) := chosenSize units alignment+8
def alignFrame (frame : CallFrame) (alignment : UInt32) := {frame with locals:=frame.locals.set! 2 (.i32 (alignPlus alignment))}
def scaledFrame (frame : CallFrame) (alignment : UInt32) := {alignFrame frame alignment with locals:=(alignFrame frame alignment).locals.set! 2 (.i32 (scaledAlign alignment))}
def chosenFrame (frame : CallFrame) (units alignment : UInt32) := {scaledFrame frame alignment with locals:=(scaledFrame frame alignment).locals.set! 2 (.i32 (chosenSize units alignment))}
def sizingFrame (frame : CallFrame) (units alignment : UInt32) := {chosenFrame frame units alignment with locals:=(chosenFrame frame units alignment).locals.set! 3 (.i32 (paddedSize units alignment))}

theorem wp_sizing (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (units alignment : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 alignment)) (h4 : frame.locals[4]?=some (.i32 units)) (hs : 5≤frame.locals.size)
    (hadd : Numeric.irelop32 .lt_u (alignPlus alignment) alignment=false)
    (hmask : alignPlus alignment &&& 536870911=alignPlus alignment)
    (hpad : Numeric.irelop32 .lt_u (paddedSize units alignment) (chosenSize units alignment)=false)
    (hc : s.host.gas.Credits (29*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 29) limits stack (sizingFrame frame units alignment) callers code)) rest post) :
    WP cfg (fuel+29) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateGrowth.sizing++code)))
      (29*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have h2 : 2<frame.locals.size := by omega
  have h3size : 3<frame.locals.size := by omega
  unfold WNear.Binary.AllocateGrowth.sizing
  simp only [List.cons_append,List.nil_append]
  rw [show 29*op+rest=cfg.regularOpCost+(28*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+28) (28*op+rest) s limits stack (frame) callers _ 3 (.i32 (alignment)) post (by simpa [alignFrame,scaledFrame,chosenFrame,sizingFrame] using h3)
  · exact hc.mono (by dsimp [op];omega)
  rw [show 28*op+rest=cfg.regularOpCost+(27*op+rest) by dsimp [op];omega]
  apply wp_i32_const cfg (fuel+27) (27*op+rest) (paid s op 1) limits (stack.push (.i32 (alignment))) (frame) callers _ 64 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))
  rw [show 27*op+rest=cfg.regularOpCost+(26*op+rest) by dsimp [op];omega]
  apply wp_i32_add cfg (fuel+26) (26*op+rest) (paid s op 2) limits stack (frame) callers _ (alignment) (64) post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))
  rw [show 26*op+rest=cfg.regularOpCost+(25*op+rest) by dsimp [op];omega]
  apply wp_local_tee cfg (fuel+25) (25*op+rest) (paid s op 3) limits stack (frame) callers _ 2 (.i32 (alignPlus alignment)) post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  rw [show 25*op+rest=cfg.regularOpCost+(24*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+24) (24*op+rest) (paid s op 4) limits (stack.push (.i32 (alignPlus alignment))) (alignFrame frame alignment) callers _ 3 (.i32 (alignment)) post (by simpa [alignFrame,scaledFrame,chosenFrame,sizingFrame] using h3)
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))
  rw [show 24*op+rest=cfg.regularOpCost+(23*op+rest) by dsimp [op];omega]
  apply wp_i32_relop cfg (fuel+23) (23*op+rest) (paid s op 5) limits stack (alignFrame frame alignment) callers _ .lt_u (alignPlus alignment) (alignment) post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))
  rw [show 23*op+rest=cfg.regularOpCost+(22*op+rest) by dsimp [op];omega]
  simp only [hadd,Numeric.bool,Bool.false_eq_true,ite_false]
  apply wp_br_if_zero cfg (fuel+22) (22*op+rest) (paid s op 6) limits stack (alignFrame frame alignment) callers _ 0 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))
  rw [show 22*op+rest=cfg.regularOpCost+(21*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+21) (21*op+rest) (paid s op 7) limits stack (alignFrame frame alignment) callers _ 2 (.i32 (alignPlus alignment)) post (by simp only [alignFrame]; simp [h2])
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))
  rw [show 21*op+rest=cfg.regularOpCost+(20*op+rest) by dsimp [op];omega]
  apply wp_i32_const cfg (fuel+20) (20*op+rest) (paid s op 8) limits (stack.push (.i32 (alignPlus alignment))) (alignFrame frame alignment) callers _ 536870911 post
  · exact paid_credits s op 8 _ (hc.mono (by dsimp [op];omega))
  rw [show 20*op+rest=cfg.regularOpCost+(19*op+rest) by dsimp [op];omega]
  apply wp_i32_and cfg (fuel+19) (19*op+rest) (paid s op 9) limits stack (alignFrame frame alignment) callers _ (alignPlus alignment) (536870911) post
  · exact paid_credits s op 9 _ (hc.mono (by dsimp [op];omega))
  rw [show 19*op+rest=cfg.regularOpCost+(18*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+18) (18*op+rest) (paid s op 10) limits (stack.push (.i32 (alignPlus alignment &&& 536870911))) (alignFrame frame alignment) callers _ 2 (.i32 (alignPlus alignment)) post (by simp only [alignFrame]; simp [h2])
  · exact paid_credits s op 10 _ (hc.mono (by dsimp [op];omega))
  rw [show 18*op+rest=cfg.regularOpCost+(17*op+rest) by dsimp [op];omega]
  apply wp_i32_relop cfg (fuel+17) (17*op+rest) (paid s op 11) limits stack (alignFrame frame alignment) callers _ .ne (alignPlus alignment &&& 536870911) (alignPlus alignment) post
  · exact paid_credits s op 11 _ (hc.mono (by dsimp [op];omega))
  rw [show 17*op+rest=cfg.regularOpCost+(16*op+rest) by dsimp [op];omega]
  simp only [hmask,Numeric.irelop32,Numeric.bool,bne_self_eq_false]
  apply wp_br_if_zero cfg (fuel+16) (16*op+rest) (paid s op 12) limits stack (alignFrame frame alignment) callers _ 1 post
  · exact paid_credits s op 12 _ (hc.mono (by dsimp [op];omega))
  rw [show 16*op+rest=cfg.regularOpCost+(15*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+15) (15*op+rest) (paid s op 13) limits stack (alignFrame frame alignment) callers _ 4 (.i32 (units)) post (by simpa [alignFrame,scaledFrame,chosenFrame,sizingFrame] using h4)
  · exact paid_credits s op 13 _ (hc.mono (by dsimp [op];omega))
  rw [show 15*op+rest=cfg.regularOpCost+(14*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+14) (14*op+rest) (paid s op 14) limits (stack.push (.i32 (units))) (alignFrame frame alignment) callers _ 2 (.i32 (alignPlus alignment)) post (by simp only [alignFrame]; simp [h2])
  · exact paid_credits s op 14 _ (hc.mono (by dsimp [op];omega))
  rw [show 14*op+rest=cfg.regularOpCost+(13*op+rest) by dsimp [op];omega]
  apply wp_i32_const cfg (fuel+13) (13*op+rest) (paid s op 15) limits ((stack.push (.i32 (units))).push (.i32 (alignPlus alignment))) (alignFrame frame alignment) callers _ 3 post
  · exact paid_credits s op 15 _ (hc.mono (by dsimp [op];omega))
  rw [show 13*op+rest=cfg.regularOpCost+(12*op+rest) by dsimp [op];omega]
  apply wp_i32_binop_ok cfg (fuel+12) (12*op+rest) (paid s op 16) limits (stack.push (.i32 (units))) (alignFrame frame alignment) callers _ .shl (alignPlus alignment) (3) (scaledAlign alignment) post rfl
  · exact paid_credits s op 16 _ (hc.mono (by dsimp [op];omega))
  rw [show 12*op+rest=cfg.regularOpCost+(11*op+rest) by dsimp [op];omega]
  apply wp_local_tee cfg (fuel+11) (11*op+rest) (paid s op 17) limits (stack.push (.i32 (units))) (alignFrame frame alignment) callers _ 2 (.i32 (scaledAlign alignment)) post
  · exact paid_credits s op 17 _ (hc.mono (by dsimp [op];omega))
  rw [show 11*op+rest=cfg.regularOpCost+(10*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+10) (10*op+rest) (paid s op 18) limits ((stack.push (.i32 (units))).push (.i32 (scaledAlign alignment))) (scaledFrame frame alignment) callers _ 4 (.i32 (units)) post (by simpa [alignFrame,scaledFrame,chosenFrame,sizingFrame] using h4)
  · exact paid_credits s op 18 _ (hc.mono (by dsimp [op];omega))
  rw [show 10*op+rest=cfg.regularOpCost+(9*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+9) (9*op+rest) (paid s op 19) limits (((stack.push (.i32 (units))).push (.i32 (scaledAlign alignment))).push (.i32 (units))) (scaledFrame frame alignment) callers _ 2 (.i32 (scaledAlign alignment)) post (by simp only [scaledFrame,alignFrame]; simp [h2])
  · exact paid_credits s op 19 _ (hc.mono (by dsimp [op];omega))
  rw [show 9*op+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op];omega]
  apply wp_i32_relop cfg (fuel+8) (8*op+rest) (paid s op 20) limits ((stack.push (.i32 (units))).push (.i32 (scaledAlign alignment))) (scaledFrame frame alignment) callers _ .gt_u (units) (scaledAlign alignment) post
  · exact paid_credits s op 20 _ (hc.mono (by dsimp [op];omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op];omega]
  apply wp_select cfg (fuel+7) (7*op+rest) (paid s op 21) limits stack (scaledFrame frame alignment) callers _ (.i32 (units)) (.i32 (scaledAlign alignment)) (Numeric.bool (Numeric.irelop32 .gt_u (units) (scaledAlign alignment))) post
  · exact paid_credits s op 21 _ (hc.mono (by dsimp [op];omega))
  rw [show (if Numeric.bool (Numeric.irelop32 .gt_u units (scaledAlign alignment))≠0 then Value.i32 units else Value.i32 (scaledAlign alignment))=Value.i32 (chosenSize units alignment) by unfold chosenSize; split <;> rfl]
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op];omega]
  apply wp_local_tee cfg (fuel+6) (6*op+rest) (paid s op 22) limits stack (scaledFrame frame alignment) callers _ 2 (.i32 (chosenSize units alignment)) post
  · exact paid_credits s op 22 _ (hc.mono (by dsimp [op];omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op];omega]
  apply wp_i32_const cfg (fuel+5) (5*op+rest) (paid s op 23) limits (stack.push (.i32 (chosenSize units alignment))) (chosenFrame frame units alignment) callers _ 8 post
  · exact paid_credits s op 23 _ (hc.mono (by dsimp [op];omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op];omega]
  apply wp_i32_add cfg (fuel+4) (4*op+rest) (paid s op 24) limits stack (chosenFrame frame units alignment) callers _ (chosenSize units alignment) (8) post
  · exact paid_credits s op 24 _ (hc.mono (by dsimp [op];omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op];omega]
  apply wp_local_tee cfg (fuel+3) (3*op+rest) (paid s op 25) limits stack (chosenFrame frame units alignment) callers _ 3 (.i32 (paddedSize units alignment)) post
  · exact paid_credits s op 25 _ (hc.mono (by dsimp [op];omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+2) (2*op+rest) (paid s op 26) limits (stack.push (.i32 (paddedSize units alignment))) (sizingFrame frame units alignment) callers _ 2 (.i32 (chosenSize units alignment)) post (by simp only [sizingFrame,chosenFrame,scaledFrame,alignFrame]; simp [h2])
  · exact paid_credits s op 26 _ (hc.mono (by dsimp [op];omega))
  rw [show 2*op+rest=cfg.regularOpCost+(1*op+rest) by dsimp [op];omega]
  apply wp_i32_relop cfg (fuel+1) (1*op+rest) (paid s op 27) limits stack (sizingFrame frame units alignment) callers _ .lt_u (paddedSize units alignment) (chosenSize units alignment) post
  · exact paid_credits s op 27 _ (hc.mono (by dsimp [op];omega))
  rw [show 1*op+rest=cfg.regularOpCost+rest by dsimp [op];omega]
  simp only [hpad,Numeric.bool,Bool.false_eq_true,ite_false]
  apply wp_br_if_zero cfg fuel rest (paid s op 28) limits stack (sizingFrame frame units alignment) callers _ 2 post
  · exact paid_credits s op 28 _ (hc.mono (by dsimp [op];omega))
  simpa only [paid,op,alignFrame,scaledFrame,chosenFrame,sizingFrame] using hnext
end WNear.Proofs.AllocateGrowth
