import Proofs.SerializeMultiplyState

/-! Actual f954 low-word arithmetic and first store, from arbitrary typed operands. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64

theorem wp_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (w : Words) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 w.out)) (h1 : frame.locals[1]?=some (.i64 w.aLo))
    (h3 : frame.locals[3]?=some (.i64 w.bLo)) (hs : 12 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hb : w.out.toNat+8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (31*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory w) limits stack (finalFrame frame w) callers code)) rest post) :
    WP cfg (fuel+31) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeMultiply.low++code)))
      (31*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have bounds : 5 < frame.locals.size ∧ 6 < frame.locals.size ∧ 7 < frame.locals.size ∧ 8 < frame.locals.size ∧ 9 < frame.locals.size ∧ 10 < frame.locals.size ∧ 11 < frame.locals.size := by omega
  unfold WNear.Binary.SerializeMultiply.low
  rw [show 31*cfg.regularOpCost+rest=cfg.regularOpCost+(30*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+30) _ s limits _ frame callers _ 0 (.i32 (w.out)) post (by simp [h0])
  · exact hc.mono (by omega)
  rw [show 30*cfg.regularOpCost+rest=cfg.regularOpCost+(29*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+29) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 3 (.i64 (w.bLo)) post (by simp [h3])
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 29*cfg.regularOpCost+rest=cfg.regularOpCost+(28*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+28) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 28*cfg.regularOpCost+rest=cfg.regularOpCost+(27*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+27) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ .and (w.bLo) (4294967295) (b0 w) post
  · simp only [Numeric.ibinop64,b0]
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 27*cfg.regularOpCost+rest=cfg.regularOpCost+(26*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+26) _ (paid s cfg.regularOpCost 4) limits _ frame callers _ 5 (.i64 (b0 w)) post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 26*cfg.regularOpCost+rest=cfg.regularOpCost+(25*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+25) _ (paid s cfg.regularOpCost 5) limits _ (frame1 frame w) callers _ 1 (.i64 (w.aLo)) post (by simp [teeFrame,frame1,h1])
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 25*cfg.regularOpCost+rest=cfg.regularOpCost+(24*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+24) _ (paid s cfg.regularOpCost 6) limits _ (frame1 frame w) callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 24*cfg.regularOpCost+rest=cfg.regularOpCost+(23*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+23) _ (paid s cfg.regularOpCost 7) limits _ (frame1 frame w) callers _ .shr_u (w.aLo) (32) (a1 w) post
  · simp only [Numeric.ibinop64,a1,show (32 : UInt64)%64=32 by decide]
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [show 23*cfg.regularOpCost+rest=cfg.regularOpCost+(22*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+22) _ (paid s cfg.regularOpCost 8) limits _ (frame1 frame w) callers _ 6 (.i64 (a1 w)) post
  · exact paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  rw [show 22*cfg.regularOpCost+rest=cfg.regularOpCost+(21*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+21) _ (paid s cfg.regularOpCost 9) limits _ (frame2 frame w) callers _ .mul (b0 w) (a1 w) (cross0 w) post
  · simp only [Numeric.ibinop64,a1,b0,cross0]
  · exact paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  rw [show 21*cfg.regularOpCost+rest=cfg.regularOpCost+(20*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+20) _ (paid s cfg.regularOpCost 10) limits _ (frame2 frame w) callers _ 7 (.i64 (cross0 w)) post
  · exact paid_credits s cfg.regularOpCost 10 _ (hc.mono (by omega))
  rw [show 20*cfg.regularOpCost+rest=cfg.regularOpCost+(19*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+19) _ (paid s cfg.regularOpCost 11) limits _ (frame3 frame w) callers _ 3 (.i64 (w.bLo)) post (by simp [teeFrame,frame1,frame2,frame3,h3])
  · exact paid_credits s cfg.regularOpCost 11 _ (hc.mono (by omega))
  rw [show 19*cfg.regularOpCost+rest=cfg.regularOpCost+(18*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+18) _ (paid s cfg.regularOpCost 12) limits _ (frame3 frame w) callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 12 _ (hc.mono (by omega))
  rw [show 18*cfg.regularOpCost+rest=cfg.regularOpCost+(17*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+17) _ (paid s cfg.regularOpCost 13) limits _ (frame3 frame w) callers _ .shr_u (w.bLo) (32) (b1 w) post
  · simp only [Numeric.ibinop64,b1,show (32 : UInt64)%64=32 by decide]
  · exact paid_credits s cfg.regularOpCost 13 _ (hc.mono (by omega))
  rw [show 17*cfg.regularOpCost+rest=cfg.regularOpCost+(16*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+16) _ (paid s cfg.regularOpCost 14) limits _ (frame3 frame w) callers _ 8 (.i64 (b1 w)) post
  · exact paid_credits s cfg.regularOpCost 14 _ (hc.mono (by omega))
  rw [show 16*cfg.regularOpCost+rest=cfg.regularOpCost+(15*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+15) _ (paid s cfg.regularOpCost 15) limits _ (frame4 frame w) callers _ 1 (.i64 (w.aLo)) post (by simp [teeFrame,frame1,frame2,frame3,frame4,h1])
  · exact paid_credits s cfg.regularOpCost 15 _ (hc.mono (by omega))
  rw [show 15*cfg.regularOpCost+rest=cfg.regularOpCost+(14*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+14) _ (paid s cfg.regularOpCost 16) limits _ (frame4 frame w) callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 16 _ (hc.mono (by omega))
  rw [show 14*cfg.regularOpCost+rest=cfg.regularOpCost+(13*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+13) _ (paid s cfg.regularOpCost 17) limits _ (frame4 frame w) callers _ .and (w.aLo) (4294967295) (a0 w) post
  · simp only [Numeric.ibinop64,a0]
  · exact paid_credits s cfg.regularOpCost 17 _ (hc.mono (by omega))
  rw [show 13*cfg.regularOpCost+rest=cfg.regularOpCost+(12*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+12) _ (paid s cfg.regularOpCost 18) limits _ (frame4 frame w) callers _ 9 (.i64 (a0 w)) post
  · exact paid_credits s cfg.regularOpCost 18 _ (hc.mono (by omega))
  rw [show 12*cfg.regularOpCost+rest=cfg.regularOpCost+(11*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+11) _ (paid s cfg.regularOpCost 19) limits _ (frame5 frame w) callers _ .mul (b1 w) (a0 w) (b1 w*a0 w) post
  · simp only [Numeric.ibinop64,a0,b1]
  · exact paid_credits s cfg.regularOpCost 19 _ (hc.mono (by omega))
  rw [show 11*cfg.regularOpCost+rest=cfg.regularOpCost+(10*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+10) _ (paid s cfg.regularOpCost 20) limits _ (frame5 frame w) callers _ .add (cross0 w) (b1 w*a0 w) (cross w) post
  · simp only [Numeric.ibinop64,a0,a1,b0,b1,cross0,cross]
  · exact paid_credits s cfg.regularOpCost 20 _ (hc.mono (by omega))
  rw [show 10*cfg.regularOpCost+rest=cfg.regularOpCost+(9*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+9) _ (paid s cfg.regularOpCost 21) limits _ (frame5 frame w) callers _ 10 (.i64 (cross w)) post
  · exact paid_credits s cfg.regularOpCost 21 _ (hc.mono (by omega))
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+8) _ (paid s cfg.regularOpCost 22) limits _ (frame6 frame w) callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 22 _ (hc.mono (by omega))
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+7) _ (paid s cfg.regularOpCost 23) limits _ (frame6 frame w) callers _ .shl (cross w) (32) (shifted w) post
  · simp only [Numeric.ibinop64,a0,a1,b0,b1,cross0,cross,shifted,show (32 : UInt64)%64=32 by decide]
  · exact paid_credits s cfg.regularOpCost 23 _ (hc.mono (by omega))
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+6) _ (paid s cfg.regularOpCost 24) limits _ (frame6 frame w) callers _ 11 (.i64 (shifted w)) post
  · exact paid_credits s cfg.regularOpCost 24 _ (hc.mono (by omega))
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+5) _ (paid s cfg.regularOpCost 25) limits _ (frame7 frame w) callers _ 5 (.i64 (b0 w)) post (by simp [teeFrame,frame1,frame2,frame3,frame4,frame5,frame6,frame7,bounds])
  · exact paid_credits s cfg.regularOpCost 25 _ (hc.mono (by omega))
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+4) _ (paid s cfg.regularOpCost 26) limits _ (frame7 frame w) callers _ 9 (.i64 (a0 w)) post (by simp [teeFrame,frame1,frame2,frame3,frame4,frame5,frame6,frame7,bounds])
  · exact paid_credits s cfg.regularOpCost 26 _ (hc.mono (by omega))
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+3) _ (paid s cfg.regularOpCost 27) limits _ (frame7 frame w) callers _ .mul (b0 w) (a0 w) (b0 w*a0 w) post
  · simp only [Numeric.ibinop64,a0,b0]
  · exact paid_credits s cfg.regularOpCost 27 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+2) _ (paid s cfg.regularOpCost 28) limits _ (frame7 frame w) callers _ .add (shifted w) (b0 w*a0 w) (lowWord w) post
  · simp only [Numeric.ibinop64,a0,a1,b0,b1,cross0,cross,shifted,lowWord]
  · exact paid_credits s cfg.regularOpCost 28 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(1*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+1) _ (paid s cfg.regularOpCost 29) limits _ (frame7 frame w) callers _ 5 (.i64 (lowWord w)) post
  · exact paid_credits s cfg.regularOpCost 29 _ (hc.mono (by omega))
  simp only [Nat.one_mul]
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 30) limits stack (finalFrame frame w) callers code {align:=3,offset:=0} w.out (lowWord w) mi index memory post
  · simpa only [paid,chargedStore,frame1,frame2,frame3,frame4,frame5,frame6,frame7,finalFrame,teeFrame] using hm
  · exact hi
  · simpa only [paid,chargedStore] using hmem
  · simpa only [Nat.add_zero] using hb
  · exact paid_credits s cfg.regularOpCost 30 _ (hc.mono (by omega))
  · simpa only [lowStore,paid,Nat.add_zero] using hnext

end WNear.Proofs.SerializeMultiply
