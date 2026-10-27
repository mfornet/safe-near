import Proofs.SerializeMultiplyState

/-! The actual 29-instruction upper-word suffix of f954. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64

def highStore (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :=
  storeI64 (paid s op 29) index (w.out.toNat+8) memory (highWord w)

theorem wp_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (w : Words) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 (w.out)))
    (h1 : frame.locals[1]?=some (.i64 (w.aLo)))
    (h2 : frame.locals[2]?=some (.i64 (w.aHi)))
    (h3 : frame.locals[3]?=some (.i64 (w.bLo)))
    (h4 : frame.locals[4]?=some (.i64 (w.bHi)))
    (h5 : frame.locals[5]?=some (.i64 (lowWord w)))
    (h6 : frame.locals[6]?=some (.i64 (a1 w)))
    (h7 : frame.locals[7]?=some (.i64 (cross0 w)))
    (h8 : frame.locals[8]?=some (.i64 (b1 w)))
    (h10 : frame.locals[10]?=some (.i64 (cross w)))
    (h11 : frame.locals[11]?=some (.i64 (shifted w)))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hb : w.out.toNat+16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (29*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory w) limits stack frame callers code)) rest post) :
    WP cfg (fuel+29) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeMultiply.high++code)))
      (29*cfg.regularOpCost+rest) post := by
  unfold WNear.Binary.SerializeMultiply.high
  rw [show 29*cfg.regularOpCost+rest=cfg.regularOpCost+(28*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+28) _ s limits _ frame callers _ 0 (.i32 (w.out)) post h0
  · exact hc.mono (by omega)
  rw [show 28*cfg.regularOpCost+rest=cfg.regularOpCost+(27*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+27) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 10 (.i64 (cross w)) post h10
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 27*cfg.regularOpCost+rest=cfg.regularOpCost+(26*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+26) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 7 (.i64 (cross0 w)) post h7
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 26*cfg.regularOpCost+rest=cfg.regularOpCost+(25*cfg.regularOpCost+rest) by omega]
  apply wp_i64_relop cfg (fuel+25) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ .lt_u (cross w) (cross0 w) post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 25*cfg.regularOpCost+rest=cfg.regularOpCost+(24*cfg.regularOpCost+rest) by omega]
  apply wp_i64_extend_i32_u cfg (fuel+24) _ (paid s cfg.regularOpCost 4) limits _ frame callers _ (Numeric.bool (Numeric.irelop64 .lt_u (cross w) (cross0 w))) post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 24*cfg.regularOpCost+rest=cfg.regularOpCost+(23*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+23) _ (paid s cfg.regularOpCost 5) limits _ frame callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 23*cfg.regularOpCost+rest=cfg.regularOpCost+(22*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+22) _ (paid s cfg.regularOpCost 6) limits _ frame callers _ .shl (carry (cross w) (cross0 w)) (32) (carry (cross w) (cross0 w) <<< (32 : UInt64)) post
  · simp only [Numeric.ibinop64,show (32 : UInt64)%64=32 by decide]
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 22*cfg.regularOpCost+rest=cfg.regularOpCost+(21*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+21) _ (paid s cfg.regularOpCost 7) limits _ frame callers _ 10 (.i64 (cross w)) post h10
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [show 21*cfg.regularOpCost+rest=cfg.regularOpCost+(20*cfg.regularOpCost+rest) by omega]
  apply wp_i64_const cfg (fuel+20) _ (paid s cfg.regularOpCost 8) limits _ frame callers _ 32 post
  · exact paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  rw [show 20*cfg.regularOpCost+rest=cfg.regularOpCost+(19*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+19) _ (paid s cfg.regularOpCost 9) limits _ frame callers _ .shr_u (cross w) (32) (cross w >>> (32 : UInt64)) post
  · simp only [Numeric.ibinop64,show (32 : UInt64)%64=32 by decide]
  · exact paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  rw [show 19*cfg.regularOpCost+rest=cfg.regularOpCost+(18*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+18) _ (paid s cfg.regularOpCost 10) limits _ frame callers _ .or (carry (cross w) (cross0 w) <<< (32 : UInt64)) (cross w >>> (32 : UInt64)) ((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64))) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 10 _ (hc.mono (by omega))
  rw [show 18*cfg.regularOpCost+rest=cfg.regularOpCost+(17*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+17) _ (paid s cfg.regularOpCost 11) limits _ frame callers _ 8 (.i64 (b1 w)) post h8
  · exact paid_credits s cfg.regularOpCost 11 _ (hc.mono (by omega))
  rw [show 17*cfg.regularOpCost+rest=cfg.regularOpCost+(16*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+16) _ (paid s cfg.regularOpCost 12) limits _ frame callers _ 6 (.i64 (a1 w)) post h6
  · exact paid_credits s cfg.regularOpCost 12 _ (hc.mono (by omega))
  rw [show 16*cfg.regularOpCost+rest=cfg.regularOpCost+(15*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+15) _ (paid s cfg.regularOpCost 13) limits _ frame callers _ .mul (b1 w) (a1 w) (b1 w*a1 w) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 13 _ (hc.mono (by omega))
  rw [show 15*cfg.regularOpCost+rest=cfg.regularOpCost+(14*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+14) _ (paid s cfg.regularOpCost 14) limits _ frame callers _ .add ((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64))) (b1 w*a1 w) (((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64)))+b1 w*a1 w) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 14 _ (hc.mono (by omega))
  rw [show 14*cfg.regularOpCost+rest=cfg.regularOpCost+(13*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+13) _ (paid s cfg.regularOpCost 15) limits _ frame callers _ 5 (.i64 (lowWord w)) post h5
  · exact paid_credits s cfg.regularOpCost 15 _ (hc.mono (by omega))
  rw [show 13*cfg.regularOpCost+rest=cfg.regularOpCost+(12*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+12) _ (paid s cfg.regularOpCost 16) limits _ frame callers _ 11 (.i64 (shifted w)) post h11
  · exact paid_credits s cfg.regularOpCost 16 _ (hc.mono (by omega))
  rw [show 12*cfg.regularOpCost+rest=cfg.regularOpCost+(11*cfg.regularOpCost+rest) by omega]
  apply wp_i64_relop cfg (fuel+11) _ (paid s cfg.regularOpCost 17) limits _ frame callers _ .lt_u (lowWord w) (shifted w) post
  · exact paid_credits s cfg.regularOpCost 17 _ (hc.mono (by omega))
  rw [show 11*cfg.regularOpCost+rest=cfg.regularOpCost+(10*cfg.regularOpCost+rest) by omega]
  apply wp_i64_extend_i32_u cfg (fuel+10) _ (paid s cfg.regularOpCost 18) limits _ frame callers _ (Numeric.bool (Numeric.irelop64 .lt_u (lowWord w) (shifted w))) post
  · exact paid_credits s cfg.regularOpCost 18 _ (hc.mono (by omega))
  rw [show 10*cfg.regularOpCost+rest=cfg.regularOpCost+(9*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+9) _ (paid s cfg.regularOpCost 19) limits _ frame callers _ .add (((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64)))+b1 w*a1 w) (carry (lowWord w) (shifted w)) ((((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64)))+b1 w*a1 w)+carry (lowWord w) (shifted w)) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 19 _ (hc.mono (by omega))
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+8) _ (paid s cfg.regularOpCost 20) limits _ frame callers _ 4 (.i64 (w.bHi)) post h4
  · exact paid_credits s cfg.regularOpCost 20 _ (hc.mono (by omega))
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+7) _ (paid s cfg.regularOpCost 21) limits _ frame callers _ 1 (.i64 (w.aLo)) post h1
  · exact paid_credits s cfg.regularOpCost 21 _ (hc.mono (by omega))
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+6) _ (paid s cfg.regularOpCost 22) limits _ frame callers _ .mul (w.bHi) (w.aLo) (w.bHi*w.aLo) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 22 _ (hc.mono (by omega))
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+5) _ (paid s cfg.regularOpCost 23) limits _ frame callers _ 3 (.i64 (w.bLo)) post h3
  · exact paid_credits s cfg.regularOpCost 23 _ (hc.mono (by omega))
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+4) _ (paid s cfg.regularOpCost 24) limits _ frame callers _ 2 (.i64 (w.aHi)) post h2
  · exact paid_credits s cfg.regularOpCost 24 _ (hc.mono (by omega))
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+3) _ (paid s cfg.regularOpCost 25) limits _ frame callers _ .mul (w.bLo) (w.aHi) (w.bLo*w.aHi) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 25 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+2) _ (paid s cfg.regularOpCost 26) limits _ frame callers _ .add (w.bHi*w.aLo) (w.bLo*w.aHi) (w.bHi*w.aLo+w.bLo*w.aHi) post
  · simp only [Numeric.ibinop64]
  · exact paid_credits s cfg.regularOpCost 26 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(1*cfg.regularOpCost+rest) by omega]
  apply wp_i64_binop_ok cfg (fuel+1) _ (paid s cfg.regularOpCost 27) limits _ frame callers _ .add ((((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64)))+b1 w*a1 w)+carry (lowWord w) (shifted w)) (w.bHi*w.aLo+w.bLo*w.aHi) (highWord w) post
  · simp only [Numeric.ibinop64,highWord]
  · exact paid_credits s cfg.regularOpCost 27 _ (hc.mono (by omega))
  simp only [Nat.one_mul]
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 28) limits stack frame callers code {align:=3,offset:=8} w.out (highWord w) mi index memory post
  · simpa only [paid,chargedStore] using hm
  · exact hi
  · simpa only [paid,chargedStore] using hmem
  · exact hb
  · exact paid_credits s cfg.regularOpCost 28 _ (hc.mono (by omega))
  · simpa only [highStore,paid] using hnext

end WNear.Proofs.SerializeMultiply
