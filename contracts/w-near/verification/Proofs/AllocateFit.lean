import Binary.AllocateFit
import Proofs.AllocateNative
import Proofs.StorePairCallerState
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules
import NearVM.MeteredBitRules

/-! Actual end subtraction and guards of the positive end-split path. Every
arithmetic check follows from the original free-block interval. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode readI32 writeI32

def fitFrame (frame : CallFrame) (memory : Memory) (head words : UInt32) :=
  {frame with locals := (frame.locals.set! 11 (.i32 (endWord memory head))).set! 12 (.i32 (splitPointer memory head words))}

theorem split_sub_check (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    Numeric.irelop32 .gt_u (endWord memory head - words*4) (endWord memory head) = false := by
  have pointer := split_pointer_toNat memory head words h
  have hnot : ¬ endWord memory head < endWord memory head - words*4 := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬ (endWord memory head).toNat < (splitPointer memory head words).toNat
    rw [pointer]
    omega
  simpa [Numeric.irelop32] using hnot

/-- The deployed thirteen-opcode prefix checks end subtraction and the
alignment overflow flag before invoking the real layout callback. -/
theorem wp_fit_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head words : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hh : frame.locals[1]? = some (.i32 head)) (hcbytes : frame.locals[10]? = some (.i32 (words*4)))
    (hz : frame.locals[8]? = some (.i32 0)) (hs : 13 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : head.toNat+4 ≤ memory.byteSize)
    (hn : SplitNative memory head words) (hc : s.host.gas.Credits (13*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 13) limits stack
      (fitFrame frame memory head words) callers code)) rest post) :
    WP cfg (fuel+13) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.fitHeader++code)))
      (13*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first : CallFrame := {frame with locals := frame.locals.set! 11 (.i32 (endWord memory head))}
  let second : CallFrame := {first with locals := first.locals.set! 12 (.i32 (splitPointer memory head words))}
  have h11 : 11 < frame.locals.size := by omega
  have h12 : 12 < frame.locals.size := by omega
  have bytes : first.locals[10]? = some (.i32 (words*4)) := by simp [first,hcbytes]
  have finish : second.locals[11]? = some (.i32 (endWord memory head)) := by simp [second,first,h11]
  have zero : second.locals[8]? = some (.i32 0) := by simp [second,first,hz]
  have check := split_sub_check memory head words hn
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 13*cfg.regularOpCost+rest=cfg.regularOpCost+(12*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+12) _ s limits stack frame callers _ 1 (.i32 head) post hh (hc.mono (by dsimp [op]; omega))
  rw [show 12*op+rest=cfg.regularOpCost+(11*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+11) _ (paid s op 1) limits stack frame callers _ {align:=2,offset:=0}
    head mi index memory post hm1 hi hmem1 (by simpa using hb)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  rw [show 11*op+rest=cfg.regularOpCost+(10*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+10) _ (paid s op 2) limits _ frame callers _ 4294967292 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 10*op+rest=cfg.regularOpCost+(9*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+9) _ (paid s op 3) limits stack frame callers _ (readI32 memory head.toNat) 4294967292 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 9*op+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+8) _ (paid s op 4) limits stack frame callers _ 11 (.i32 (endWord memory head)) post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+7) _ (paid s op 5) limits _ first callers _ 10 (.i32 (words*4)) post bytes
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_i32_sub cfg (fuel+6) _ (paid s op 6) limits stack first callers _ (endWord memory head) (words*4) post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+5) _ (paid s op 7) limits stack first callers _ 12 (.i32 (splitPointer memory head words)) post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 8) limits _ second callers _ 11 (.i32 (endWord memory head)) post finish
  · exact paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel+3) _ (paid s op 9) limits stack second callers _ .gt_u
    (endWord memory head - words*4) (endWord memory head) post
  · exact paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))
  simp only [check,Numeric.bool]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_br_if_zero cfg (fuel+2) _ (paid s op 10) limits stack second callers _ 0 post
  · exact paid_credits s op 10 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+1) _ (paid s op 11) limits stack second callers _ 8 (.i32 0) post zero
  · exact paid_credits s op 11 _ (hc.mono (by dsimp [op]; omega))
  apply wp_br_if_zero cfg fuel rest (paid s op 12) limits stack second callers code 1 post
  · exact paid_credits s op 12 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [second,first,fitFrame,op,paid] using hnext
end WNear.Proofs.Allocate
