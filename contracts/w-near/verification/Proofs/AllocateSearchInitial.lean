import Proofs.AllocateSearchState
import Binary.AllocateSearch
import NearVM.MeteredNumericRules
import NearVM.MeteredI32MemoryRules

/-! Actual sixteen-opcode f580 initialization for alignment one. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
set_option maxRecDepth 16384

def initialFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=(((((frame.locals.set! 5 (.i32 0)).set! 6 (.i32 4294967295)).set! 7 (.i32 0)).set! 8 (.i32 0)).set! 1 (.i32 (head p)))}
def initialAfter (s : Store NearState) (op : Nat) := paid s op 16

theorem wp_initial (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 1)) (h2 : frame.locals[2]?=some (.i32 p.root))
    (hm : s.modules[frame.inst]?=some p.mi)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hb : p.root.toNat+4 ≤ p.memory.byteSize) (hc : s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (initialAfter s cfg.regularOpCost) limits stack (initialFrame frame p) callers code)) rest post) :
    WP cfg (fuel+16) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.initialCode++code)))
      (16*cfg.regularOpCost+rest) post := by
  let f1 : CallFrame := {frame with locals:=frame.locals.set! 5 (.i32 0)}
  let f2 : CallFrame := {f1 with locals:=f1.locals.set! 6 (.i32 4294967295)}
  let f3 : CallFrame := {f2 with locals:=f2.locals.set! 7 (.i32 0)}
  let f4 : CallFrame := {f3 with locals:=f3.locals.set! 8 (.i32 0)}
  have one1 : f1.locals[1]?=some (.i32 1) := by simp [f1,h1]
  have one2 : f2.locals[1]?=some (.i32 1) := by simp [f2,f1,h1]
  have one3 : f3.locals[1]?=some (.i32 1) := by simp [f3,f2,f1,h1]
  have root4 : f4.locals[2]?=some (.i32 p.root) := by simp [f4,f3,f2,f1,h2]
  have mem14 : (paid s cfg.regularOpCost 14).mems[p.memoryIndex]?=some p.memory := by simpa only [paid,chargedStore] using hmem
  have module14 : (paid s cfg.regularOpCost 14).modules[f4.inst]?=some p.mi := by simpa only [paid,chargedStore,f4,f3,f2,f1] using hm
  unfold WNear.Binary.AllocateSearch.initialCode
  rw [show 16*cfg.regularOpCost+rest=cfg.regularOpCost+(15*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+15) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  rw [show 15*cfg.regularOpCost+rest=cfg.regularOpCost+(14*cfg.regularOpCost+rest) by omega]
  apply wp_local_set cfg (fuel+14) _ (paid s cfg.regularOpCost 1) limits stack frame callers _ 5 (.i32 0) post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 14*cfg.regularOpCost+rest=cfg.regularOpCost+(13*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+13) _ (paid s cfg.regularOpCost 2) limits stack f1 callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 13*cfg.regularOpCost+rest=cfg.regularOpCost+(12*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+12) _ (paid s cfg.regularOpCost 3) limits _ f1 callers _ 1 (.i32 1) post one1
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 12*cfg.regularOpCost+rest=cfg.regularOpCost+(11*cfg.regularOpCost+rest) by omega]
  apply wp_i32_sub cfg (fuel+11) _ (paid s cfg.regularOpCost 4) limits stack f1 callers _ 0 1 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  simp only [show (0 : UInt32)-1=4294967295 by decide]
  rw [show 11*cfg.regularOpCost+rest=cfg.regularOpCost+(10*cfg.regularOpCost+rest) by omega]
  apply wp_local_set cfg (fuel+10) _ (paid s cfg.regularOpCost 5) limits stack f1 callers _ 6 (.i32 4294967295) post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 10*cfg.regularOpCost+rest=cfg.regularOpCost+(9*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+9) _ (paid s cfg.regularOpCost 6) limits stack f2 callers _ 1 (.i32 1) post one2
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*cfg.regularOpCost+rest) by omega]
  apply wp_i32_const cfg (fuel+8) _ (paid s cfg.regularOpCost 7) limits _ f2 callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*cfg.regularOpCost+rest) by omega]
  apply wp_i32_add cfg (fuel+7) _ (paid s cfg.regularOpCost 8) limits stack f2 callers _ 1 4294967295 post
  · exact paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  simp only [show (1 : UInt32)+4294967295=0 by decide]
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*cfg.regularOpCost+rest) by omega]
  apply wp_local_tee cfg (fuel+6) _ (paid s cfg.regularOpCost 9) limits stack f2 callers _ 7 (.i32 0) post
  · exact paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  rw [show 6*cfg.regularOpCost+rest=cfg.regularOpCost+(5*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+5) _ (paid s cfg.regularOpCost 10) limits _ f3 callers _ 1 (.i32 1) post one3
  · exact paid_credits s cfg.regularOpCost 10 _ (hc.mono (by omega))
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_i32_relop cfg (fuel+4) _ (paid s cfg.regularOpCost 11) limits stack f3 callers _ .gt_u 0 1 post
  · exact paid_credits s cfg.regularOpCost 11 _ (hc.mono (by omega))
  simp only [show Numeric.bool (Numeric.irelop32 .gt_u 0 1)=0 by decide]
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*cfg.regularOpCost+rest) by omega]
  apply wp_local_set cfg (fuel+3) _ (paid s cfg.regularOpCost 12) limits stack f3 callers _ 8 (.i32 0) post
  · exact paid_credits s cfg.regularOpCost 12 _ (hc.mono (by omega))
  rw [show 3*cfg.regularOpCost+rest=cfg.regularOpCost+(2*cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+2) _ (paid s cfg.regularOpCost 13) limits stack f4 callers _ 2 (.i32 p.root) post root4
  · exact paid_credits s cfg.regularOpCost 13 _ (hc.mono (by omega))
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_i32_load cfg (fuel+1) _ (paid s cfg.regularOpCost 14) limits stack f4 callers _ {align:=2,offset:=0} p.root p.mi p.memoryIndex p.memory post module14 hi mem14 (by simpa only [Nat.add_zero] using hb)
  · exact paid_credits s cfg.regularOpCost 14 _ (hc.mono (by omega))
  simp only [Nat.add_zero]
  apply wp_local_set cfg fuel rest (paid s cfg.regularOpCost 15) limits stack f4 callers code 1 (.i32 (head p)) post
  · exact paid_credits s cfg.regularOpCost 15 _ (hc.mono (by omega))
  · simpa only [initialAfter,initialFrame,f4,f3,f2,f1,paid] using hnext

theorem initialFrame_locals (frame : CallFrame) (p : Layout) (hs : 14 ≤ frame.locals.size) :
    (initialFrame frame p).locals[1]?=some (.i32 (head p)) ∧
    (initialFrame frame p).locals[5]?=some (.i32 0) ∧
    (initialFrame frame p).locals[6]?=some (.i32 4294967295) ∧
    (initialFrame frame p).locals[7]?=some (.i32 0) ∧
    (initialFrame frame p).locals[8]?=some (.i32 0) := by
  simp [initialFrame,show 1 < frame.locals.size by omega,show 5 < frame.locals.size by omega,
    show 6 < frame.locals.size by omega,show 7 < frame.locals.size by omega,show 8 < frame.locals.size by omega]

theorem initialFrame_original (frame : CallFrame) (p : Layout) :
    (initialFrame frame p).locals[0]?=frame.locals[0]? ∧
    (initialFrame frame p).locals[2]?=frame.locals[2]? ∧
    (initialFrame frame p).locals[3]?=frame.locals[3]? ∧
    (initialFrame frame p).locals[4]?=frame.locals[4]? := by simp [initialFrame]

theorem initialAfter_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (16*op+rest)) :
    (initialAfter s op).host.gas.Credits rest := paid_credits s op 16 rest hc

end WNear.Proofs.AllocateSearch
