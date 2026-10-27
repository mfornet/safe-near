import Binary.AllocateSkip
import Proofs.AllocateLoopPrepare
import Proofs.AllocateSearchState
import Proofs.AllocateSearchMemory
import Proofs.AllocateFit

/-! The actual unflagged-candidate preparation, from original header metadata. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

theorem wp_prepare (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (hbound : (head p).toNat+12≤p.memory.byteSize)
    (hflag : readI32 p.memory ((head p).toNat+8) &&& 1=0)
    (hh : frame.locals[1]? = some (.i32 (head p))) (_hs : 10 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hc : s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 10) limits stack (prepareFrame frame p) callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.candidatePrepare++code)))
      (10*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let word := readI32 p.memory ((head p).toNat+8)
  let first : CallFrame := {frame with locals:=frame.locals.set! 9 (.i32 word)}
  have headFirst : first.locals[1]? = some (.i32 (head p)) := by simp [first,hh]
  have hm1 : (paid s op 1).modules[frame.inst]? = some p.mi := by simpa only [paid,chargedStore] using hm
  have mem1 : (paid s op 1).mems[p.memoryIndex]? = some p.memory := by simpa only [paid,chargedStore] using hmem
  rw [show 10*cfg.regularOpCost+rest=cfg.regularOpCost+(9*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+9) _ s limits stack frame callers _ 1 (.i32 (head p)) post hh (hc.mono (by dsimp [op]; omega))
  rw [show 9*op+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+8) _ (paid s op 1) limits stack frame callers _ {align:=2,offset:=8} (head p) p.mi p.memoryIndex p.memory post hm1 hi mem1 (by change (head p).toNat+8+4≤p.memory.byteSize; omega)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+7) _ (paid s op 2) limits stack frame callers _ 9 (.i32 word) post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+6) _ (paid s op 3) limits (stack.push (.i32 word)) first callers _ 1 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+5) _ (paid s op 4) limits stack first callers _ word 1 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  simp only [word,hflag]
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_br_if_zero cfg (fuel+4) _ (paid s op 5) limits stack first callers _ 0 post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ (paid s op 6) limits stack first callers _ 1 (.i32 (head p)) post headFirst
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 7) limits (stack.push (.i32 (head p))) first callers _ 8 post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel+1) _ (paid s op 8) limits stack first callers _ (head p) 8 post
  · exact paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  apply wp_local_set cfg fuel rest (paid s op 9) limits stack first callers code 9 (.i32 (head p+8)) post
  · exact paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [first,prepareFrame,paid,op,Array.set!_eq_setIfInBounds,Array.setIfInBounds_setIfInBounds] using hnext
end WNear.Proofs.AllocateSkip
