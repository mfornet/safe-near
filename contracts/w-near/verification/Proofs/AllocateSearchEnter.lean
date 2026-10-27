import Proofs.AllocateSearchShell
import Proofs.AllocateSearchState
import NearVM.MeteredNumericRules

/-! Actual paid loop entries and the nonempty-head scan of580. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open WNear.Binary.AllocateSearch
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode outer exhausted scan candidateOuter candidateMiddle candidateInner candidateLoop inspect

theorem wp_enter_candidate (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (post : Post) (hc : s.host.gas.Credits (cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore s cfg.regularOpCost) limits stack
      (inspectFrame frame stack.size code) callers inspect)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack (scanFrame frame stack.size code) callers [.block .empty candidateOuter]))
      (cfg.regularOpCost+rest) post := by
  apply wp_block_empty cfg (fuel+4) _ s limits stack _ callers candidateOuter [] post hc
  rw [candidateOuter_eq]
  apply wp_block_empty cfg (fuel+3) _ s limits stack _ callers candidateMiddle _ post hc
  rw [candidateMiddle_eq]
  apply wp_block_empty cfg (fuel+2) _ s limits stack _ callers candidateInner _ post hc
  rw [candidateInner_eq]
  apply wp_loop_empty cfg (fuel+1) rest s limits stack _ callers candidateLoop _ post hc
  rw [candidateLoop_eq]
  apply wp_block_empty cfg fuel rest (chargedStore s cfg.regularOpCost) limits stack _ callers inspect _ post
    (StorePair.charged_credits s cfg.regularOpCost rest hc)
  simpa only [inspectFrame,List.append_eq,List.nil_append,←candidateLoop_eq] using hnext

theorem wp_scan_nonempty (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : head p≠0)
    (hh : frame.locals[1]?=some (.i32 (head p))) (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack
      (inspectFrame frame stack.size code) callers inspect)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack (scanFrame frame stack.size code) callers scan))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let sf := scanFrame frame stack.size code
  have enterNext : WP cfg fuel (.next (atCode (chargedStore (paid s op 3) cfg.regularOpCost) limits stack
      (inspectFrame frame stack.size code) callers inspect)) rest post := by simpa only [op,paid] using hnext
  have enter := wp_enter_candidate cfg fuel rest (paid s op 3) limits stack frame callers code post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) enterNext
  rw [scan_eq]
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+7) _ s limits stack sf callers _ 1 (.i32 (head p)) post hh (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+6) _ (paid s op 1) limits stack sf callers _ (head p) post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  simp only [show (head p==0)=false from by simp [hn],Numeric.bool,Bool.false_eq_true,ite_false]
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_br_if_zero cfg (fuel+5) _ (paid s op 2) limits stack sf callers _ 2 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  simpa only [sf,op,paid] using enter

theorem wp_enter_search (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : head p≠0)
    (hh : frame.locals[1]?=some (.i32 (head p))) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      (inspectFrame frame stack.size code) callers inspect)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits stack frame callers (.block .empty outer::.local_get 5::code)))
      (5*cfg.regularOpCost+rest) post := by
  apply wp_block_empty cfg (fuel+10) _ s limits stack frame callers outer (.local_get 5::code) post hc
  rw [outer_eq]
  apply wp_block_empty cfg (fuel+9) _ s limits stack _ callers exhausted WNear.Binary.Allocate.commit post hc
  rw [exhausted_eq]
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*cfg.regularOpCost+rest) by omega]
  apply wp_loop_empty cfg (fuel+8) (4*cfg.regularOpCost+rest) s limits stack _ callers scan _ post (hc.mono (by omega))
  have next : WP cfg fuel (.next (atCode (paid (chargedStore s cfg.regularOpCost) cfg.regularOpCost 4) limits stack
      (inspectFrame frame stack.size code) callers inspect)) rest post := by
    simpa only [paid] using hnext
  have result := wp_scan_nonempty cfg fuel rest (chargedStore s cfg.regularOpCost) limits stack frame callers code p post hn hh
    (StorePair.charged_credits s cfg.regularOpCost _ (hc.mono (by omega))) next
  simpa only [scanFrame,outerFrame,List.append_eq,List.nil_append] using result
end
end WNear.Proofs.AllocateSearch
