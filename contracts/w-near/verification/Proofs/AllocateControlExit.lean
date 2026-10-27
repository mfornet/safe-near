import Proofs.AllocateSearchMemory
import NearVM.MeteredLabelRules
import Binary.AllocateControl

/-! Actual flag-zero exit from all thirteen nested labels in f580. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem header_flag_zero (p : Layout) (hn : Native p) : header p &&& 2 = 0 := by
  calc
    header p &&& 2 = header p &&& ((3 : UInt32) &&& 2) := rfl
    _ = (header p &&& 3) &&& 2 := (UInt32.and_assoc (header p) 3 2).symm
    _ = 0 := by rw [header_aligned p hn]; rfl

/-- The actual branch12 is resolved from its label stack, with its condition
derived from the new header's original-heap alignment. -/
theorem wp_flag_exit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length = 12) (h2 : frame.locals[2]? = some (.i32 (header p))) (hn : Native p)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (WNear.Binary.AllocateSearch.flagExit++discarded))) (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let nested := labelPrefixFrame frame stack.size skipped code
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ s limits stack nested callers _ 2 (.i32 (header p)) post h2 (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 1) limits _ nested callers _ 2 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+2) _ (paid s op 2) limits stack nested callers _ (header p) 2 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [header_flag_zero p hn]
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 3) limits stack nested callers _ 0 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have next : WP cfg fuel (.next (atCode (chargedStore (paid s op 4) op) limits stack frame callers code)) rest post := by
    simpa only [paid,op] using hnext
  have branch := wp_br_if_label_nonzero cfg fuel rest (paid s op 4) limits stack frame callers skipped code discarded 1 post
    (by decide) (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) next
  simpa only [hskip,Numeric.bool,BEq.rfl,ite_true,nested,op,paid,List.append_eq,List.cons_append,List.nil_append] using branch
end WNear.Proofs.AllocateSearch
