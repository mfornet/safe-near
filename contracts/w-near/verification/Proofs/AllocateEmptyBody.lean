import Proofs.AllocateSearchInitial
import Proofs.AllocateSearchShell
import NearVM.MeteredNumericRules

/-! The actual empty free-list branch of580. No candidate metadata is required. -/
namespace WNear.Proofs.AllocateEmpty
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateSearch
open WNear.Binary.AllocateSearch
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode outer exhausted scan

def after (s : Store NearState) (op : Nat) := paid s op 21

theorem wp_empty_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (post : Post)
    (hh : frame.locals[1]?=some (.i32 0)) (hz : frame.locals[5]?=some (.i32 0))
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (stack.push (.i32 0)) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (.block .empty outer::.local_get 5::code))) (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let sf := scanFrame frame stack.size code
  have hhs : sf.locals[1]?=some (.i32 0) := hh
  have getNext : WP cfg fuel (.next (atCode (chargedStore (paid s op 4) op) limits
      (stack.push (.i32 0)) frame callers code)) rest post := hnext
  have get := wp_local_get cfg fuel rest (paid s op 4) limits stack frame callers code 5 (.i32 0) post hz
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) getNext
  let skipped : List Label := [⟨0,stack.size,exhausted.drop 1,some scan⟩,⟨0,stack.size,WNear.Binary.Allocate.commit,none⟩]
  have branch := wp_br_if_label_nonzero cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers skipped
    (.local_get 5::code) [.block .empty candidateOuter] 1 post (by decide)
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) get
  have branchNext : WP cfg (fuel+2) (.next (atCode (paid s op 3) limits (stack.push (.i32 1))
      (scanFrame frame stack.size code) callers [.br_if 2,.block .empty candidateOuter])) (2*op+rest) post := by
    simpa only [skipped,scanFrame,outerFrame,emptyLoopFrame,emptyBlockFrame,labelPrefixFrame,
      List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+rest)=2*op+rest by dsimp [op]; omega] using branch
  apply wp_block_empty cfg (fuel+6) _ s limits stack frame callers outer (.local_get 5::code) post hc
  rw [outer_eq]
  apply wp_block_empty cfg (fuel+5) _ s limits stack _ callers exhausted WNear.Binary.Allocate.commit post hc
  rw [exhausted_eq]
  rw [show 5*cfg.regularOpCost+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_loop_empty cfg (fuel+4) (4*op+rest) s limits stack _ callers scan _ post (hc.mono (by dsimp [op]; omega))
  change WP cfg (fuel+4) (.next (atCode (paid s op 1) limits stack sf callers scan)) (4*op+rest) post
  rw [scan_eq]
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+3) _ (paid s op 1) limits stack sf callers _ 1 (.i32 0) post hhs
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+2) _ (paid s op 2) limits stack sf callers _ 0 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  simpa only [Numeric.bool,show ((0 : UInt32)==0)=true from rfl,ite_true,sf,scanFrame,outerFrame,
    emptyBlockFrame,emptyLoopFrame,List.append_eq,List.nil_append,op,paid] using branchNext

/-- Full21-operation/23-step body, derived from an original empty root word. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (ha : frame.locals[1]?=some (.i32 1)) (hr : frame.locals[2]?=some (.i32 p.root))
    (hs : 14≤frame.locals.size) (hh : head p=0)
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.memAddrs[0]?=some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]?=some p.memory) (hb : p.root.toNat+4≤p.memory.byteSize)
    (hc : s.host.gas.Credits (21*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost) limits
      (stack.push (.i32 0)) (initialFrame frame p) callers code)) rest post) :
    WP cfg (fuel+23) (.next (atCode s limits stack frame callers
      (WNear.Binary.Allocate.searchFunction.body++code))) (21*cfg.regularOpCost+rest) post := by
  have locals := initialFrame_locals frame p hs
  have zeroHead : (initialFrame frame p).locals[1]?=some (.i32 0) := by simpa only [hh] using locals.1
  have tailNext : WP cfg fuel (.next (atCode (paid (initialAfter s cfg.regularOpCost) cfg.regularOpCost 5) limits
      (stack.push (.i32 0)) (initialFrame frame p) callers code)) rest post := by
    simpa only [after,initialAfter,ValueReturnBorrow.paid_add,Nat.reduceAdd] using hnext
  have tail := wp_empty_tail cfg fuel rest (initialAfter s cfg.regularOpCost) limits stack (initialFrame frame p)
    callers code post zeroHead locals.2.1 (initialAfter_credits s cfg.regularOpCost _ (hc.mono (by omega))) tailNext
  have result := wp_initial cfg (fuel+7) (5*cfg.regularOpCost+rest) s limits stack frame callers
    (.block .empty outer::.local_get 5::code) p post ha hr hm hi hmem hb (hc.mono (by omega)) tail
  rw [WNear.Binary.AllocateSearch.function_body]
  simpa only [Nat.add_assoc,Nat.reduceAdd,show 16*cfg.regularOpCost+(5*cfg.regularOpCost+rest)=21*cfg.regularOpCost+rest by omega,
    List.append_assoc,List.cons_append,List.nil_append] using result
end
end WNear.Proofs.AllocateEmpty
