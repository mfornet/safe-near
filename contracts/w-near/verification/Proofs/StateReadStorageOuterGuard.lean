import Binary.StateReadStorageOuter
import Proofs.StorePairCallerState
import NearVM.MeteredBrTableRules
import NearVM.MeteredLoopRules
import NearVM.MeteredWordRules

/-! Actual548 status-one branch, including its real br_table selection. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def statusFrame (frame : CallFrame) := {frame with locals:=frame.locals.set! 4 (.i64 1)}

theorem wp_status_one (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code : Expr) (post : Post) (hs : 5≤frame.locals.size) (hl : skipped.length=2)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack (statusFrame frame) callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits (stack.push (.i64 1))
      (labelPrefixFrame frame stack.size skipped code) callers WNear.Binary.StateReadStorageOuter.statusGuard))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let sf := statusFrame frame
  let nf := labelPrefixFrame sf stack.size skipped code
  have h4 : nf.locals[4]?=some (.i64 1) := by
    simp [nf,labelPrefixFrame,sf,statusFrame,show 4<frame.locals.size by omega]
  have branch := wp_br_table_label cfg fuel rest (paid s op 6) limits stack sf callers skipped code [] 1 [1,2] 1 post
    (by rw [hl];rfl) (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have wrap := wp_i32_wrap_i64 cfg (fuel+1) (op+rest) (paid s op 5) limits stack nf callers [.br_table [1,2] 1] 1 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) (by simpa only [nf,paid,op,show (1:UInt64).toUInt32=1 by decide] using branch)
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits stack nf callers [.cvt .i32_wrap_i64,.br_table [1,2] 1] 4 (.i64 1) post h4
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) wrap
  have br := wp_br_if_zero cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits stack nf callers
    [.local_get 4,.cvt .i32_wrap_i64,.br_table [1,2] 1] 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) get
  have rel := wp_i64_relop cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits stack nf callers
    [.br_if 0,.local_get 4,.cvt .i32_wrap_i64,.br_table [1,2] 1] .gt_u 1 1 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [paid,op,Nat.reduceAdd,show Numeric.bool (Numeric.irelop64 .gt_u 1 1)=0 by decide] using br)
  have con := wp_i64_const cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits (stack.push (.i64 1)) nf callers
    [.i64_relop .gt_u,.br_if 0,.local_get 4,.cvt .i32_wrap_i64,.br_table [1,2] 1] 1 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) rel
  have tee := wp_local_tee cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack
    (labelPrefixFrame frame stack.size skipped code) callers
    [.i64_const 1,.i64_relop .gt_u,.br_if 0,.local_get 4,.cvt .i32_wrap_i64,.br_table [1,2] 1] 4 (.i64 1) post
    (hc.mono (by dsimp [op];omega)) con
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.StateReadStorageOuter.statusGuard,cost] using tee
end WNear.Proofs.StateReadStorageOuter
