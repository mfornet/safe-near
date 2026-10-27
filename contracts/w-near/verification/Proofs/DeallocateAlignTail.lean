import Proofs.DeallocateAlignGuards
import Proofs.ValueReturnLazyReturn

/-! The actual unsigned division and explicit return of f568. -/
namespace WNear.Proofs.DeallocateAlign
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open ValueReturnLazyLookup (wp_return_wasm)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- Division is executed only with a nonzero denominator; the explicit return
removes all guard labels and restores the saved caller with one result. -/
theorem wp_divide_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : List Instr) (numerator denominator : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 numerator)) (hb : frame.locals[1]? = some (.i32 denominator))
    (hn : denominator ≠ 0) (harity : frame.arity = 1) (hheight : frame.height = base.length)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (base ++ [Value.i32 (numerator / denominator)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits base.toArray frame (caller :: callers) (divideTail ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have ret := wp_return_wasm cfg fuel rest (paid s op 3) limits base [.i32 (numerator / denominator)] frame caller callers code post
    harity.symm hheight (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have array : (base ++ [Value.i32 (numerator / denominator)]).toArray = base.toArray.push (.i32 (numerator / denominator)) := by
    apply Array.toList_inj.mp
    simp
  have retNext : WP cfg (fuel + 1) (.next (atCode (paid s op 3) limits (base.toArray.push (.i32 (numerator / denominator))) frame (caller :: callers) (.return :: code))) (op + rest) post := by
    simpa only [array, op] using ret
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 3) _ s limits base.toArray frame (caller :: callers) _ 0 (.i32 numerator) post ha (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s op 1) limits _ frame (caller :: callers) _ 1 (.i32 denominator) post hb
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_div_u cfg (fuel + 1) _ (paid s op 2) limits base.toArray frame (caller :: callers) _ numerator denominator post hn
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  · exact retNext
end WNear.Proofs.DeallocateAlign
