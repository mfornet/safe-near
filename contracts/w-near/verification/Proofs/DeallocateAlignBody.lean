import Proofs.DeallocateAlignTail

/-! Complete checked arithmetic body, including both free guard blocks. -/
namespace WNear.Proofs.DeallocateAlign
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

private theorem paid_add (s : Store NearState) (op m n : Nat) :
    paid (paid s op m) op n = paid s op (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [paid, ih]
    rfl

def quotient (a b : UInt32) := (a + b + 4294967295) / b

/-- Actual normal f568 execution, with explicit arithmetic checks excluding
both panic blocks. No function or memory behavior is assumed. -/
theorem wp_body568 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a)) (hb : frame.locals[1]? = some (.i32 b)) (hsize : 3 ≤ frame.locals.size)
    (hadd : Numeric.irelop32 .lt_u (a + b) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + b + 4294967295) (a + b) = false)
    (hn : b ≠ 0) (harity : frame.arity = 1) (hheight : frame.height = base.length)
    (hc : s.host.gas.Credits (18 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 18) limits
      (base ++ [Value.i32 (quotient a b)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 20) (.next (atCode s limits base.toArray frame (caller :: callers)
      (WNear.Binary.DeallocateAlign.body568 ++ code))) (18 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let outer := emptyBlockFrame frame base.toArray.size (WNear.Binary.DeallocateAlign.overflowSub ++ code)
  let inner := emptyBlockFrame outer base.toArray.size WNear.Binary.DeallocateAlign.overflowAdd
  let summed := sumFrame inner (a + b)
  let adjusted := adjustedFrame summed (a + b + 4294967295)
  have ha0 : adjusted.locals[0]? = some (.i32 (a + b + 4294967295)) := by
    simp [adjusted, adjustedFrame, summed, sumFrame, inner, outer, emptyBlockFrame, show 0 < frame.locals.size by omega]
  have hb0 : adjusted.locals[1]? = some (.i32 b) := by
    simpa [adjusted, adjustedFrame, summed, sumFrame, inner, outer, emptyBlockFrame] using hb
  have tailNext : WP cfg fuel (.next (atCode (paid (paid s op 14) op 4) limits
      (base ++ [Value.i32 ((a + b + 4294967295) / b)]).toArray caller callers caller.code)) rest post := by
    simpa only [paid_add, quotient, Nat.reduceAdd] using hnext
  have tail := wp_divide_tail cfg fuel rest (paid s op 14) limits base adjusted caller callers [] (a + b + 4294967295) b post ha0 hb0 hn harity hheight
    (paid_credits s op 14 _ (hc.mono (by dsimp [op]; omega))) tailNext
  have hs : summed.locals[2]? = some (.i32 (a + b)) := by
    simp [summed, sumFrame, inner, outer, emptyBlockFrame, show 2 < frame.locals.size by omega]
  have subNext : WP cfg (fuel + 4) (.next (atCode (paid (paid s op 7) op 7) limits base.toArray
      (adjustedFrame summed (a + b + 4294967295)) (caller :: callers) divideTail)) (4 * op + rest) post := by
    simpa only [paid_add, adjusted, List.append_nil, Nat.reduceAdd] using tail
  have sub := wp_sub_guard cfg (fuel + 4) (4 * op + rest) (paid s op 7) limits base.toArray summed (caller :: callers) divideTail (a + b) post hs hsub
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) subNext
  have addNext : WP cfg (fuel + 11) (.next (atCode (paid s op 7) limits base.toArray (sumFrame inner (a + b)) (caller :: callers)
      (subGuard ++ divideTail))) (11 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, show 7 * cfg.regularOpCost + (4 * op + rest) = 11 * op + rest by dsimp [op]; omega] using sub
  have add := wp_add_guard cfg (fuel + 11) (11 * op + rest) s limits base.toArray inner (caller :: callers) (subGuard ++ divideTail) a b post ha hb hadd
    (hc.mono (by dsimp [op]; omega)) addNext
  have innerNext : WP cfg (fuel + 18) (.next (atCode s limits base.toArray inner (caller :: callers) WNear.Binary.DeallocateAlign.accepted))
      (18 * op + rest) post := by
    simpa only [addGuard, subGuard, divideTail, WNear.Binary.DeallocateAlign.accepted, List.cons_append, List.nil_append,
      Nat.add_assoc, Nat.reduceAdd, show 7 * cfg.regularOpCost + (11 * op + rest) = 18 * op + rest by dsimp [op]; omega] using add
  have innerBlock := wp_block_empty cfg (fuel + 18) (18 * op + rest) s limits base.toArray outer (caller :: callers)
    WNear.Binary.DeallocateAlign.accepted WNear.Binary.DeallocateAlign.overflowAdd post hc innerNext
  have outerNext : WP cfg (fuel + 19) (.next (atCode s limits base.toArray outer (caller :: callers)
      ([.block .empty WNear.Binary.DeallocateAlign.accepted] ++ WNear.Binary.DeallocateAlign.overflowAdd))) (18 * op + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append] using innerBlock
  have outerBlock := wp_block_empty cfg (fuel + 19) (18 * op + rest) s limits base.toArray frame (caller :: callers)
    ([.block .empty WNear.Binary.DeallocateAlign.accepted] ++ WNear.Binary.DeallocateAlign.overflowAdd)
    (WNear.Binary.DeallocateAlign.overflowSub ++ code) post hc outerNext
  simpa only [WNear.Binary.DeallocateAlign.body568, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using outerBlock
end WNear.Proofs.DeallocateAlign
