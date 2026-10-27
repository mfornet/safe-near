import Proofs.ZeroFillLoop

/-! Residual gas and caller-frame fields of the actual symbolic fill loop. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] iterationStore written
set_option maxRecDepth 16384

theorem loopAfter_credits (s : Store NearState) (op index rest : Nat) (memory : Memory)
    (ptr value count : UInt32) (n : Nat)
    (hc : s.host.gas.Credits (loopCost n*op+rest)) :
    (loopAfter s op index memory ptr value count n).host.gas.Credits rest := by
  induction n generalizing s memory ptr count with
  | zero => simpa only [loopAfter,loopCost,Nat.zero_mul,Nat.zero_add,ite_true] using hc
  | succ n ih =>
    have cut : 11*op+((if n=0 then op else 2*op)+(loopCost n*op+rest)) ≤ loopCost (n+1)*op+rest := by
      rw [loopCost_succ]
      split <;> simp only [Nat.add_mul] <;> omega
    have ci := iteration_credits s op index _ memory ptr value (hc.mono cut)
    have cb := StorePair.charged_credits (iterationStore s op index memory ptr value)
      (if n=0 then op else 2*op) (loopCost n*op+rest) ci
    exact ih _ (writeByte memory ptr.toNat value) (ptr+1) (nextCount count) cb

theorem loopFrameAfter_shape (frame : CallFrame) (ptr count : UInt32) (n : Nat) :
    (loopFrameAfter frame ptr count n).inst=frame.inst ∧
    (loopFrameAfter frame ptr count n).arity=frame.arity ∧
    (loopFrameAfter frame ptr count n).height=frame.height ∧
    (loopFrameAfter frame ptr count n).labels=frame.labels ∧
    (loopFrameAfter frame ptr count n).locals[0]?=frame.locals[0]? ∧
    (loopFrameAfter frame ptr count n).locals[1]?=frame.locals[1]? := by
  induction n generalizing frame ptr count with
  | zero => simp only [loopFrameAfter,and_self]
  | succ n ih =>
    have h := ih (iterationFrame frame ptr count) (ptr+1) (nextCount count)
    simpa [loopFrameAfter,iterationFrame,pointerFrame] using h

end WNear.Proofs.ZeroFill
