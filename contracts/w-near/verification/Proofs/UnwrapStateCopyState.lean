import Proofs.UnwrapStateCopy
import Proofs.ForwardCopyMemory

/-! Frames, credits and concrete memory effects of the actual f951 loop. -/
namespace WNear.Proofs.UnwrapStateCopyState
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.UnwrapStateCopy
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)

@[simp] theorem loopFrame_inst (frame : CallFrame) (out source : UInt32) (count : Nat) :
    (loopFrame frame out source count).inst = frame.inst := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih => simpa only [loopFrame, prefixFrame] using ih (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1)

@[simp] theorem loopFrame_arity (frame : CallFrame) (out source : UInt32) (count : Nat) :
    (loopFrame frame out source count).arity = frame.arity := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih => simpa only [loopFrame, prefixFrame] using ih (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1)

@[simp] theorem loopFrame_height (frame : CallFrame) (out source : UInt32) (count : Nat) :
    (loopFrame frame out source count).height = frame.height := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih => simpa only [loopFrame, prefixFrame] using ih (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1)

@[simp] theorem loopFrame_labels (frame : CallFrame) (out source : UInt32) (count : Nat) :
    (loopFrame frame out source count).labels = frame.labels := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih => simpa only [loopFrame, prefixFrame] using ih (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1)

@[simp] theorem loopFrame_local_zero (frame : CallFrame) (out source : UInt32) (count : Nat) :
    (loopFrame frame out source count).locals[0]? = frame.locals[0]? := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih =>
    rw [loopFrame, ih]
    simp [prefixFrame]

theorem loopFrame_set_labels (frame : CallFrame) (out source : UInt32) (count : Nat) (labels : List Label) :
    loopFrame {frame with labels} out source count = {loopFrame frame out source count with labels} := by
  induction count generalizing frame out source with
  | zero => rfl
  | succ n ih =>
    simp only [loopFrame, prefixFrame]
    exact ih (prefixFrame frame out source (UInt32.ofNat (n + 1))) (out + 1) (source + 1)

attribute [local irreducible] prefixStore byteStore chargedStore

/-- Exact residual gas credits, independent of pointer bounds or aliasing. -/
theorem loopStore_credits (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count rest : Nat)
    (hc : s.host.gas.Credits ((18 * count - 1) * op + rest)) :
    (loopStore s op index out source memory count).host.gas.Credits rest := by
  induction count generalizing s memory out source with
  | zero =>
    have hz : (18 * 0 - 1) * op + rest = rest := by omega
    rw [hz] at hc
    exact hc
  | succ n ih =>
    have hb : (18 * (n + 1) - 1) * op = 16 * op + ((if n = 0 then 1 else 2) * op + (18 * n - 1) * op) := by
      by_cases hn : n = 0
      · subst n; simp; omega
      · simp only [hn, ↓reduceIte]
        exact loop_cost_step op n (by omega)
    have h0 : s.host.gas.Credits (16 * op + ((if n = 0 then 1 else 2) * op + ((18 * n - 1) * op + rest))) := by
      convert hc using 1; omega
    have hp := prefixStore_credits s op index out source memory _ h0
    have hbranch := GasCounter.burn_credits (prefixStore s op index out source memory).host.gas
      ((if n = 0 then 1 else 2) * op) ((18 * n - 1) * op + rest) hp
    rw [loopStore_succ]
    have hnext : (chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)).host.gas.Credits
        ((18 * n - 1) * op + rest) := by
      simpa only [chargedStore, chargeHost] using hbranch.2.2.2
    exact ih _ _ _ _ hnext

end WNear.Proofs.UnwrapStateCopyState
