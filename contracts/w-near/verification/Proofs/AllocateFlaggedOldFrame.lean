import Proofs.AllocateFlaggedMemory

/-! The flags-two split keeps bytes below its original head, except its root cell. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout)
attribute [local irreducible] readI32 writeI32 writeI64

private theorem outside (p : Layout) (m : Memory) (shape : Shape p m)
    (a : Nat) (v : UInt32) (hb : a+4≤p.memory.byteSize) (j : Nat)
    (hj : j<a ∨ a+4≤j) : (writeI32 m a v).read8 j=m.read8 j := by
  rw [(writeI32_spec m a v shape.wf (by rw [shape.size];exact hb)).2.2.2 j]
  exact ite_eq_right (by omega)

theorem finalMemory_below_head (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<(head p).toNat) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have b := intervals p hn
  unfold finalMemory Allocate.markedMemory
  rw [outside p _ (flagged_shape p hn) _ _ (by omega) j (by omega)]
  unfold flaggedMemory
  rw [outside p _ (clearedFlag_shape p hn) _ _ (by omega) j (by omega)]
  unfold clearedFlagMemory
  rw [outside p _ (linked_shape p hn) _ _ (by omega) j (by omega)]
  unfold linkedMemory
  rw [outside p _ (unflagged_shape p hn) _ _ (by omega) j (by omega)]
  unfold unflaggedMemory
  rw [outside p _ (previous_shape p hn) _ _ (by omega) j (by omega)]
  unfold previousMemory
  rw [outside p _ (initialized_shape p hn) _ _ (by omega) j (by omega)]
  have init := Allocate.initializedMemory_spec p.memory (head p) (header p) hn.memoryWf (by omega) (by omega)
  exact init.2.2.2.2.2 j (Or.inl (by omega))
end WNear.Proofs.AllocateFlagged
