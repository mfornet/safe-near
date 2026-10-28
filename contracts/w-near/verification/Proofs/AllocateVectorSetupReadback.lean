import Proofs.AllocateVectorNative

/-! Both686 layout words follow from actual685 writes and packed copying. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 laidOutMemory

theorem setup_words (p : Layout) (hn : Native p) :
    readI32 (laidOutMemory p) ((reservedSP p).toNat+24)=p.size ∧
    readI32 (laidOutMemory p) ((reservedSP p).toNat+28)=1 := by
  have bounds := setup_bounds p hn
  have words := AllocateLayoutWrapper.final_spec (layout685 p) hn.allocation.wf hn.allocation.width bounds.1 bounds.2
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have outEq : (layout685 p).out.toNat=(reservedSP p).toNat+24 := by
    rw [nums.2.2.2.1,nums.1];omega
  have low : readI32 (laidOutMemory p) ((reservedSP p).toNat+24)=p.size := by
    unfold laidOutMemory
    rw [←outEq]
    exact words.2.2.2.1
  have high : readI32 (laidOutMemory p) ((reservedSP p).toNat+28)=1 := by
    unfold laidOutMemory
    rw [show (reservedSP p).toNat+28=(layout685 p).out.toNat+4 by rw [outEq]]
    exact words.2.2.2.2
  exact ⟨low,high⟩

theorem setup_load_bounds (p : Layout) (hn : Native p) :
    (reservedSP p).toNat+28+4≤(laidOutMemory p).byteSize := by
  have shape := setup_spec p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  rw [shape.2.1,nums.1]
  omega
end WNear.Proofs.AllocateVector
