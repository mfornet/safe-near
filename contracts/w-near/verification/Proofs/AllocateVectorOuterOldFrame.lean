import Proofs.AllocateVectorOldFrame
import Proofs.AllocateVectorOuterResult

/-! Old-memory byte and word frames for the actual growing f687 call. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 finalMemory

theorem finalMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.memory.byteSize) (hsp : p.sp687.toNat≤j)
    (ha : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j)
    (ho : j<p.out687.toNat ∨ p.out687.toNat+12≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have child := hn.vector p
  have shape := AllocateVector.finalMemory_spec p.toVector child
  have span := AllocateVector.resultMemory_spec p.toVector child
  have hb : p.out687.toNat+12≤(allocatedMemory p).byteSize := by
    change p.out687.toNat+12≤(AllocateVector.finalMemory p.toVector).byteSize
    rw [shape.2.1]
    exact hn.outputBound.trans span.2.1
  have copy := outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1 hb
  unfold finalMemory
  rw [copy.2.2.2.2.2 j ho]
  have nums := stack_numbers p hn
  have lower := hn.spLower
  exact AllocateVector.finalMemory_old_frame p.toVector child j hj (by omega) ha
    (Or.inr (by rw [nums.2.2];omega))

theorem finalMemory_old_word (p : Layout) (hn : Native p) (address : Nat)
    (hb : address+4≤p.memory.byteSize) (hsp : p.sp687.toNat≤address)
    (ha : address+4≤p.allocator.toNat ∨ p.allocator.toNat+4≤address)
    (ho : address+4≤p.out687.toNat ∨ p.out687.toNat+12≤address) :
    readI32 (finalMemory p) address=readI32 p.memory address := by
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  exact finalMemory_old_frame p hn (address+i) (by omega) (by omega) (by omega) (by omega)

theorem finalMemory_old_word64 (p : Layout) (hn : Native p) (address : Nat)
    (hb : address+8≤p.memory.byteSize) (hsp : p.sp687.toNat≤address)
    (ha : address+8≤p.allocator.toNat ∨ p.allocator.toNat+4≤address)
    (ho : address+8≤p.out687.toNat ∨ p.out687.toNat+12≤address) :
    readI64 (finalMemory p) address=readI64 p.memory address := by
  apply Wasm.Near.MeteredLogic.readI64_congr_bytes
  intro i hi
  exact finalMemory_old_frame p hn (address+i) (by omega) (by omega) (by omega) (by omega)
end WNear.Proofs.AllocateVectorOuter
