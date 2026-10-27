import Proofs.AllocateLayoutWrapperResult

/-! Byte-preserving packed loads and the actual layout wrapper's output words. -/
namespace WNear.Proofs.AllocateLayoutWrapperReadback
open Wasm Wasm.Near MeteredLogic

/-- Re-encoding the actual little-endian load recovers every source byte. -/
theorem readI64_byte (memory : Memory) (address i : Nat) (hi : i < 8) :
    UInt8.ofNat ((readI64 memory address).toNat >>> (8 * i)) = memory.read8 (address + i) := by
  have bounds : ∀ j, (memory.read8 (address + j)).toNat < 256 := fun j => UInt8.toNat_lt _
  apply UInt8.toNat_inj.mp
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [readI64,List.range_succ,Nat.shiftRight_eq_div_pow] <;>
    have h0 := bounds 0 <;> have h1 := bounds 1 <;> have h2 := bounds 2 <;>
    have h3 := bounds 3 <;> have h4 := bounds 4 <;> have h5 := bounds 5 <;>
    have h6 := bounds 6 <;> have h7 := bounds 7 <;> simp only [Nat.add_zero] at * <;> omega

/-- A load snapshots all eight bytes before the write, including overlapping spans. -/
def packedCopy (memory : Memory) (out source : Nat) : Memory :=
  memory.writeRun out 8 fun i => UInt8.ofNat ((readI64 memory source).toNat >>> (8 * i))

theorem packedCopy_spec (memory : Memory) (out source : Nat) (hw : memory.wf)
    (hb : out + 8 ≤ memory.byteSize) :
    (packedCopy memory out source).wf ∧ (packedCopy memory out source).byteSize = memory.byteSize ∧
    (packedCopy memory out source).max = memory.max ∧
    ∀ j, (packedCopy memory out source).read8 j =
      if out ≤ j ∧ j < out + 8 then memory.read8 (source + (j - out)) else memory.read8 j := by
  have h := Memory.writeRun_spec hw hb (fun i => UInt8.ofNat ((readI64 memory source).toNat >>> (8 * i)))
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro j
  rw [show (packedCopy memory out source).read8 j = _ from h.2.2.2 j]
  split
  · rename_i hj
    rw [readI64_byte memory source (j-out) (by omega)]
  · rfl

theorem packedCopy_word (memory : Memory) (out source offset : Nat) (hw : memory.wf)
    (hb : out + 8 ≤ memory.byteSize) (ho : offset + 4 ≤ 8) :
    readI32 (packedCopy memory out source) (out + offset) = readI32 memory (source + offset) := by
  have spec := packedCopy_spec memory out source hw hb
  have bytes (i : Nat) (hi : i < 4) :
      (packedCopy memory out source).read8 (out + offset + i) = memory.read8 (source + offset + i) := by
    rw [spec.2.2.2]
    rw [ite_eq_left (show out ≤ out+offset+i ∧ out+offset+i < out+8 by omega)]
    congr 1
    omega
  have zero : (packedCopy memory out source).read8 (out + offset) = memory.read8 (source + offset) := by
    simpa only [Nat.add_zero] using bytes 0 (by decide)
  simp [readI32,List.range_succ,bytes,zero]

end WNear.Proofs.AllocateLayoutWrapperReadback

namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open AllocateLayoutWrapperReadback
attribute [local irreducible] readI32 writeI32

theorem laidOut_spec (p : Layout) (hw : p.memory.wf) (hwidth : p.memory.byteSize ≤ 2^32)
    (hb : (scratch p).toNat + 16 ≤ p.memory.byteSize) :
    (laidOutMemory p).wf ∧ (laidOutMemory p).byteSize = p.memory.byteSize ∧
    (laidOutMemory p).max = p.memory.max ∧
    readI32 (laidOutMemory p) (scratch p).toNat = p.size ∧
    readI32 (laidOutMemory p) ((scratch p).toNat + 4) = 1 := by
  have setup := setup_spec p hw hb
  have address : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have bound : (leafLayout p).out.toNat + 8 ≤ (leafLayout p).memory.byteSize := by
    change (scratch p).toNat + 8 ≤ (setupMemory p).byteSize
    rw [setup.2.1]
    omega
  have leaf := AllocateLayout.final_spec (leafLayout p) setup.1 bound
  have value : AllocateLayout.size (leafLayout p) = p.size := by
    simpa only [AllocateLayout.size,leafLayout,address] using setup.2.2.2.1
  exact ⟨leaf.1,leaf.2.1.trans setup.2.1,leaf.2.2.1.trans setup.2.2.1,
    leaf.2.2.2.1.trans value,leaf.2.2.2.2.1⟩

/-- The actual packed copy returns the requested size and alignment one.
Output may overlap any part of the scratch record. -/
theorem final_spec (p : Layout) (hw : p.memory.wf) (hwidth : p.memory.byteSize ≤ 2^32)
    (hs : (scratch p).toNat + 16 ≤ p.memory.byteSize) (ho : p.out.toNat + 8 ≤ p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize = p.memory.byteSize ∧
    (finalMemory p).max = p.memory.max ∧
    readI32 (finalMemory p) p.out.toNat = p.size ∧
    readI32 (finalMemory p) (p.out.toNat + 4) = 1 := by
  have l := laidOut_spec p hw hwidth hs
  have outBound : p.out.toNat + 8 ≤ (laidOutMemory p).byteSize := by rw [l.2.1]; exact ho
  have c := packedCopy_spec (laidOutMemory p) p.out.toNat (scratch p).toNat l.1 outBound
  have low := packedCopy_word (laidOutMemory p) p.out.toNat (scratch p).toNat 0 l.1 outBound (by decide)
  have high := packedCopy_word (laidOutMemory p) p.out.toNat (scratch p).toNat 4 l.1 outBound (by decide)
  have low' : readI32 (finalMemory p) p.out.toNat = p.size := by
    simpa only [finalMemory,packedCopy,Nat.add_zero] using low.trans (by simpa only [Nat.add_zero] using l.2.2.2.1)
  exact ⟨c.1,c.2.1.trans l.2.1,c.2.2.1.trans l.2.2.1,low',high.trans l.2.2.2.2⟩

theorem final_words_of_ready (s : Store NearState) (frame : CallFrame) (p : Layout) (hr : Ready s frame p) :
    readI32 (finalMemory p) p.out.toNat = p.size ∧ readI32 (finalMemory p) (p.out.toNat + 4) = 1 := by
  have h := final_spec p hr.wf hr.width hr.scratchBound hr.outBound
  exact ⟨h.2.2.2.1,h.2.2.2.2⟩

end WNear.Proofs.AllocateLayoutWrapper
