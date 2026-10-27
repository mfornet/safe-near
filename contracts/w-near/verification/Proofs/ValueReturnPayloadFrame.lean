import Proofs.ValueReturnOuterLayout
import Proofs.ValueReturnSlice

/-! Original-payload preservation through both actual wrapper and outer writes.
Every claimed snapshot equality retains explicit span-disjointness premises. -/
namespace WNear.Proofs.ValueReturnPayloadFrame
open Wasm Wasm.Near MeteredLogic
open ValueReturnOuterBody

/-- Saving the slice writes only the two four-byte words at scratch+8/+12. -/
theorem slice_payload_frame (memory : Memory) (scratch pointer length : UInt32)
    (address count : Nat) (hwf : memory.wf)
    (hspan : scratch.toNat + 16 ≤ memory.byteSize)
    (hdisjoint : address + count ≤ scratch.toNat + 8 ∨ scratch.toNat + 16 ≤ address) :
    (ValueReturnWrapper.sliceMemory memory scratch pointer length).readList address count =
      memory.readList address count := by
  have hs := ValueReturnSlice.sliceMemory_spec memory scratch pointer length hwf hspan
  apply ValueReturnOuterLayout.readList_frame
  intro i hi
  exact hs.2.2.2.2.2 (address + i) (by omega)

/-- The exact payload supplied to the host after both scratch regions and the
counter write is the original payload, under the three explicit interval frames.
The payload itself needs no bounds premise for this total-reader equality. -/
theorem outer_payload_frame (memory : Memory) (wrapperScratch pointer length : UInt32)
    (p : Layout)
    (hprepared : p.memory = ValueReturnWrapper.sliceMemory memory wrapperScratch pointer length)
    (hwf : memory.wf) (hwrapper : wrapperScratch.toNat + 16 ≤ memory.byteSize)
    (hcell : 1074904 + 4 ≤ memory.byteSize)
    (houter : (scratch p).toNat + 16 ≤ memory.byteSize)
    (hcounter : pointer.toNat + length.toNat ≤ 1074904 ∨ 1074908 ≤ pointer.toNat)
    (hscratch : pointer.toNat + length.toNat ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ pointer.toNat)
    (hslice : pointer.toNat + length.toNat ≤ wrapperScratch.toNat + 8 ∨ wrapperScratch.toNat + 16 ≤ pointer.toNat) :
    (lowMemory p).readList pointer.toNat length.toNat = memory.readList pointer.toNat length.toNat := by
  have hs := ValueReturnSlice.sliceMemory_spec memory wrapperScratch pointer length hwf hwrapper
  have hpwf : p.memory.wf := by rw [hprepared]; exact hs.1
  have hsize : p.memory.byteSize = memory.byteSize := by rw [hprepared]; exact hs.2.1
  have hcell' : 1074904 + 4 ≤ p.memory.byteSize := by rw [hsize]; exact hcell
  have houter' : (scratch p).toNat + 16 ≤ p.memory.byteSize := by rw [hsize]; exact houter
  have hlow := ValueReturnOuterLayout.lowMemory_payload_frame p pointer.toNat length.toNat
    hpwf hcell' houter' hcounter hscratch
  rw [hlow, hprepared]
  exact slice_payload_frame memory wrapperScratch pointer length pointer.toNat length.toNat hwf hwrapper hslice

end WNear.Proofs.ValueReturnPayloadFrame
