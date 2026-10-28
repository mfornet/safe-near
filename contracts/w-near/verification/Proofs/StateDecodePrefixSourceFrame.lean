import Proofs.StateDecodePrefixRecord
import Proofs.StateDecodeVectorCopyIntervalFrame

/-! Original bytes beyond the selected free block survive316's allocation,
copy, scratch updates and final writes under their explicit byte exclusions. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic

theorem finalMemory_after_end (p : Layout) (hn : Native p) (j : Nat)
    (hstack : p.spVector.toNat≤j)
    (hheap : (StateDecodeRaw.originalFinish p.toRaw).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (hout : j<p.outVector.toNat ∨p.outVector.toNat+12≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have vector:=StateDecodeVector.finalMemory_interval_frame p.toVector hn.vector j hstack (Or.inr hheap) hroot hout
  have bound:=StateDecodeRaw.result_finish_bound p.toRaw hn.vector.raw
  have after:(pointer p).toNat+p.size.toNat≤j:=by exact Nat.le_trans bound (by omega)
  have copy: (copiedMemory p).read8 j=(StateDecodeVector.finalMemory p.toVector).read8 j:=
    (copiedMemory_spec p hn).2.2.2 j (Or.inr after)
  have last: (finalMemory p).read8 j=(copiedMemory p).read8 j:=
    (finalMemory_spec p hn).2.2.2.2 j (by rcases hout with h|h <;> omega)
  exact last.trans (copy.trans vector)
end WNear.Proofs.StateDecodeVectorCopy

namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 allocatedMemory droppedMemory takenPayloadMemory lengthMemory advancedMemory droppedFourMemory takenFourMemory readI64 writeI32 writeI64

theorem allocatedMemory_source_frame (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (j : Nat) (hstack : p.sp.toNat≤j)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤j)
    (hroot : j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (allocatedMemory p q).read8 j=p.memory.read8 j := by
  have native:=allocation_copy_native p q hn hd
  have endsp:=scratch_end p hn
  have sp:(allocationInput p q).spVector.toNat=(scratch p).toNat:=congrArg UInt32.toNat hd.sp
  have out:(allocationInput p q).outVector.toNat=(scratch p).toNat+48:=by change q.outVector.toNat=_;rw[hd.out];exact scratch_add p hn 48 (by omega)
  have heap:(StateDecodeRaw.originalFinish (allocationInput p q).toRaw).toNat+8≤j:=by rw[allocation_finish_eq p q hn hd];exact hheap
  have after:=StateDecodeVectorCopy.finalMemory_after_end (allocationInput p q) native j
    (by rw[sp];omega) heap hroot (Or.inr (by rw[out];omega))
  unfold allocatedMemory
  exact after.trans (takenPayload_byte_frame p hn j hstack hslice)

theorem finalMemory_source_frame (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (j : Nat) (hstack : p.sp.toNat≤j)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤j)
    (hroot : j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout : j<p.out.toNat ∨p.out.toNat+16≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (finalMemory p q).read8 j=p.memory.read8 j := by
  have a:=allocatedMemory_spec p q hn hd
  have add:(dropPayloadOut p).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have endsp:=scratch_end p hn
  have bound:(dropPayloadOut p).toNat+8≤(allocatedMemory p q).byteSize:=by rw[add,a.2.1];have h:=hn.spBound;omega
  have drop:=StateDecodeSlices.finalMemory_spec true (allocatedMemory p q) (dropPayloadOut p)
    (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p) a.1 bound
  have no1:¬((dropPayloadOut p).toNat≤j ∧j<(dropPayloadOut p).toNat+4):=by rw[add];omega
  have no2:¬((dropPayloadOut p).toNat+4≤j ∧j<(dropPayloadOut p).toNat+8):=by rw[add];omega
  have df:(droppedMemory p q).read8 j=(allocatedMemory p q).read8 j:=by
    unfold droppedMemory
    rw[drop.2.2.2]
    simp only[ite_eq_right no1,ite_eq_right no2]
  have output:=Output.finalMemory_byte_frame (outputLayout p q) (output_native p q hn hd) j hout hslice
  exact output.trans (df.trans (allocatedMemory_source_frame p q hn hd j hstack hheap hroot hslice))
end WNear.Proofs.StateDecodePrefix
