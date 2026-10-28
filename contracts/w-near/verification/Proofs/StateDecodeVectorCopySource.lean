import Proofs.StateDecodeVectorCopyState
import Proofs.StateDecodeRawOldFrame

/-! Source preservation is conditional on original heap/stack/output separation.
The operational373/374 domains themselves continue to permit arbitrary aliases. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] writeI32 writeI64 readI64

theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hstack : p.spVector.toNat≤j)
    (hheap : (StateDecodeRaw.originalFinish p.toRaw).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (hout : j<p.outVector.toNat ∨p.outVector.toNat+12≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have a:=allocated_spec p hn
  have nums:=stack_numbers p hn
  have e: (scratch p).toNat+16=p.spVector.toNat:=by
    have lo:=hn.spLower
    omega
  have hr:p.spRaw.toNat≤j:=by rw[nums.2.1];omega
  have ho:j<p.outRaw.toNat ∨p.outRaw.toNat+8≤j:=by rw[nums.2.2.1];omega
  have raw:=StateDecodeRaw.finalMemory_byte_frame p.toRaw hn.raw j hr hheap hroot ho
  have zb:p.outVector.toNat+8+4≤(memoryAllocated p).byteSize:=by rw[a.2.1];exact hn.outBound
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 zb
  have fb:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1];have h:=hn.outBound;omega
  have f:=writeI64_spec (zeroMemory p) p.outVector.toNat (packed p) z.1 fb
  have nf:¬(p.outVector.toNat≤j ∧j<p.outVector.toNat+8):=by omega
  have nz:¬(p.outVector.toNat+8≤j ∧j<p.outVector.toNat+8+4):=by omega
  calc
    (finalMemory p).read8 j=(zeroMemory p).read8 j:=by unfold finalMemory;rw[f.2.2.2];exact ite_eq_right nf
    _=(memoryAllocated p).read8 j:=by unfold zeroMemory;rw[z.2.2.2];exact ite_eq_right nz
    _=p.memory.read8 j:=raw
end WNear.Proofs.StateDecodeVector

namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic

theorem vector_source_bytes (p : Layout) (hn : Native p)
    (hstack : p.spVector.toNat≤p.source.toNat)
    (hheap : (StateDecodeRaw.originalFinish p.toVector.toRaw).toNat+8≤p.source.toNat)
    (hroot : p.source.toNat+p.size.toNat≤p.allocator.toNat ∨p.allocator.toNat+4≤p.source.toNat)
    (hout : p.source.toNat+p.size.toNat≤p.outVector.toNat ∨p.outVector.toNat+12≤p.source.toNat)
    (i : Nat) (hi : i<p.size.toNat) :
    (StateDecodeVector.finalMemory p.toVector).read8 (p.source.toNat+i)=p.memory.read8 (p.source.toNat+i) := by
  apply StateDecodeVector.finalMemory_byte_frame p.toVector hn.vector
  · omega
  · omega
  · rcases hroot with h|h <;> omega
  · rcases hout with h|h <;> omega

theorem destination_before_source (p : Layout) (hn : Native p)
    (hheap : (StateDecodeRaw.originalFinish p.toVector.toRaw).toNat+8≤p.source.toNat) :
    (pointer p).toNat+p.size.toNat≤p.source.toNat := by
  have h:=StateDecodeRaw.result_finish_bound p.toVector.toRaw hn.vector.raw
  change (StateDecodeRaw.result p.toVector.toRaw).toNat+p.size.toNat≤_
  omega
/-- The actual forward copy contains the original source snapshot. This is a
pre-final-length-write statement; that last write may itself alias the payload. -/
theorem copied_original_bytes (p : Layout) (hn : Native p)
    (hstack : p.spVector.toNat≤p.source.toNat)
    (hheap : (StateDecodeRaw.originalFinish p.toVector.toRaw).toNat+8≤p.source.toNat)
    (hroot : p.source.toNat+p.size.toNat≤p.allocator.toNat ∨p.allocator.toNat+4≤p.source.toNat)
    (hout : p.source.toNat+p.size.toNat≤p.outVector.toNat ∨p.outVector.toNat+12≤p.source.toNat)
    (i : Nat) (hi : i<p.size.toNat) :
    (copiedMemory p).read8 ((pointer p).toNat+i)=p.memory.read8 (p.source.toNat+i) := by
  have bounds:=copy_bounds p hn
  have sep:=destination_before_source p hn hheap
  have copied:=ForwardCopyMemory.copied_bytes (StateDecodeVector.finalMemory p.toVector)
    (pointer p).toNat p.source.toNat p.size.toNat bounds.1 bounds.2.2.2.2.1 (Or.inl sep) i hi
  exact copied.trans (vector_source_bytes p hn hstack hheap hroot hout i hi)

/-- Preserving copied payload through374's last store additionally excludes
that length word from the allocated destination span. -/
theorem final_original_bytes (p : Layout) (hn : Native p)
    (hstack : p.spVector.toNat≤p.source.toNat)
    (hheap : (StateDecodeRaw.originalFinish p.toVector.toRaw).toNat+8≤p.source.toNat)
    (hroot : p.source.toNat+p.size.toNat≤p.allocator.toNat ∨p.allocator.toNat+4≤p.source.toNat)
    (hout : p.source.toNat+p.size.toNat≤p.outVector.toNat ∨p.outVector.toNat+12≤p.source.toNat)
    (hlength : (pointer p).toNat+p.size.toNat≤p.outVector.toNat+8 ∨p.outVector.toNat+12≤(pointer p).toNat)
    (i : Nat) (hi : i<p.size.toNat) :
    (finalMemory p).read8 ((pointer p).toNat+i)=p.memory.read8 (p.source.toNat+i) := by
  have bounds:=copy_bounds p hn
  have shape:=ForwardCopyMemory.spec (StateDecodeVector.finalMemory p.toVector)
    (pointer p).toNat p.source.toNat p.size.toNat bounds.1 bounds.2.2.2.2.1
  have hb:p.outVector.toNat+8+4≤(copiedMemory p).byteSize:=by
    change _≤(ForwardCopyMemory.forward _ _ _ _).byteSize
    rw[shape.2.1,bounds.2.1]
    exact hn.vector.outBound
  have write:=writeI32_spec (copiedMemory p) (p.outVector.toNat+8) p.size shape.1 hb
  have no:¬(p.outVector.toNat+8≤(pointer p).toNat+i ∧(pointer p).toNat+i<p.outVector.toNat+8+4):=by
    rcases hlength with h|h <;> omega
  calc
    _=(copiedMemory p).read8 ((pointer p).toNat+i):=by unfold finalMemory;rw[write.2.2.2];exact ite_eq_right no
    _=p.memory.read8 (p.source.toNat+i):=copied_original_bytes p hn hstack hheap hroot hout i hi

end WNear.Proofs.StateDecodeVectorCopy
