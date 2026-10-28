import Proofs.StateDecodeVectorCopySource
import Proofs.StateDecodeRawIntervalFrame

/-! Actual373 frames bytes outside either side of its original heap interval. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] writeI32 writeI64 readI64

theorem finalMemory_interval_frame (p : Layout) (hn : Native p) (j : Nat)
    (hstack : p.spVector.toNat≤j)
    (hheap : j<(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat ∨ (StateDecodeRaw.originalFinish p.toRaw).toNat+8≤j)
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
  have raw:=StateDecodeRaw.finalMemory_interval_frame p.toRaw hn.raw j hr hheap hroot ho
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
