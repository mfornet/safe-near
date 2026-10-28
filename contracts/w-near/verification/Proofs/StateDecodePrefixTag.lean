import Proofs.StateDecodePrefixMemoryNative
import Proofs.AllocateSplitReadback

/-! The output tag is stored before the slice descriptor. Its final zero value
therefore requires the original tag word and descriptor span to be disjoint. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_tag0 (p : Layout) (hn : Native p)
    (hsep : p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat) :
    readI32 (finalMemory p) p.out.toNat=0 := by
  have specs:=memory_specs p hn
  have lowWf: (lowMemory p).wf:=specs.2.2.1
  have lowSize: (lowMemory p).byteSize=p.memory.byteSize:=specs.2.2.2.1
  have tagWf: (tagMemory p).wf:=specs.2.2.2.2.1
  have tagSize: (tagMemory p).byteSize=p.memory.byteSize:=specs.2.2.2.2.2
  have tagBound:p.out.toNat+4≤(lowMemory p).byteSize:=by rw[lowSize];have h:=hn.outBound;omega
  have tag:=PanicAllocateReadback.read_write_self (lowMemory p) p.out.toNat 0 lowWf tagBound
  have descriptorBound:p.slice.toNat+8≤(tagMemory p).byteSize:=by rw[tagSize];exact hn.sliceBound
  have written:=writeI64_spec (tagMemory p) p.slice.toNat (remainder p) tagWf descriptorBound
  have same:readI32 (finalMemory p) p.out.toNat=readI32 (tagMemory p) p.out.toNat:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    have no:¬(p.slice.toNat≤p.out.toNat+i ∧p.out.toNat+i<p.slice.toNat+8):=by
      rcases hsep with h|h <;> omega
    unfold finalMemory
    rw[written.2.2.2]
    exact ite_eq_right no
  exact same.trans tag
end WNear.Proofs.StateDecodePrefix.Output

namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

/-- Full316 tag readback, from original accepted domain and tag/slice separation. -/
theorem finalMemory_tag0 (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q)
    (hsep : p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat) :
    readI32 (finalMemory p q) p.out.toNat=0 :=
  Output.finalMemory_tag0 (outputLayout p q) (output_native p q hn hd.toAllocationDomain) hsep
end WNear.Proofs.StateDecodePrefix
