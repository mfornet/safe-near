import Proofs.StateDecodePrefixMemoryNative

/-! Complete selected316 memory shape follows the actual sequential stores;
no tag/payload separation is needed for well-formedness or size preservation. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧(finalMemory p).byteSize=p.memory.byteSize ∧(finalMemory p).max=p.memory.max := by
  have specs:=memory_specs p hn
  have highBound:(p.out+12).toNat+4≤p.memory.byteSize:=by rw[out_address p hn];exact hn.outBound
  have high:=writeI32_spec p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56)) hn.wf highBound
  have lowBound:p.out.toNat+4+8≤(highMemory p).byteSize:=by rw[specs.2.1];have h:=hn.outBound;omega
  have low:=writeI64_spec (highMemory p) (p.out.toNat+4) (readI64 (highMemory p) (p.scratch.toNat+48)) specs.1 lowBound
  have tagBound:p.out.toNat+4≤(lowMemory p).byteSize:=by rw[specs.2.2.2.1];have h:=hn.outBound;omega
  have tag:=writeI32_spec (lowMemory p) p.out.toNat 0 specs.2.2.1 tagBound
  have descriptorBound:p.slice.toNat+8≤(tagMemory p).byteSize:=by rw[specs.2.2.2.2.2];exact hn.sliceBound
  have final:=writeI64_spec (tagMemory p) p.slice.toNat (remainder p) specs.2.2.2.2.1 descriptorBound
  have hm:(tagMemory p).max=p.memory.max:=tag.2.2.1.trans (low.2.2.1.trans high.2.2.1)
  exact ⟨final.1,final.2.1.trans specs.2.2.2.2.2,final.2.2.1.trans hm⟩
end WNear.Proofs.StateDecodePrefix.Output

namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

theorem finalMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AllocationDomain p q) :
    (finalMemory p q).wf ∧(finalMemory p q).byteSize=p.memory.byteSize ∧(finalMemory p q).max=p.memory.max := by
  have final:=Output.finalMemory_spec (outputLayout p q) (output_native p q hn hd)
  have input:=droppedMemory_spec p q hn hd
  exact ⟨final.1,final.2.1.trans input.2.1,final.2.2.trans input.2.2⟩
end WNear.Proofs.StateDecodePrefix
