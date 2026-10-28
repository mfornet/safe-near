import Proofs.StateDecodePrefixWrapperBody

/-! Complete315 memory shape, including its final output tag store. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧(finalMemory p).byteSize=p.memory.byteSize ∧(finalMemory p).max=p.memory.max := by
  have specs:=memory_specs p hn
  have lb:p.out.toNat+4+8≤p.memory.byteSize:=by have h:=hn.outputBound;omega
  have low:=writeI64_spec p.memory (p.out.toNat+4) (lowValue p) hn.wf lb
  have hb:(p.out+12).toNat+4≤(lowMemory p).byteSize:=by rw[add_output p hn,specs.2.1];exact hn.outputBound
  have high:=writeI32_spec (lowMemory p) (p.out+12).toNat (highValue p) specs.1 hb
  have tb:p.out.toNat+4≤(highMemory p).byteSize:=by rw[specs.2.2.2];have h:=hn.outputBound;omega
  have tag:=writeI32_spec (highMemory p) p.out.toNat 0 specs.2.2.1 tb
  exact ⟨tag.1,tag.2.1.trans specs.2.2.2,tag.2.2.1.trans (high.2.2.1.trans low.2.2.1)⟩
end WNear.Proofs.StateDecodePrefixWrapper.Tail

namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic

theorem finalMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p)
    (hd : StateDecodePrefix.AcceptedDomain p.toPrefix q) :
    (finalMemory p q).wf ∧(finalMemory p q).byteSize=p.memory.byteSize ∧(finalMemory p q).max=p.memory.max := by
  have shape:=Tail.finalMemory_spec (tailLayout p q) (tail_native p q hn hd)
  have child:=StateDecodePrefix.finalMemory_spec p.toPrefix q hn.child hd.toAllocationDomain
  exact ⟨shape.1,shape.2.1.trans child.2.1,shape.2.2.trans child.2.2⟩
end WNear.Proofs.StateDecodePrefixWrapper
