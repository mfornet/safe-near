import Proofs.StateDecodeBorshReadIntervalFrame
import Proofs.StateDecodeBorshWrapperAllocatedFrame

/-! The actual161 copies frame the allocation performed by its prepared decoder. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] setupMemory wrappedMemory finalMemory
  StateDecodePrefix.allocatedMemory StateDecodePrefix.count count readI32 readI64 writeI32 writeI64
theorem finalMemory_allocated_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hstack:p.sp161.toNat≤j)
    (hout:j<p.out161.toNat ∨p.out161.toNat+48≤j):
    (finalMemory p q).read8 j=(StateDecodePrefix.allocatedMemory (actualWrapper p).toPrefix (actualAllocation p q)).read8 j:=by
  have n:=scratch_numbers p hn
  have geo:=stack_geometry p hn
  have child:=StateDecodeBorshWrapper.finalMemory_allocated_frame (actualWrapper p) (actualAllocation p q)
    (wrapper_native p hn) (accepted_domain p q hn hd) j (by change p.sp162.toNat≤j;omega)
    (by change j<p.out162.toNat ∨p.out162.toNat+48≤j;right;omega)
    (by change j<p.slice.toNat ∨p.slice.toNat+8≤j;right;omega)
  have folded:(wrappedMemory p q).read8 j=(StateDecodePrefix.allocatedMemory (actualWrapper p).toPrefix (actualAllocation p q)).read8 j:=by
    simpa only[wrappedMemory] using child
  exact (finalMemory_wrapped_interval p q hn hd j hstack hout).trans folded
end WNear.Proofs.StateDecodeBorshRead
