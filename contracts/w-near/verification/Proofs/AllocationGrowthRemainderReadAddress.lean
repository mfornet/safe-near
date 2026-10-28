import Proofs.AllocationGrowthRemainderRootAddress

/-! The actual523 input heap names its freshly appended page as free head. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readInputMemory actualVector AllocateVectorOuter.finalMemory

 theorem readInputMemory_root_nat(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (readI32 (readInputMemory p) p.allocator.toNat).toNat=p.memory.byteSize:=by
  have vn:=vector_native p hn ha
  have nums:=stack_numbers p hn
  have vnums:=AllocateVectorOuter.stack_numbers (actualVector p) vn
  have lo:=hn.spLower
  have vlo:=vn.spLower
  have heap:=hn.heapAbove
  have va:(actualVector p).allocator=p.allocator:=by simp only[actualVector,vectorMemoryTemplate]
  have vsp:(actualVector p).sp687=scratch p:=by simp only[actualVector,vectorMemoryTemplate];exact hn.vectorSP
  have vo:(actualVector p).out687=scratch p+32:=by simp only[actualVector,vectorMemoryTemplate];exact hn.vectorOut
  have inner:(actualVector p).out686.toNat+8≤(actualVector p).allocator.toNat:=by
    rw[vnums.2.2,va,vsp,nums.1];omega
  have outer:(actualVector p).out687.toNat+12≤(actualVector p).allocator.toNat:=by
    rw[vo,va,nums.2.2.2.2];omega
  have result:=AllocateVectorOuter.finalMemory_root_nat (actualVector p) vn (Or.inl inner) (Or.inl outer)
  have old:(actualVector p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualVector,vectorMemoryTemplate];exact (lengthMemory_footprint p hn).2.1
  rw[va,old] at result
  unfold readInputMemory
  exact result
end WNear.Proofs.StateReadRegisterOuter
