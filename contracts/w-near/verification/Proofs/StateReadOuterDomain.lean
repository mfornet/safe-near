import Proofs.StateReadOuterHeap

/-! The complete actual161 accepted domain follows from original219 data.
All allocator Native and saved-head facts are derived, not future inputs. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 packedMemory actualAllocation actualDecoder

 theorem allocation_head_above(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (bytes:p.bytes=WNear.header state):
    (actualDecoder p).sp161.toNat≤
      (AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p).toPositive)).toNat:=by
  have native:=allocation_native p hn state hw bytes
  have pos:=native.vector.raw.allocation
  have head:=AllocatePositive.saved_head_original (actualAllocation p).toPositive pos.wf pos.spLower pos.spBound
  have root:(actualAllocation p).allocator=p.allocator:=by
    simp only[actualAllocation];exact hn.allocationRoot
  have memory:(actualAllocation p).memory=packedMemory p:=actualAllocation_memory p
  have nat:(readI32 (actualAllocation p).memory (actualAllocation p).allocator.toNat).toNat=p.memory.byteSize:=by
    rw[memory,root];exact packed_root_nat p hn
  have sp:(actualDecoder p).sp161=scratch p:=by simp only[actualDecoder];exact hn.decoderSP
  rw[head,nat,sp]
  have nums:=scratch_numbers p hn
  have bound:=hn.spBound
  omega

/-- No original nonempty allocator domain is assumed:548 starts with an empty
head, grows memory, and the derived remainder supplies this actual161 domain. -/
 theorem decoder_domain(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (bytes:p.bytes=WNear.header state):
    StateDecodeBorshRead.AcceptedDomain (actualDecoder p) (actualAllocation p):=by
  have native:=allocation_native p hn state hw bytes
  have geo:=actualAllocation_geometry p hn
  have nums:=scratch_numbers p hn
  have cb:=hn.callbackAbove
  have sp:(actualDecoder p).sp161=scratch p:=by simp only[actualDecoder];exact hn.decoderSP
  have root:(actualAllocation p).allocator=p.allocator:=by simp only[actualAllocation];exact hn.allocationRoot
  refine {
    original:=native
    memory:=?_
    size:=?_
    sp:=geo.vectorSP
    out:=geo.vectorOut
    source:=?_
    allocatorAbove:=?_
    headAbove:=allocation_head_above p hn state hw bytes
    callbackAbove:=?_
    module:=?_
    memoryIndex:=?_
    globalIndex:=?_
    global:=geo.vectorGlobal }
  · rw[actualAllocation_memory,actualDecoder_memory]
  · simp only[actualAllocation_size,decodeCount]
  · simp only[actualAllocation]
  · rw[sp,root,hn.allocator]
    change (scratch p).toNat≤1074896
    omega
  · rw[sp];omega
  · simp only[actualAllocation,actualDecoder]
    exact hn.allocationModule.trans hn.decoderModule.symm
  · simp only[actualAllocation,actualDecoder]
    exact hn.allocationMemoryIndex.trans hn.decoderMemoryIndex.symm
  · simp only[actualAllocation,actualDecoder]
    exact hn.allocationGlobalIndex.trans hn.decoderGlobalIndex.symm
end WNear.Proofs.StateReadOuter
