import Proofs.AllocationGrowthRemainderRead

/-! The allocator root is outside435's exact borrow/copy/release footprint. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 readInputMemory readOutputMemory readFinalMemory actualVector AllocateRetry.finalMemory copiedMemory AllocateVectorOuter.remainderLayout AllocateVector.remainderLayout AllocateVectorOuter.finalMemory AllocateVector.result
 theorem read_final_protected_byte(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (j:Nat)(above:p.sp523.toNat≤j)
    (counterOutside:j<1074904 ∨1074908≤j)
    (before:j<(AllocateVector.result (actualVector p).toVector).toNat):
    (readFinalMemory p).read8 j=(readInputMemory p).read8 j:=by
  have snapshot:=read_snapshot p hn ha
  have sn:=snapshot.scratch_nat
  have num:=stack_numbers p hn
  have lower:=hn.spLower
  have bound:=hn.spBound
  have cellOriginal:=hn.threadBound
  have low:=StateReadRegisterOuterReadMemory.low_spec (readLayout p) snapshot.wf
    (by have:=snapshot.stateBound;omega) snapshot.scratch_bound
  have lowFrame:(StateDispatchRead.lowMemory (readLayout p)).read8 j=(readInputMemory p).read8 j:=by
    apply low.2.2.2 j counterOutside
    right;rw[sn];change (scratch p).toNat-16+16≤j;omega
  have pb:(StateDispatchRead.ptr (readLayout p)).toNat+p.bytes.length≤
      (StateDispatchRead.lowMemory (readLayout p)).byteSize:=by
    rw[snapshot.ptr_nat,snapshot.low_shape.2.1];exact snapshot.payloadBound
  have copy:=Memory.writeList_spec p.bytes (StateDispatchRead.lowMemory (readLayout p))
    (StateDispatchRead.ptr (readLayout p)).toNat low.1 pb
  have copyWf:(readOutputMemory p).wf:=by
    simpa only[readOutputMemory,StateDispatchRead.readMemory] using copy.1
  have copySize:(readOutputMemory p).byteSize=(readInputMemory p).byteSize:=by
    simpa only[readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.1.trans snapshot.low_shape.2.1
  have copied:(readOutputMemory p).read8 j=(StateDispatchRead.lowMemory (readLayout p)).read8 j:=by
    unfold readOutputMemory StateDispatchRead.readMemory
    rw[copy.2.2.2 j,ite_eq_right (by rw[snapshot.ptr_nat];omega)]
  have counter:readCounter p=1074904:=snapshot.counter
  have cell:1074916≤(readInputMemory p).byteSize:=snapshot.stateBound
  have releaseBound:(readCounter p).toNat+4≤(readOutputMemory p).byteSize:=by
    rw[counter,copySize];change 1074908≤(readInputMemory p).byteSize
    omega
  have release:=writeI32_spec (readOutputMemory p) (readCounter p).toNat
    (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295) copyWf releaseBound
  unfold readFinalMemory
  rw[release.2.2.2 j,ite_eq_right (by rw[counter];change ¬(1074904≤j ∧ j<1074908);rcases counterOutside with h|h <;> omega),copied,lowFrame]

 theorem allocated_pointer_above(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    p.memory.byteSize≤(AllocateVector.result (actualVector p).toVector).toNat:=by
  have payload:=AllocateVectorOuter.result_payload (actualVector p) (vector_native p hn ha)
  have old:=(lengthMemory_footprint p hn).2.1
  have h:(lengthMemory p).byteSize≤(AllocateVector.result (actualVector p).toVector).toNat:=by
    simpa only[actualVector,vectorMemoryTemplate] using payload.1
  exact old.symm.trans_le h

 theorem copiedMemory_root_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (output:p.out523.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out523.toNat):
    readI32 (copiedMemory p) p.allocator.toNat=readI32 (readInputMemory p) p.allocator.toNat:=by
  have head:=hn.allocation.allocatorBound
  have pointer:=allocated_pointer_above p hn ha
  have above:=hn.heapAbove
  apply readI32_congr_bytes
  intro i hi
  have copied:(copiedMemory p).read8 (p.allocator.toNat+i)=(readFinalMemory p).read8 (p.allocator.toNat+i):=
    (copiedMemory_spec p hn ha).2.2.2.2.2 _ (by rcases output with h|h <;> omega)
  have read:=read_final_protected_byte p hn ha (p.allocator.toNat+i) (by omega)
    (Or.inl (by rw[ha];change 1074896+i<1074904;omega)) (by omega)
  exact copied.trans read
end WNear.Proofs.StateReadRegisterOuter
