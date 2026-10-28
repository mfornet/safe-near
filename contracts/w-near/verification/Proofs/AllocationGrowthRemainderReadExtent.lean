import Proofs.AllocationGrowthRemainderRegisterFacts

/-! The read/counter/result-copy suffix preserves the exact grown memory extent. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 readInputMemory readOutputMemory readFinalMemory copiedMemory finalMemory AllocateRetry.finalMemory

 theorem readFinalMemory_byteSize(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (readFinalMemory p).byteSize=(readInputMemory p).byteSize:=by
  have snapshot:=read_snapshot p hn ha
  have low:=snapshot.low_shape
  have payload:(StateDispatchRead.ptr (readLayout p)).toNat+p.bytes.length≤(StateDispatchRead.lowMemory (readLayout p)).byteSize:=by
    rw[snapshot.ptr_nat,low.2.1];exact snapshot.payloadBound
  have copy:=Memory.writeList_spec p.bytes (StateDispatchRead.lowMemory (readLayout p))
    (StateDispatchRead.ptr (readLayout p)).toNat low.1 payload
  have copySize:(readOutputMemory p).byteSize=(readInputMemory p).byteSize:=by
    simpa only[readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.1.trans low.2.1
  have copyWf:(readOutputMemory p).wf:=by
    simpa only[readOutputMemory,StateDispatchRead.readMemory] using copy.1
  have counter:readCounter p=1074904:=snapshot.counter
  have cell:1074916≤(readInputMemory p).byteSize:=snapshot.stateBound
  have bound:(readCounter p).toNat+4≤(readOutputMemory p).byteSize:=by
    rw[counter,copySize];change 1074908≤(readInputMemory p).byteSize;omega
  have release:=writeI32_spec (readOutputMemory p) (readCounter p).toNat
    (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295) copyWf bound
  unfold readFinalMemory
  exact release.2.1.trans copySize

 theorem copiedMemory_read_byteSize(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (copiedMemory p).byteSize=(readInputMemory p).byteSize:=by
  have shape:=readFinalMemory_spec p hn ha
  have bounds:=copy_bounds p hn
  have copy:=finalMemory_shape (readFinalMemory p) p.out523 (scratch p) shape.1
    (bounds.2.2.2.1.trans shape.2.1) (bounds.2.2.2.2.2.trans shape.2.1)
  unfold copiedMemory
  exact copy.2.1.trans (readFinalMemory_byteSize p hn ha)

 theorem readInputMemory_remainder_size(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (readInputMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=by
  have h:=AllocateVectorOuter.finalMemory_remainder_size (actualVector p) (vector_native p hn ha)
  unfold AllocateVectorOuter.remainderLayout at h
  unfold readInputMemory remainderLayout
  exact h

 theorem copiedMemory_remainder_size(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (copiedMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=
  (copiedMemory_read_byteSize p hn ha).trans (readInputMemory_remainder_size p hn ha)
end WNear.Proofs.StateReadRegisterOuter
