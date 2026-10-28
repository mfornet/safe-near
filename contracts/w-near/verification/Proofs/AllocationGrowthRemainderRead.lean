import Proofs.AllocationGrowthRemainderFlags
import Proofs.StateReadRegisterOuterReadRecord
import Proofs.StateReadRegisterOuterOutput

/-! The real435 register copy and counter release keep the new-page free
remainder before the payload; both writes and the borrow footprint are retained. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 readInputMemory readOutputMemory readFinalMemory actualVector AllocateRetry.finalMemory copiedMemory AllocateVectorOuter.remainderLayout AllocateVector.remainderLayout AllocateVectorOuter.finalMemory AllocateVector.result

 theorem read_final_remainder_byte(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (j:Nat)(above:p.memory.byteSize≤j)
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
    apply low.2.2.2 j (Or.inr (by omega))
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
  rw[release.2.2.2 j,ite_eq_right (by rw[counter];change ¬(1074904≤j ∧ j<1074908);omega),copied,lowFrame]

 theorem copiedMemory_remainder_byte(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (j:Nat)(above:p.memory.byteSize≤j)
    (before:j<(AllocateVector.result (actualVector p).toVector).toNat):
    (copiedMemory p).read8 j=
      (AllocateRetry.finalMemory (AllocateVector.remainderLayout (actualVector p).toVector)).read8 j:=by
  have bound:=hn.outputBound
  have copy:(copiedMemory p).read8 j=(readFinalMemory p).read8 j:=
    (copiedMemory_spec p hn ha).2.2.2.2.2 j (Or.inr (by omega))
  have read:=read_final_remainder_byte p hn ha j above before
  have shape:=(lengthMemory_footprint p hn).2.1
  have above':(actualVector p).memory.byteSize≤j:=by
    simp only[actualVector,vectorMemoryTemplate]
    rw[shape];exact above
  have vector:(readInputMemory p).read8 j=
      (AllocateRetry.finalMemory (AllocateVector.remainderLayout (actualVector p).toVector)).read8 j:=by
    unfold readInputMemory
    exact AllocateVectorOuter.finalMemory_new_remainder (actualVector p) (vector_native p hn ha) j above' before
  exact copy.trans (read.trans vector)
end WNear.Proofs.StateReadRegisterOuter
