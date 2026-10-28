import Proofs.StateReadRegisterOuterOutput

/-! The returned allocation contains the original register bytes. Its fresh
payload lies beyond every original-memory counter and final result write. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 readFinalMemory readOutputMemory copiedMemory AllocateVector.result actualVector

theorem copiedMemory_payload (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (i : Nat) (hi : i<p.bytes.length) :
    (copiedMemory p).read8 ((AllocateVector.result (actualVector p).toVector).toNat+i)=p.bytes[i]! := by
  have snapshot := read_snapshot p hn ha
  have low := snapshot.low_shape
  have fresh := AllocateVectorOuter.result_payload (actualVector p) (vector_native p hn ha)
  have length := lengthMemory_footprint p hn
  have pointerAbove : p.memory.byteSize≤(AllocateVector.result (actualVector p).toVector).toNat := by
    simpa only [show (actualVector p).memory=lengthMemory p from by simp only [actualVector,vectorMemoryTemplate],length.2.1] using fresh.1
  have ptrEq := snapshot.ptr_nat
  have pb : (StateDispatchRead.ptr (readLayout p)).toNat+p.bytes.length≤(StateDispatchRead.lowMemory (readLayout p)).byteSize := by
    rw [ptrEq,low.2.1];exact snapshot.payloadBound
  have copy := Memory.writeList_spec p.bytes (StateDispatchRead.lowMemory (readLayout p))
    (StateDispatchRead.ptr (readLayout p)).toNat low.1 pb
  have copyWf : (readOutputMemory p).wf := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory] using copy.1
  have copySize : (readOutputMemory p).byteSize=(readInputMemory p).byteSize := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.1.trans low.2.1
  have counter : readCounter p=1074904 := snapshot.counter
  have bound : (readCounter p).toNat+4≤(readOutputMemory p).byteSize := by
    rw [counter,copySize];change 1074908≤(readInputMemory p).byteSize
    have cell : 1074916≤(readInputMemory p).byteSize := snapshot.stateBound
    omega
  have release := writeI32_spec (readOutputMemory p) (readCounter p).toNat
    (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295) copyWf bound
  have actual : (readFinalMemory p).read8 ((AllocateVector.result (actualVector p).toVector).toNat+i)=p.bytes[i]! := by
    unfold readFinalMemory
    rw [release.2.2.2,ite_eq_right (by rw [counter];change ¬(1074904≤_ ∧ _<1074908);have := hn.threadBound;omega)]
    unfold readOutputMemory StateDispatchRead.readMemory
    rw [copy.2.2.2,ptrEq,ite_eq_left (by omega),Nat.add_sub_cancel_left]
  rw [(copiedMemory_spec p hn ha).2.2.2.2.2 _ (Or.inr (by have := hn.outputBound;omega))]
  exact actual
end WNear.Proofs.StateReadRegisterOuter
