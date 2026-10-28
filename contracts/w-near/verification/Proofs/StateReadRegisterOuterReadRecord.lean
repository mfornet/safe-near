import Proofs.StateReadRegisterOuterReadResult
import NearVM.MemoryListWordRules

/-! The actual687 record remains intact through435's borrow, fresh payload copy,
and counter release. No output-copy alias assumption is used at this stage. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 readInputMemory readOutputMemory readFinalMemory actualVector AllocateVectorOuter.finalMemory AllocateVector.result

theorem read_final_stack_byte (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (j : Nat) (hj : (scratch p).toNat≤j) (hupper : j<p.sp523.toNat) :
    (readFinalMemory p).read8 j=(readInputMemory p).read8 j := by
  have snapshot := read_snapshot p hn ha
  have sn := snapshot.scratch_nat
  have num := stack_numbers p hn
  have lower := hn.spLower
  have static := hn.staticAbove
  have bound := hn.spBound
  have low := StateReadRegisterOuterReadMemory.low_spec (readLayout p) snapshot.wf
    (by have := snapshot.stateBound;omega) snapshot.scratch_bound
  have lowFrame : (StateDispatchRead.lowMemory (readLayout p)).read8 j=(readInputMemory p).read8 j := by
    exact low.2.2.2 j (Or.inl (by omega)) (Or.inr (by rw [sn];change (scratch p).toNat-16+16≤j;omega))
  have native := vector_native p hn ha
  have payload := AllocateVectorOuter.result_payload (actualVector p) native
  have old := lengthMemory_footprint p hn
  have pointerAbove : p.memory.byteSize≤(StateDispatchRead.ptr (readLayout p)).toNat := by
    rw [snapshot.ptr_nat]
    simpa only [show (actualVector p).memory=lengthMemory p from by simp only [actualVector,vectorMemoryTemplate],old.2.1] using payload.1
  have pb : (StateDispatchRead.ptr (readLayout p)).toNat+p.bytes.length≤(StateDispatchRead.lowMemory (readLayout p)).byteSize := by
    rw [snapshot.ptr_nat,snapshot.low_shape.2.1];exact snapshot.payloadBound
  have copy := Memory.writeList_spec p.bytes (StateDispatchRead.lowMemory (readLayout p))
    (StateDispatchRead.ptr (readLayout p)).toNat low.1 pb
  have copyWf : (readOutputMemory p).wf := by simpa only [readOutputMemory,StateDispatchRead.readMemory] using copy.1
  have copySize : (readOutputMemory p).byteSize=(readInputMemory p).byteSize := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.1.trans snapshot.low_shape.2.1
  have copied : (readOutputMemory p).read8 j=(StateDispatchRead.lowMemory (readLayout p)).read8 j := by
    unfold readOutputMemory StateDispatchRead.readMemory
    rw [copy.2.2.2 j,ite_eq_right (by omega)]
  have counter : readCounter p=1074904 := snapshot.counter
  have cell : 1074916≤(readInputMemory p).byteSize := snapshot.stateBound
  have releaseBound : (readCounter p).toNat+4≤(readOutputMemory p).byteSize := by
    rw [counter,copySize];change 1074908≤(readInputMemory p).byteSize;omega
  have release := writeI32_spec (readOutputMemory p) (readCounter p).toNat
    (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295) copyWf releaseBound
  unfold readFinalMemory
  rw [release.2.2.2 j,ite_eq_right (by rw [counter];change ¬(1074904≤j ∧ j<1074908);omega),copied,lowFrame]

theorem read_final_stack_word (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (address : Nat) (hj : (scratch p).toNat≤address) (hupper : address+4≤p.sp523.toNat) :
    readI32 (readFinalMemory p) address=readI32 (readInputMemory p) address := by
  apply readI32_congr_bytes
  intro i hi
  exact read_final_stack_byte p hn ha (address+i) (by omega) (by omega)

theorem read_final_stack_word64 (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (address : Nat) (hj : (scratch p).toNat≤address) (hupper : address+8≤p.sp523.toNat) :
    readI64 (readFinalMemory p) address=readI64 (readInputMemory p) address := by
  apply readI64_congr_bytes
  intro i hi
  exact read_final_stack_byte p hn ha (address+i) (by omega) (by omega)

theorem read_final_record (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI32 (readFinalMemory p) ((scratch p).toNat+32)=AllocateVector.result (actualVector p).toVector ∧
    readI32 (readFinalMemory p) ((scratch p).toNat+36)=p.size ∧
    readI32 (readFinalMemory p) ((scratch p).toNat+40)=p.size ∧
    readI64 (readFinalMemory p) ((scratch p).toNat+32)=readI64 (readInputMemory p) ((scratch p).toNat+32) := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have record := AllocateVectorOuter.final_record (actualVector p) (vector_native p hn ha)
  have out : (actualVector p).out687.toNat=(scratch p).toNat+32 := by
    have eq : (actualVector p).out687=p.out687 := by simp only [actualVector,vectorMemoryTemplate]
    rw [eq,hn.vectorOut,nums.2.2.2.2,nums.1];omega
  have size : (actualVector p).size=p.size := by simp only [actualVector,vectorMemoryTemplate]
  rw [out,size] at record
  have lo := read_final_stack_word p hn ha ((scratch p).toNat+32) (by omega) (by rw [nums.1];omega)
  have hi := read_final_stack_word p hn ha ((scratch p).toNat+36) (by omega) (by rw [nums.1];omega)
  have len := read_final_stack_word p hn ha ((scratch p).toNat+40) (by omega) (by rw [nums.1];omega)
  have packed := read_final_stack_word64 p hn ha ((scratch p).toNat+32) (by omega) (by rw [nums.1];omega)
  refine ⟨lo.trans ?_,hi.trans ?_,len.trans ?_,packed⟩
  · simpa only [readInputMemory] using record.1
  · simpa only [readInputMemory,Nat.add_assoc,Nat.reduceAdd] using record.2.1
  · simpa only [readInputMemory,Nat.add_assoc,Nat.reduceAdd] using record.2.2
end WNear.Proofs.StateReadRegisterOuter
