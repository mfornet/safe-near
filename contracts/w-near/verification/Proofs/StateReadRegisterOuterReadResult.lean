import Proofs.StateReadRegisterOuterReadDomain
import Proofs.StateReadRegisterOuterReadFinal

/-! Complete actual435 memory extent, including payload copy and sequential
counter release, follows from523's original domain. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 readInputMemory readFinalMemory readOutputMemory

theorem readFinalMemory_spec (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    (readFinalMemory p).wf ∧ p.memory.byteSize≤(readFinalMemory p).byteSize ∧
    (readFinalMemory p).max=p.memory.max := by
  have snapshot := read_snapshot p hn ha
  have low := snapshot.low_shape
  have payload : (StateDispatchRead.ptr (readLayout p)).toNat+p.bytes.length≤(StateDispatchRead.lowMemory (readLayout p)).byteSize := by
    rw [snapshot.ptr_nat,low.2.1];exact snapshot.payloadBound
  have copy := Memory.writeList_spec p.bytes (StateDispatchRead.lowMemory (readLayout p))
    (StateDispatchRead.ptr (readLayout p)).toNat low.1 payload
  have copySize : (readOutputMemory p).byteSize=(readInputMemory p).byteSize := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.1.trans low.2.1
  have copyMax : (readOutputMemory p).max=(readInputMemory p).max := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory,readLayout,readOn] using copy.2.2.1.trans low.2.2
  have counter : readCounter p=1074904 := by simpa only [readCounter] using snapshot.counter
  have cell := snapshot.stateBound
  have bound : (readCounter p).toNat+4≤(readOutputMemory p).byteSize := by
    rw [counter,copySize];change 1074908≤(readInputMemory p).byteSize;exact le_trans (by decide) cell
  have copyWf : (readOutputMemory p).wf := by
    simpa only [readOutputMemory,StateDispatchRead.readMemory] using copy.1
  have release := writeI32_spec (readOutputMemory p) (readCounter p).toNat
    (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295) copyWf bound
  have length := lengthMemory_footprint p hn
  have vector := AllocateVectorOuter.final_spec (actualVector p) (vector_native p hn ha)
  have vectorSize : p.memory.byteSize≤(readInputMemory p).byteSize := by
    unfold readInputMemory
    rw [←length.2.1]
    exact vector.2.1
  have vectorMax : (readInputMemory p).max=p.memory.max := by
    unfold readInputMemory
    exact vector.2.2.1.trans length.2.2.1
  unfold readFinalMemory
  exact ⟨release.1,by rw [release.2.1,copySize];exact vectorSize,
    release.2.2.1.trans (copyMax.trans vectorMax)⟩
end WNear.Proofs.StateReadRegisterOuter
