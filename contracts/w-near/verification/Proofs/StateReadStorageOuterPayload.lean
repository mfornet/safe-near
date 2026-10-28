import Proofs.StateReadStorageOuterResultOutput

/-! The fresh allocation retains every original storage byte through the final copy. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] finalMemory registeredMemory actualRegister
  StateReadRegisterOuter.actualVector AllocateVector.result

namespace StateReadRegisterOuterPointer
open WNear.Proofs.StateReadRegisterOuter
theorem above (q : StateReadRegisterOuter.Layout) (hn : StateReadRegisterOuter.Native q)
    (ha : q.allocator=1074896) :
    q.memory.byteSize≤(AllocateVector.result (StateReadRegisterOuter.actualVector q).toVector).toNat := by
  have fresh := AllocateVectorOuter.result_payload (StateReadRegisterOuter.actualVector q)
    (StateReadRegisterOuter.vector_native q hn ha)
  have length := StateReadRegisterOuter.lengthMemory_footprint q hn
  simpa only [show (StateReadRegisterOuter.actualVector q).memory=StateReadRegisterOuter.lengthMemory q from by
    simp only [StateReadRegisterOuter.actualVector,StateReadRegisterOuter.vectorMemoryTemplate],length.2.1] using fresh.1
end StateReadRegisterOuterPointer

theorem registered_pointer_above (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    p.memory.byteSize≤(AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat := by
  have ar : (actualRegister p).allocator=1074896 := by simpa only [actualRegister,registerTemplate] using ha
  have bound := StateReadRegisterOuterPointer.above (actualRegister p) (register_native p hn ha) ar
  have old : (actualRegister p).memory.byteSize=p.memory.byteSize := by
    unfold actualRegister registerTemplate
    change (storageMemory p).byteSize=p.memory.byteSize
    exact (storageMemory_footprint p hn).2.1
  rw [old] at bound
  exact bound

theorem finalMemory_payload (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (i : Nat) (hi : i<p.bytes.length) :
    (finalMemory p).read8 ((AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat+i)=p.bytes[i]! := by
  have above := registered_pointer_above p hn ha
  have bound := hn.outputBound
  rw [finalMemory_byte_frame p hn ha _ (Or.inr (by omega))]
  unfold registeredMemory
  have ar : (actualRegister p).allocator=1074896 := by simpa only [actualRegister,registerTemplate] using ha
  have byte := StateReadRegisterOuter.copiedMemory_payload (actualRegister p) (register_native p hn ha) ar i
  have bytes : (actualRegister p).bytes=p.bytes := by simp only [actualRegister,registerTemplate]
  rw [bytes] at byte
  exact byte hi
end WNear.Proofs.StateReadStorageOuter
