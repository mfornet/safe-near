import Proofs.AllocationGrowthRemainderReadExtent
import Proofs.AllocationGrowthRemainderStorageFacts

/-! Exact548 extent equals the actual grown allocator heap. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] finalMemory registeredMemory actualRegister AllocateRetry.finalMemory StateReadRegisterOuter.remainderLayout AllocateVector.remainderLayout

 theorem finalMemory_remainder_size(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (finalMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=by
  have rn:=register_native p hn ha
  have ca:(actualRegister p).allocator=1074896:=by simp only[actualRegister,registerTemplate];exact ha
  have h:=StateReadRegisterOuter.copiedMemory_remainder_size (actualRegister p) rn ca
  have outer:=finalMemory_shape p hn ha
  have size:(registeredMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=by
    unfold registeredMemory remainderLayout
    unfold StateReadRegisterOuter.remainderLayout at h
    exact h
  exact outer.2.1.trans size
end WNear.Proofs.StateReadStorageOuter
