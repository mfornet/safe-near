import Proofs.AllocationGrowthRemainderStatic

/-! Original extent and maximum after the complete present548 path. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] finalMemory registeredMemory actualRegister

 theorem finalMemory_shape_original(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (finalMemory p).wf ∧p.memory.byteSize≤(finalMemory p).byteSize ∧(finalMemory p).max=p.memory.max:=by
  have outer:=finalMemory_shape p hn ha
  have register:=StateReadRegisterOuter.copiedMemory_spec (actualRegister p) (register_native p hn ha)
    (by simp only[actualRegister,registerTemplate];exact ha)
  have old:(actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualRegister,registerTemplate];exact (storageMemory_footprint p hn).2.1
  have max:(actualRegister p).memory.max=p.memory.max:=by
    simp only[actualRegister,registerTemplate];exact (storageMemory_footprint p hn).2.2.1
  have lower:p.memory.byteSize≤(registeredMemory p).byteSize:=by
    have h:=register.2.1
    rw[old] at h
    unfold registeredMemory
    exact h
  have equal:(registeredMemory p).max=p.memory.max:=by
    unfold registeredMemory
    exact register.2.2.1.trans max
  exact ⟨outer.1,lower.trans_eq outer.2.1.symm,outer.2.2.trans equal⟩
end WNear.Proofs.StateReadStorageOuter
