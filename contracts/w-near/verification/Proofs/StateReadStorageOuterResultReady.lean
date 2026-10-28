import Proofs.StateReadStorageOuterPhases
import Proofs.StateReadStorageOuterRegisterNative
import Proofs.AllocateVectorResources
import Proofs.StateReadResultReadback

/-! Original f548 stack geometry gives a present f498 source and all copy bounds. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] registeredMemory storageMemory readI32 readI64

theorem register_copy_separation (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    (StateReadRegisterOuter.scratch (actualRegister p)).toNat+40≤((actualRegister p).out523+8).toNat := by
  have rn := register_native p hn ha
  have nums := StateReadRegisterOuter.stack_numbers (actualRegister p) rn
  have cb := StateReadRegisterOuter.copy_bounds (actualRegister p) rn
  have out : (actualRegister p).out523=scratch p+16 := hn.registerOut
  have sp : (actualRegister p).sp523=scratch p := hn.registerSP
  have outer := stack_numbers p hn
  rw [cb.1,out,outer.2.2.2,nums.1,sp,outer.1]
  have := hn.spLower
  omega

theorem registeredMemory_record (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI32 (registeredMemory p) (scratch p+16).toNat=
      AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector ∧
    readI32 (registeredMemory p) ((scratch p+16).toNat+4)=p.size ∧
    readI32 (registeredMemory p) ((scratch p+16).toNat+8)=p.size := by
  have record :=  StateReadRegisterOuter.copiedMemory_record (actualRegister p) (register_native p hn ha) ha
    (Or.inl (register_copy_separation p hn ha))
  simpa only [registeredMemory,show (actualRegister p).out523=scratch p+16 from hn.registerOut,
    show (actualRegister p).size=p.size from rfl] using record

theorem registeredMemory_present (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI32 (registeredMemory p) (scratch p+16).toNat≠0 := by
  rw [(registeredMemory_record p hn ha).1]
  exact AllocateVector.result_nonzero _ ((StateReadRegisterOuter.vector_native (actualRegister p) (register_native p hn ha) ha).vector _)

theorem result_bounds (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    (registeredMemory p).wf ∧
    p.out548.toNat+8≤(registeredMemory p).byteSize ∧
    (scratch p+16).toNat+8≤(registeredMemory p).byteSize ∧
    (p.out548+8).toNat+4≤(registeredMemory p).byteSize ∧
    (scratch p+16+8).toNat+4≤(registeredMemory p).byteSize ∧
    (p.out548+8).toNat=p.out548.toNat+8 ∧
    (scratch p+16+8).toNat=(scratch p+16).toNat+8 := by
  have shape := StateReadRegisterOuter.copiedMemory_spec (actualRegister p) (register_native p hn ha) ha
  have old : (actualRegister p).memory.byteSize=p.memory.byteSize := by
    change (storageMemory p).byteSize=p.memory.byteSize
    exact (storageMemory_footprint p hn).2.1
  have grows : p.memory.byteSize≤(registeredMemory p).byteSize := by
    have grow := shape.2.1
    rw [old] at grow
    unfold registeredMemory
    exact grow
  have width := hn.register.allocation.width
  have bound := hn.outputBound
  have nums := stack_numbers p hn
  have lo := hn.spLower
  have sb := hn.spBound
  have out : (p.out548+8).toNat=p.out548.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt;omega
  have src : (scratch p+16+8).toNat=(scratch p+16).toNat+8 := by
    rw [UInt32.toNat_add,nums.2.2.2]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    have := p.sp548.toNat_lt
    omega
  refine ⟨?_,by omega,by rw [nums.2.2.2];omega,by rw [out];omega,
    by rw [src,nums.2.2.2];omega,out,src⟩
  unfold registeredMemory
  exact shape.1
end WNear.Proofs.StateReadStorageOuter
