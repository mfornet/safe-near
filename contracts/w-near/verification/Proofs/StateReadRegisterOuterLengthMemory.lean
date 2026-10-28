import Proofs.StateReadRegisterOuterBorrow

/-! Original-memory shape and byte frames of the complete length-query setup. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 writeI64 lengthMemory registerMemory

theorem lengthMemory_footprint (p : Layout) (hn : Native p) :
    (lengthMemory p).wf ∧ (lengthMemory p).byteSize=p.memory.byteSize ∧
    (lengthMemory p).max=p.memory.max ∧
    ∀ j, p.sp523.toNat≤j → (j<1074904 ∨ 1074908≤j) →
      (lengthMemory p).read8 j=p.memory.read8 j := by
  have reg := registerMemory_spec p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have cell := hn.threadBound
  have inner : (StateDispatchLength.scratch (actualLength p).inner).toNat=p.sp523.toNat-80 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,actualLength,lengthOn] using nums.2.2.1
  have outer : (StateDispatchLengthOuter.scratch (actualLength p)).toNat=p.sp523.toNat-64 := by
    simpa only [StateDispatchLengthOuter.scratch,actualLength,lengthOn] using nums.2.1
  have out : (actualLength p).out.toNat=p.sp523.toNat-40 := nums.2.2.2.1
  have memoryEq : (actualLength p).memory=registerMemory p := rfl
  have fp := StateDispatchLengthOuter.outputMemory_footprint (actualLength p) (UInt64.ofNat p.bytes.length)
    reg.1 rfl
    (by rw [memoryEq,reg.2.1,outer];omega)
    (by rw [memoryEq,reg.2.1,inner];omega)
    (by rw [memoryEq,reg.2.1];omega)
    (by rw [memoryEq,reg.2.1,counter_eq p hn];change 1074904+4≤p.memory.byteSize;omega)
    (by rw [memoryEq,reg.2.1,out];omega)
  have shape : (lengthMemory p).wf ∧ (lengthMemory p).byteSize=p.memory.byteSize ∧
      (lengthMemory p).max=p.memory.max := by
    unfold lengthMemory
    exact ⟨fp.1,fp.2.1.trans reg.2.1,fp.2.2.1.trans reg.2.2⟩
  refine ⟨shape.1,shape.2.1,shape.2.2,?_⟩
  intro j hj hc
  have frame := fp.2.2.2 j (Or.inr (by rw [outer];omega)) (Or.inr (by rw [inner];omega)) hc
    (by rw [counter_eq p hn];exact hc) (Or.inr (by rw [out];omega))
  have saved := writeI64_spec p.memory ((scratch p).toNat+24) p.register hn.allocation.wf
    (by rw [nums.1];omega)
  unfold lengthMemory
  rw [frame]
  rw [memoryEq]
  unfold registerMemory
  rw [saved.2.2.2 j,ite_eq_right (by rw [nums.1];omega)]

theorem lengthMemory_size (p : Layout) (hn : Native p) : (lengthMemory p).size=p.memory.size := by
  have h := (lengthMemory_footprint p hn).2.1
  change (lengthMemory p).size*65536=p.memory.size*65536 at h
  omega

theorem lengthMemory_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp523.toNat≤address) (hc : address+4≤1074904 ∨ 1074908≤address) :
    readI32 (lengthMemory p) address=readI32 p.memory address := by
  apply readI32_congr_bytes
  intro i hi
  exact (lengthMemory_footprint p hn).2.2.2 (address+i) (by omega) (by omega)
end WNear.Proofs.StateReadRegisterOuter
