import Proofs.StateReadRegisterOuterReadState
import Proofs.StateReadRegisterOuterLengthMemory
import Proofs.StateReadRegisterOuterVectorNative
import Proofs.AllocateVectorOuterOldFrame

/-! The saved register ID survives524 and687; all byte exclusions follow from
original stack positions rather than a post-call equality premise. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI64 lengthMemory registerMemory

theorem length_saved_register (p : Layout) (hn : Native p) :
    readI64 (lengthMemory p) ((scratch p).toNat+24)=p.register := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have static := hn.staticAbove
  have reg := registerMemory_spec p hn
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
    (by rw [memoryEq,reg.2.1];have := hn.threadBound;omega)
    (by rw [memoryEq,reg.2.1,counter_eq p hn];change 1074904+4≤p.memory.byteSize;have := hn.threadBound;omega)
    (by rw [memoryEq,reg.2.1,out];omega)
  have preserved : readI64 (lengthMemory p) ((scratch p).toNat+24)=
      readI64 (registerMemory p) ((scratch p).toNat+24) := by
    apply readI64_congr_bytes
    intro i hi
    unfold lengthMemory
    change _=(actualLength p).memory.read8 _
    exact fp.2.2.2 ((scratch p).toNat+24+i)
      (Or.inr (by rw [outer,nums.1];omega))
      (Or.inr (by rw [inner,nums.1];omega))
      (Or.inl (by rw [nums.1];omega))
      (by rw [counter_eq p hn];exact Or.inl (by change (scratch p).toNat+24+i<1074904;rw [nums.1];omega))
      (Or.inr (by rw [out,nums.1];omega))
  rw [preserved]
  unfold registerMemory
  have write := writeI64_spec p.memory ((scratch p).toNat+24) p.register hn.allocation.wf (by rw [nums.1];omega)
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [write.2.2.2 ((scratch p).toNat+24+i)]
  have inside : (scratch p).toNat+24≤(scratch p).toNat+24+i ∧ (scratch p).toNat+24+i<(scratch p).toNat+24+8 := by omega
  rw [ite_eq_left inside]
  simp only [Nat.add_sub_cancel_left]

theorem read_saved_register (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI64 (readInputMemory p) ((scratch p+24).toNat)=p.register := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have upper := p.sp523.toNat_lt
  have bound := hn.spBound
  have root := hn.heapAbove
  have shape := lengthMemory_footprint p hn
  have nat24 : (scratch p+24).toNat=(scratch p).toNat+24 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reduceMod,Nat.reducePow]
    rw [nums.1];omega
  have nv := vector_native p hn ha
  have vsp : (actualVector p).sp687=scratch p := hn.vectorSP
  have vo : (actualVector p).out687=scratch p+32 := hn.vectorOut
  have va : (actualVector p).allocator=1074896 := ha
  have vm : (actualVector p).memory=lengthMemory p := rfl
  unfold readInputMemory
  rw [AllocateVectorOuter.finalMemory_old_word64 (actualVector p) nv ((scratch p+24).toNat)
    (by rw [vm,shape.2.1,nat24,nums.1];omega)
    (by rw [vsp,nat24];omega)
    (Or.inl (by rw [va,nat24,nums.1];change p.sp523.toNat-48+24+8≤1074896;rw [ha] at root;change p.sp523.toNat≤1074896 at root;omega))
    (Or.inl (by rw [vo,nat24,nums.2.2.2.2,nums.1];omega))]
  rw [vm,nat24]
  exact length_saved_register p hn
end WNear.Proofs.StateReadRegisterOuter
