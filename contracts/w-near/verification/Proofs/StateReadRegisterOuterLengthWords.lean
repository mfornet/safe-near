import Proofs.StateReadRegisterOuterLengthMemory
import Proofs.StateReadRegisterOuterCounter

/-! The real524 option record contains a present tag and the original byte length. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] lengthMemory readI64 StateDispatchLength.finalMemory actualLength registerMemory StateDispatchLengthOuter.inputMemory StateDispatchLength.acquiredMemory StateDispatchLength.lowMemory StateDispatchLength.highMemory

theorem length_words (p : Layout) (hn : Native p) :
    readI64 (lengthMemory p) ((scratch p).toNat+8)=1 ∧
    readI64 (lengthMemory p) ((scratch p).toNat+16)=UInt64.ofNat p.bytes.length := by
  have prep := prepared_spec p hn
  have bounds := prepared_native_bounds p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have cell := hn.threadBound
  have cf := StateDispatchLength.finalMemory_footprint (actualLength p).inner prep.1 bounds.2 bounds.1
    (by rw [counter_eq p hn,prep.2.1];simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega)
  have outEq : (actualLength p).out.toNat=(scratch p).toNat+8 := by
    simp only [actualLength,lengthOn]
    rw [nums.2.2.2.1,nums.1];omega
  have cb : (actualLength p).out.toNat+16≤(StateDispatchLength.finalMemory (actualLength p).inner).byteSize := by
    rw [cf.2.1,prep.2.1,outEq,nums.1];omega
  have spec := StateDispatchLengthOuterTail.finalMemory_spec (StateDispatchLength.finalMemory (actualLength p).inner)
    (actualLength p).out (UInt64.ofNat p.bytes.length) cf.1 cb
  have small := hn.sizeBound
  have nz : UInt64.ofNat p.bytes.length≠u64Max := by
    intro h
    have n := congrArg UInt64.toNat h
    simp only [UInt64.toNat_ofNat',u64Max,UInt64.toNat_ofNat,Nat.reducePow,Nat.reduceMod] at n
    rw [Nat.mod_eq_of_lt (by omega : p.bytes.length<18446744073709551616)] at n
    omega
  have tag : StateDispatchLengthOuterTail.present (UInt64.ofNat p.bytes.length)=1 := by
    rw [StateDispatchLengthOuterTail.present_eq,ite_eq_left nz]
  have lo := spec.2.2.2.1
  have hi := spec.2.2.2.2.1
  rw [outEq,tag] at lo
  rw [outEq] at hi
  unfold lengthMemory
  exact ⟨lo,by simpa only [Nat.add_assoc,Nat.reduceAdd] using hi⟩

theorem length_wrap (p : Layout) (hn : Native p) : (UInt64.ofNat p.bytes.length).toUInt32=p.size := by
  rw [hn.size]
  have small := hn.sizeBound
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32,UInt64.toNat_ofNat',UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : p.bytes.length<2^64)]
end WNear.Proofs.StateReadRegisterOuter
