import Proofs.StateReadRegisterOuterNative
import NearVM.MemoryListWordRules

/-! The523 register save and524 input save preserve all original static words. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI64 registerMemory

private theorem word64_away (m : Memory) (address source : Nat) (v : UInt64)
    (hw : m.wf) (hb : source+8≤m.byteSize)
    (hs : address+4≤source ∨ source+8≤address) :
    readI32 (writeI64 m source v) address=readI32 m address := by
  have written := writeI64_spec m source v hw hb
  apply readI32_congr_bytes
  intro i hi
  rw [written.2.2.2,ite_eq_right (show ¬(source≤address+i ∧ address+i<source+8) by omega)]

theorem registerMemory_spec (p : Layout) (hn : Native p) :
    (registerMemory p).wf ∧ (registerMemory p).byteSize=p.memory.byteSize ∧
    (registerMemory p).max=p.memory.max := by
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have writeBound : (scratch p).toNat+24+8≤p.memory.byteSize := by rw [nums.1];omega
  unfold registerMemory
  have h := writeI64_spec p.memory ((scratch p).toNat+24) p.register hn.allocation.wf writeBound
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem prepared_spec (p : Layout) (hn : Native p) :
    (actualLength p).inner.memory.wf ∧ (actualLength p).inner.memory.byteSize=p.memory.byteSize ∧
    (actualLength p).inner.memory.max=p.memory.max := by
  have reg := registerMemory_spec p hn
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have writeBound : (scratch p-16).toNat+8+8≤(registerMemory p).byteSize := by
    rw [reg.2.1,nums.2.1];omega
  have h := writeI64_spec (registerMemory p) ((scratch p-16).toNat+8) p.register reg.1 writeBound
  exact ⟨h.1,h.2.1.trans reg.2.1,h.2.2.1.trans reg.2.2⟩

theorem prepared_word (p : Layout) (hn : Native p) (address : Nat) (ha : p.sp523.toNat≤address) :
    readI32 (actualLength p).inner.memory address=readI32 p.memory address := by
  have reg := registerMemory_spec p hn
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have regBound : (scratch p).toNat+24+8≤p.memory.byteSize := by rw [nums.1];omega
  have inputBound : (scratch p-16).toNat+8+8≤(registerMemory p).byteSize := by
    rw [reg.2.1,nums.2.1];omega
  have regSep : (scratch p).toNat+24+8≤address := by rw [nums.1];omega
  have inputSep : (scratch p-16).toNat+8+8≤address := by rw [nums.2.1];omega
  have first := word64_away p.memory address ((scratch p).toNat+24) p.register hn.allocation.wf regBound (Or.inr regSep)
  have second := word64_away (registerMemory p) address ((scratch p-16).toNat+8) p.register reg.1 inputBound (Or.inr inputSep)
  change readI32 (writeI64 (registerMemory p) ((scratch p-16).toNat+8) p.register) address=_
  rw [second]
  unfold registerMemory
  exact first

theorem prepared_native_bounds (p : Layout) (hn : Native p) :
    (StateDispatchLength.scratch (actualLength p).inner).toNat+16≤(actualLength p).inner.memory.byteSize ∧
    1074904+4≤(actualLength p).inner.memory.byteSize := by
  have shape := prepared_spec p hn
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have cell := hn.threadBound
  have b : (StateDispatchLength.scratch (actualLength p).inner).toNat=p.sp523.toNat-80 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,actualLength,lengthOn] using nums.2.2.1
  rw [b,shape.2.1]
  omega
end WNear.Proofs.StateReadRegisterOuter
