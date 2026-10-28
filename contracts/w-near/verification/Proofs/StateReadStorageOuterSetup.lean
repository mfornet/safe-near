import Proofs.StateReadStorageOuterNative
import Proofs.StateDispatchLengthOuterFootprint

/-! The actual548 key-record stores preserve original static and key bytes. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem setup_spec (p : Layout) (hn : Native p) :
    (setupMemory p).wf ∧ (setupMemory p).byteSize=p.memory.byteSize ∧ (setupMemory p).max=p.memory.max := by
  have nums := stack_numbers p hn
  have lo := hn.spLower
  have bound := hn.spBound
  have hhi : (scratch p).toNat+12+4≤p.memory.byteSize := by rw [nums.1];omega
  have high := writeI32_spec p.memory ((scratch p).toNat+12) p.keyLen hn.register.allocation.wf hhi
  have hlo : (scratch p).toNat+8+4≤(highMemory p).byteSize := by change _≤(writeI32 p.memory _ _).byteSize;rw [high.2.1];omega
  have low := writeI32_spec (highMemory p) ((scratch p).toNat+8) p.keyPtr high.1 hlo
  exact ⟨low.1,low.2.1.trans high.2.1,low.2.2.1.trans high.2.2.1⟩

theorem setup_byte (p : Layout) (hn : Native p) (address : Nat) (ha : p.sp548.toNat≤address) :
    (setupMemory p).read8 address=p.memory.read8 address := by
  have nums := stack_numbers p hn
  have lo := hn.spLower
  have bound := hn.spBound
  have hhi : (scratch p).toNat+12+4≤p.memory.byteSize := by rw [nums.1];omega
  have high := writeI32_spec p.memory ((scratch p).toNat+12) p.keyLen hn.register.allocation.wf hhi
  have hlo : (scratch p).toNat+8+4≤(highMemory p).byteSize := by change _≤(writeI32 p.memory _ _).byteSize;rw [high.2.1];omega
  have low := writeI32_spec (highMemory p) ((scratch p).toNat+8) p.keyPtr high.1 hlo
  have a := high.2.2.2 address
  have b := low.2.2.2 address
  have hiSep : ¬((scratch p).toNat+12≤address ∧ address<(scratch p).toNat+12+4) := by rw [nums.1];omega
  have loSep : ¬((scratch p).toNat+8≤address ∧ address<(scratch p).toNat+8+4) := by rw [nums.1];omega
  simp only [ite_eq_right hiSep] at a
  simp only [ite_eq_right loSep] at b
  exact b.trans a

theorem setup_word (p : Layout) (hn : Native p) (address : Nat) (ha : p.sp548.toNat≤address) :
    readI32 (setupMemory p) address=readI32 p.memory address := by
  apply readI32_congr_bytes
  intro i hi
  exact setup_byte p hn (address+i) (by omega)

theorem setup_native_bounds (p : Layout) (hn : Native p) :
    (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(setupMemory p).byteSize ∧
    1074904+4≤(setupMemory p).byteSize := by
  have shape := setup_spec p hn
  have nums := stack_numbers p hn
  have lo := hn.spLower
  have bound := hn.spBound
  have cell := hn.register.threadBound
  have b : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  rw [b,shape.2.1]
  omega
end WNear.Proofs.StateReadStorageOuter
