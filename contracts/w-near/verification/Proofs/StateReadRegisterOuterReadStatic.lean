import Proofs.StateReadRegisterOuterReadSaved
import Proofs.StateReadRegisterOuterCounter

/-! Original static interface words survive both real callees, while the shared
borrow counter is restored by524 before687 preserves it. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 readInputMemory lengthMemory

theorem read_length_word (p : Layout) (hn : Native p) (ha : p.allocator=1074896) (address : Nat)
    (hb : address+4≤p.memory.byteSize) (hs : p.sp523.toNat≤address)
    (hr : address+4≤1074896 ∨ 1074900≤address) :
    readI32 (readInputMemory p) address=readI32 (lengthMemory p) address := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have shape := lengthMemory_footprint p hn
  have nv := vector_native p hn ha
  have vm : (actualVector p).memory=lengthMemory p := rfl
  have vsp : (actualVector p).sp687=scratch p := hn.vectorSP
  have vo : (actualVector p).out687=scratch p+32 := hn.vectorOut
  have va : (actualVector p).allocator=1074896 := ha
  unfold readInputMemory
  exact AllocateVectorOuter.finalMemory_old_word (actualVector p) nv address
    (by rw [vm,shape.2.1];exact hb)
    (by rw [vsp,nums.1];omega)
    (by rw [va];exact hr)
    (Or.inr (by rw [vo,nums.2.2.2.2];omega))

theorem read_original_word (p : Layout) (hn : Native p) (ha : p.allocator=1074896) (address : Nat)
    (hb : address+4≤p.memory.byteSize) (hs : p.sp523.toNat≤address)
    (hr : address+4≤1074896 ∨ 1074900≤address)
    (hc : address+4≤1074904 ∨ 1074908≤address) :
    readI32 (readInputMemory p) address=readI32 p.memory address := by
  rw [read_length_word p hn ha address hb hs hr]
  exact lengthMemory_word p hn address hs hc

theorem read_counter_zero (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI32 (readInputMemory p) 1074904=0 := by
  have bound := hn.threadBound
  have above := hn.staticAbove
  rw [read_length_word p hn ha 1074904 (by omega) (by omega) (Or.inr (by omega))]
  exact length_counter_restored p hn
end WNear.Proofs.StateReadRegisterOuter
