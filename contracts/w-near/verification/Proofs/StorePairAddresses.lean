import NearVM.MeteredScalarRules

/-! Address arithmetic for deployed f414. `Memory.wf` constrains page contents,
not the number of pages; the address-width hypotheses here remain explicit. -/
namespace WNear.Proofs.StorePairAddresses
open Wasm

/-- A separate page-count bound supplies the 32-bit memory-width invariant. -/
theorem byteSize_le_u32 (memory : Memory) (hpages : memory.size ≤ maxPages) :
    memory.byteSize ≤ 2 ^ 32 := by
  simp only [Memory.size, maxPages] at hpages
  simp only [Memory.byteSize, pageSize]
  omega

theorem add_eight (address : UInt32) (hspan : address.toNat + 16 ≤ 2 ^ 32) :
    (address + 8).toNat = address.toNat + 8 := by
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem add_eight_memory (memory : Memory) (address : UInt32)
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hspan : address.toNat + 16 ≤ memory.byteSize) :
    (address + 8).toNat = address.toNat + 8 :=
  add_eight address (Nat.le_trans hspan hwidth)

theorem sub_sixteen (sp : UInt32) (hsp : 16 ≤ sp.toNat) :
    (sp - 16).toNat = sp.toNat - 16 := by
  have hlt := UInt32.toNat_lt sp
  rw [UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- Restoring the stack pointer is a bit-vector identity, including wraparound. -/
theorem restore (sp : UInt32) : (sp - 16) + 16 = sp := UInt32.sub_add_cancel sp 16

theorem scratch_end (sp : UInt32) (hsp : 16 ≤ sp.toNat) :
    (sp - 16).toNat + 16 = sp.toNat := by
  rw [sub_sixteen sp hsp]
  omega

theorem scratch_add_eight (sp : UInt32) (hsp : 16 ≤ sp.toNat) :
    ((sp - 16) + 8).toNat = (sp - 16).toNat + 8 := by
  have he := scratch_end sp hsp
  have hlt := UInt32.toNat_lt sp
  apply add_eight
  omega

theorem scratch_bounds (memory : Memory) (sp : UInt32)
    (hsp : 16 ≤ sp.toNat) (hlimit : sp.toNat ≤ memory.byteSize) :
    (sp - 16).toNat + 16 ≤ memory.byteSize ∧
    (sp - 16).toNat + 8 + 8 ≤ memory.byteSize ∧
    ((sp - 16) + 8).toNat + 8 ≤ memory.byteSize := by
  rw [scratch_add_eight sp hsp]
  have he := scratch_end sp hsp
  omega

theorem source_bounds (memory : Memory) (source : UInt32)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hspan : source.toNat + 16 ≤ memory.byteSize) :
    source.toNat + 8 ≤ memory.byteSize ∧
    (source + 8).toNat + 8 ≤ memory.byteSize := by
  rw [add_eight_memory memory source hwidth hspan]
  omega

end WNear.Proofs.StorePairAddresses
