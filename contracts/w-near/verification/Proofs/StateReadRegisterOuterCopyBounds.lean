import Proofs.StateReadRegisterOuterNative

/-! Original523 spans give all actual sequentialcopy addresses without UInt32 wrap. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

theorem copy_bounds (p : Layout) (hn : Native p) :
    (p.out523+8).toNat=p.out523.toNat+8 ∧
    (scratch p+32+8).toNat=(scratch p).toNat+40 ∧
    (scratch p+32+8).toNat+4≤p.memory.byteSize ∧
    (p.out523+8).toNat+4≤p.memory.byteSize ∧
    (scratch p).toNat+32+8≤p.memory.byteSize ∧ p.out523.toNat+8≤p.memory.byteSize := by
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have width := hn.allocation.width
  have upper := p.sp523.toNat_lt
  have outBound := hn.outputBound
  have out : (p.out523+8).toNat=p.out523.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt;omega
  have inner : (scratch p+32).toNat=(scratch p).toNat+32 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt;omega
  have src : (scratch p+32+8).toNat=(scratch p).toNat+40 := by
    rw [UInt32.toNat_add,inner]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : (scratch p).toNat+32+8<4294967296)]
  exact ⟨out,src,by omega,by omega,by omega,by omega⟩
end WNear.Proofs.StateReadRegisterOuter
