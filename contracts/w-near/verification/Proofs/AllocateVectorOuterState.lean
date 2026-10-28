import Proofs.AllocateVectorState

/-! Original f687 data. The686 domain is reconstructed after a32-byte SP reservation;
no Native proposition about a future poststore is an input. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic

structure Layout extends toVector : AllocateVector.Layout where
  sp687 : UInt32
  global687 : GlobalInst
  out687 : UInt32
  flag : UInt32
  address686 : Nat

structure Native (p : Layout) : Prop where
  allocation : AllocateZeroedRetry.Native p.toRecord.toZeroed
  innerSP : p.outerSP=p.sp687-32
  childSP : p.sp=p.sp687-80
  childOut : p.out=p.sp+8
  outerGlobal : p.outerGlobal={p.global687 with value:=.i32 p.outerSP}
  childGlobal : p.global={p.global687 with value:=.i32 p.sp}
  innerOut : p.out686=p.outerSP+8
  spLower : 96≤p.sp687.toNat
  spBound : p.sp687.toNat≤p.memory.byteSize
  sizeBound : p.size.toNat<2^31
  outputBound : p.out687.toNat+12≤p.memory.byteSize
  heapAbove : p.sp687.toNat≤p.allocator.toNat
  callbackAbove : p.sp687.toNat≤1057464+16
  byteFlag : p.flag &&& 255=0

theorem stack_numbers (p : Layout) (hn : Native p) :
    p.outerSP.toNat=p.sp687.toNat-32 ∧ p.sp.toNat=p.sp687.toNat-80 ∧
    p.out686.toNat=p.sp687.toNat-24 := by
  have lower := hn.spLower
  have upper := p.sp687.toNat_lt
  have a : p.outerSP.toNat=p.sp687.toNat-32 := by
    rw [hn.innerSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have b : p.sp.toNat=p.sp687.toNat-80 := by
    rw [hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have c : p.out686.toNat=p.sp687.toNat-24 := by
    rw [hn.innerOut,UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨a,b,c⟩

theorem Native.vector (p : Layout) (hn : Native p) : AllocateVector.Native p.toVector := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have upper := p.sp687.toNat_lt
  have child : p.sp=p.outerSP-48 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub,nums.1,nums.2.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have global : p.global={p.outerGlobal with value:=.i32 p.sp} := by
    rw [hn.outerGlobal]
    exact hn.childGlobal
  have bound := hn.spBound
  have heap := hn.heapAbove
  have callback := hn.callbackAbove
  exact ⟨hn.allocation,child,hn.childOut,global,by omega,
    by omega,hn.sizeBound,
    by omega,
    by omega,
    by omega⟩
end WNear.Proofs.AllocateVectorOuter
