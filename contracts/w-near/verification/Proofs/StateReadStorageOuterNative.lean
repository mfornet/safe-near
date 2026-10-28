import Proofs.StateReadStorageOuterState
import Proofs.StateReadRegisterOuterNative

/-! Original data for the present-storage path. The register template refers
only to the original memory; its actual post459 Native is derived separately. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic

structure Native (p : Layout) : Prop where
  register : StateReadRegisterOuter.Native p.toRegisterOuter
  registerSP : p.sp523=scratch p
  registerOut : p.out523=scratch p+16
  registerId : p.register=0
  registerGlobal : p.global523={p.global548 with value:=.i32 (scratch p)}
  spLower : 176≤p.sp548.toNat
  spBound : p.sp548.toNat≤p.memory.byteSize
  aligned : p.sp548.toNat%16=0
  keyAbove : p.sp548.toNat≤p.keyPtr.toNat
  keyCounterSep : p.keyPtr.toNat+p.keyLen.toNat≤1074904 ∨ 1074908≤p.keyPtr.toNat
  vtableBeforeHeap : p.dispatchVtable.toNat+192≤p.allocator.toNat
  keyBound : p.keyPtr.toNat+p.keyLen.toNat≤p.memory.byteSize
  outputBound : p.out548.toNat+12≤p.memory.byteSize
  vtableBound : p.dispatchVtable.toNat+192≤p.memory.byteSize
  staticAbove : p.sp548.toNat≤1055020
  threadAbove : p.sp548.toNat≤1074900
  vtableAbove : p.sp548.toNat≤p.dispatchVtable.toNat

theorem stack_numbers (p : Layout) (hn : Native p) :
    (scratch p).toNat=p.sp548.toNat-32 ∧
    (scratch p-16).toNat=p.sp548.toNat-48 ∧
    (scratch p+8).toNat=p.sp548.toNat-24 ∧
    (scratch p+16).toNat=p.sp548.toNat-16 := by
  have lower := hn.spLower
  have upper := p.sp548.toNat_lt
  have a : (scratch p).toNat=p.sp548.toNat-32 := by
    rw [scratch,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have b : (scratch p-16).toNat=p.sp548.toNat-48 := by
    rw [UInt32.toNat_sub,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have c : (scratch p+8).toNat=p.sp548.toNat-24 := by
    rw [UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have d : (scratch p+16).toNat=p.sp548.toNat-16 := by
    rw [UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  exact ⟨a,b,c,d⟩
end WNear.Proofs.StateReadStorageOuter
