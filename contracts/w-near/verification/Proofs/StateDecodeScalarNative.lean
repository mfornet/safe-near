import Proofs.StateDecodeScalarState
import Proofs.StorePairAddresses

/-! Original native geometry for accepted scalar reads. Scratch writes are below
`sp`; descriptors and source bytes start at or above it. Output may alias either. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic

structure Native (wide : Bool) (p : Layout) : Prop where
  wf : p.memory.wf
  memoryWidth : p.memory.byteSize≤2^32
  spLower : 48≤p.sp.toNat
  spBound : p.sp.toNat≤p.memory.byteSize
  outAbove : p.sp.toNat≤p.out.toNat
  outBound : p.out.toNat+(if wide then 24 else 16)≤p.memory.byteSize
  sliceAbove : p.sp.toNat≤p.slice.toNat
  sliceBound : p.slice.toNat+8≤p.memory.byteSize
  pointerRead : readI32 p.memory p.slice.toNat=p.pointer
  lengthRead : readI32 p.memory (p.slice.toNat+4)=p.length
  lengthAccepted : widthNat wide≤p.length.toNat
  pointerAbove : p.sp.toNat≤p.pointer.toNat
  payloadBound : p.pointer.toNat+widthNat wide≤p.memory.byteSize

theorem scratch_nat (wide : Bool) (p : Layout) (hn : Native wide p) :
    (scratch p).toNat=p.sp.toNat-48 := by
  have hlt:=UInt32.toNat_lt p.sp
  have hlo:=hn.spLower
  unfold scratch
  rw [UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem scratch_end (wide : Bool) (p : Layout) (hn : Native wide p) :
    (scratch p).toNat+48=p.sp.toNat := by
  rw [scratch_nat wide p hn]
  have h:=hn.spLower
  omega

theorem scratch_add (wide : Bool) (p : Layout) (hn : Native wide p) (n : Nat) (h : n≤48) :
    (scratch p+UInt32.ofNat n).toNat=(scratch p).toNat+n := by
  have he:=scratch_end wide p hn
  have hlt:=UInt32.toNat_lt p.sp
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat',Nat.reducePow]
  have hnlt:n<4294967296:=by omega
  rw [Nat.mod_eq_of_lt hnlt,Nat.mod_eq_of_lt (by omega)]

theorem takeOut_nat (wide : Bool) (p : Layout) (hn : Native wide p) :
    (takeOut wide p).toNat=(scratch p).toNat+(if wide then 8 else 16) := by
  cases wide with
  |false=>exact scratch_add false p hn 16 (by omega)
  |true=>exact scratch_add true p hn 8 (by omega)

theorem wordOut_nat (wide : Bool) (p : Layout) (hn : Native wide p) :
    (wordOut wide p).toNat=(scratch p).toNat+(if wide then 16 else 24) := by
  cases wide with
  |false=>exact scratch_add false p hn 24 (by omega)
  |true=>exact scratch_add true p hn 16 (by omega)

theorem dropOut_nat (wide : Bool) (p : Layout) (hn : Native wide p) :
    (dropOut wide p).toNat=(scratch p).toNat+(if wide then 0 else 8) := by
  cases wide with
  |false=>exact scratch_add false p hn 8 (by omega)
  |true=>exact scratch_add true p hn 0 (by omega)

theorem scratch_spans (wide : Bool) (p : Layout) (hn : Native wide p) :
    (takeOut wide p).toNat+8≤p.sp.toNat ∧
    (wordOut wide p).toNat+(StateDecodeWords.widthNat wide+1)≤p.sp.toNat ∧
    (dropOut wide p).toNat+8≤p.sp.toNat := by
  rw [takeOut_nat wide p hn,wordOut_nat wide p hn,dropOut_nat wide p hn]
  have he:=scratch_end wide p hn
  cases wide <;> simp only [StateDecodeWords.widthNat,ite_true,Bool.false_eq_true,ite_false] <;> omega

end WNear.Proofs.StateDecodeScalar
