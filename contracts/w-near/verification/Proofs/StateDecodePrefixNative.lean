import Proofs.StateDecodePrefixState

/-! Original accepted positive byte-vector domain. The slice/payload separation
is necessary for preserving original bytes across the early slice advance. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

structure Native (p : Layout) : Prop where
  wf : p.memory.wf
  memoryWidth : p.memory.byteSize≤2^32
  spLower : 64≤p.sp.toNat
  spBound : p.sp.toNat≤p.memory.byteSize
  outAbove : p.sp.toNat≤p.out.toNat
  outBound : p.out.toNat+16≤p.memory.byteSize
  sliceAbove : p.sp.toNat≤p.slice.toNat
  sliceBound : p.slice.toNat+8≤p.memory.byteSize
  pointerRead : readI32 p.memory p.slice.toNat=p.pointer
  lengthRead : readI32 p.memory (p.slice.toNat+4)=p.length
  pointerAbove : p.sp.toNat≤p.pointer.toNat
  payloadBound : p.pointer.toNat+4+(count p).toNat≤p.memory.byteSize
  lengthAccepted : 4+(count p).toNat≤p.length.toNat
  countPositive : count p≠0
  countSigned : (count p).toNat<2^31
  slicePayloadSep : p.slice.toNat+8≤p.pointer.toNat ∨p.pointer.toNat+4+(count p).toNat≤p.slice.toNat

theorem scratch_nat (p : Layout) (hn : Native p) : (scratch p).toNat=p.sp.toNat-64 := by
  have hlo:=hn.spLower
  have hlt:=UInt32.toNat_lt p.sp
  unfold scratch
  rw[UInt32.toNat_sub]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem scratch_end (p : Layout) (hn : Native p) : (scratch p).toNat+64=p.sp.toNat:=by
  rw[scratch_nat p hn]
  have hlo:=hn.spLower
  omega

theorem scratch_add (p : Layout) (hn : Native p) (n : Nat) (h:n≤64) :
    (scratch p+UInt32.ofNat n).toNat=(scratch p).toNat+n := by
  have he:=scratch_end p hn
  have hlt:=UInt32.toNat_lt p.sp
  rw[UInt32.toNat_add]
  simp only[UInt32.toNat_ofNat',Nat.reducePow]
  have nh:n<4294967296:=by omega
  rw[Nat.mod_eq_of_lt nh,Nat.mod_eq_of_lt (by omega)]

theorem payload_numbers (p : Layout) (hn : Native p) :
    (payloadPointer p).toNat=p.pointer.toNat+4 ∧(remaining p).toNat=p.length.toNat-4 ∧
    (count p).toNat≤(remaining p).toNat ∧4≤p.length.toNat ∧
    (payloadPointer p).toNat+(count p).toNat≤p.memory.byteSize := by
  have plen:=hn.lengthAccepted
  have pb:=hn.payloadBound
  have width:=hn.memoryWidth
  have lt:=UInt32.toNat_lt p.length
  have positive:0<(count p).toNat:=by
    have h:=hn.countPositive
    by_contra no
    have e:(count p).toNat=0:=by omega
    have eq:count p=0:=UInt32.toNat_inj.mp e
    exact h eq
  have add:(payloadPointer p).toNat=p.pointer.toNat+4:=by
    unfold payloadPointer
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have sub:(remaining p).toNat=p.length.toNat-4:=by
    unfold remaining
    rw[UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨add,sub,by omega,by omega,by omega⟩
end WNear.Proofs.StateDecodePrefix
