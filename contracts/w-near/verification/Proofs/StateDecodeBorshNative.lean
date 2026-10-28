import Proofs.StateDecodeBorshState

/-! Native arithmetic for425's original96-byte frame and complete Borsh header.
No post-callee state or decoded-value predicate is assumed. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic

theorem scratch_numbers(p:Layout)(hn:Native p):
    (scratch p).toNat=p.sp425.toNat-96 ∧(scratch p).toNat+96=p.sp425.toNat ∧
    (scratch p).toNat+96≤p.memory.byteSize ∧scratch p+96=p.sp425:=by
  have lo:=hn.spLower
  have lt:=p.sp425.toNat_lt
  have eq:(scratch p).toNat=p.sp425.toNat-96:=by
    rw[scratch,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨eq,by omega,by have b:=hn.spBound;omega,UInt32.sub_add_cancel p.sp425 96⟩

theorem scratch_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<96):
    (scratch p+UInt32.ofNat offset).toNat=(scratch p).toNat+offset:=by
  have n:=scratch_numbers p hn
  have lt:=p.sp425.toNat_lt
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

theorem output_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<44):
    (p.out425+UInt32.ofNat offset).toNat=p.out425.toNat+offset:=by
  have b:=hn.outBound
  have w:=hn.prefixNative.child.memoryWidth
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

def widePointer(p:Layout):=StateDecodePrefix.payloadPointer p.toPrefix+count p
def wideLength(p:Layout):=StateDecodePrefix.remaining p.toPrefix-count p

theorem header_numbers(p:Layout)(hn:Native p):
    (widePointer p).toNat=p.pointer.toNat+4+(count p).toNat ∧
    (wideLength p).toNat=p.length.toNat-4-(count p).toNat ∧
    24≤(wideLength p).toNat ∧
    (widePointer p).toNat+24≤p.memory.byteSize ∧p.sp425.toNat≤(widePointer p).toNat:=by
  have old:=StateDecodePrefix.payload_numbers p.toPrefix hn.prefixNative.child
  have b:=hn.headerBound
  have len:=hn.headerLength
  have w:=hn.prefixNative.child.memoryWidth
  have llt:=p.length.toNat_lt
  have source:=hn.sourceAbove
  have pointer:(widePointer p).toNat=p.pointer.toNat+4+(count p).toNat:=by
    rw[widePointer,UInt32.toNat_add,old.1]
    exact Nat.mod_eq_of_lt (by omega)
  have length:(wideLength p).toNat=p.length.toNat-4-(count p).toNat:=by
    rw[wideLength,UInt32.toNat_sub,old.2.1]
    simp only[Nat.reducePow]
    omega
  exact ⟨pointer,length,by omega,by omega,by omega⟩

def narrowPointer(p:Layout):=widePointer p+16
def narrowLength(p:Layout):=wideLength p-16

theorem narrow_numbers(p:Layout)(hn:Native p):
    (narrowPointer p).toNat=p.pointer.toNat+20+(count p).toNat ∧
    (narrowLength p).toNat=p.length.toNat-20-(count p).toNat ∧
    8≤(narrowLength p).toNat ∧
    (narrowPointer p).toNat+8≤p.memory.byteSize ∧p.sp425.toNat≤(narrowPointer p).toNat:=by
  have h:=header_numbers p hn
  have w:=hn.prefixNative.child.memoryWidth
  have pointer:(narrowPointer p).toNat=(widePointer p).toNat+16:=by
    rw[narrowPointer,UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by omega)
  have length:(narrowLength p).toNat=(wideLength p).toNat-16:=by
    rw[narrowLength,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have lt:=(wideLength p).toNat_lt
    omega
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩
end WNear.Proofs.StateDecodeBorsh
