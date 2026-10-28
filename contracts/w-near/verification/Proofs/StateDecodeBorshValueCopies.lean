import Proofs.StateDecodeBorshSourceFrame
import Proofs.AllocateLayoutWrapperReadback

/-! Byte-level reconstruction of the actual overlapping-word scratch copies. -/
namespace WNear.Proofs.StateDecodeBorsh.ValueCopies
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem word_eq(m n:Memory)(a b:Nat)
    (h:∀i,i<8→m.read8 (a+i)=n.read8 (b+i)):
    readI64 m a=readI64 n b:=by
  have h0:=h 0 (by omega)
  simp only[Nat.add_zero] at h0
  simp [readI64,List.range_succ,h,h0]

private theorem read32_byte(m:Memory)(a i:Nat)(hi:i<4):
    UInt8.ofNat ((readI32 m a).toNat >>> (8*i))=m.read8 (a+i):=by
  have b:∀j,(m.read8 (a+j)).toNat<256:=fun j=>UInt8.toNat_lt _
  apply UInt8.toNat_inj.mp
  have cases:i=0∨i=1∨i=2∨i=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl <;>
    simp [readI32,List.range_succ,Nat.shiftRight_eq_div_pow] <;>
    have h0:=b 0 <;> have h1:=b 1 <;> have h2:=b 2 <;> have h3:=b 3 <;>
    simp only[Nat.add_zero] at * <;> omega

def wideFirst(m:Memory)(r:Nat):=writeI64 m (r+40) (readI64 m (r+68))
def wideSecond(m:Memory)(r:Nat):=writeI32 (wideFirst m r) (r+48) (readI32 (wideFirst m r) (r+76))
def wideSaved(m:Memory)(r:Nat):=writeI64 (wideSecond m r) (r+32) (readI64 (wideSecond m r) (r+60))

theorem wide_words(m:Memory)(r:Nat)(hw:m.wf)(hb:r+80≤m.byteSize):
    readI64 (wideSaved m r) (r+36)=readI64 m (r+64) ∧
    readI64 (wideSaved m r) (r+44)=readI64 m (r+72):=by
  have first:=writeI64_spec m (r+40) (readI64 m (r+68)) hw (by omega)
  have second:=writeI32_spec (wideFirst m r) (r+48) (readI32 (wideFirst m r) (r+76)) first.1 (by unfold wideFirst;rw[first.2.1];omega)
  have last:=writeI64_spec (wideSecond m r) (r+32) (readI64 (wideSecond m r) (r+60)) second.1 (by unfold wideSecond;rw[second.2.1];unfold wideFirst;rw[first.2.1];omega)
  have source2:readI32 (wideFirst m r) (r+76)=readI32 m (r+76):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold wideFirst;rw[first.2.2.2]
    exact ite_eq_right (by omega)
  have source3:readI64 (wideSecond m r) (r+60)=readI64 m (r+60):=by
    apply readI64_congr_bytes
    intro i hi
    unfold wideSecond;rw[second.2.2.2,ite_eq_right (by omega)]
    unfold wideFirst;rw[first.2.2.2]
    exact ite_eq_right (by omega)
  have bytes(j:Nat)(hlo:r+32≤j)(hhi:j<r+52):
      (wideSaved m r).read8 j=m.read8 (j+28):=by
    unfold wideSaved
    rw[last.2.2.2,source3]
    by_cases h:j<r+40
    · rw[ite_eq_left (by omega),AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega)]
      congr 1;omega
    · rw[ite_eq_right (by omega)]
      unfold wideSecond
      rw[second.2.2.2,source2]
      by_cases h2:r+48≤j
      · rw[ite_eq_left (by omega),read32_byte _ _ _ (by omega)]
        congr 1;omega
      · rw[ite_eq_right (by omega)]
        unfold wideFirst
        rw[first.2.2.2,ite_eq_left (by omega),AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega)]
        congr 1;omega
  constructor
  · apply word_eq
    intro i hi
    have h:=bytes (r+36+i) (by omega) (by omega)
    simpa only[Nat.add_assoc,show 36+i+28=64+i by omega] using h
  · apply word_eq
    intro i hi
    have h:=bytes (r+44+i) (by omega) (by omega)
    simpa only[Nat.add_assoc,show 44+i+28=72+i by omega] using h

def narrowHigh(m:Memory)(r:Nat):=writeI32 m (r+88) (readI32 m (r+68))
def narrowSaved(m:Memory)(r:Nat):=writeI64 (narrowHigh m r) (r+80) (readI64 (narrowHigh m r) (r+60))

theorem narrow_word(m:Memory)(r:Nat)(hw:m.wf)(hb:r+92≤m.byteSize):
    readI64 (narrowSaved m r) (r+84)=readI64 m (r+64):=by
  have first:=writeI32_spec m (r+88) (readI32 m (r+68)) hw (by omega)
  have last:=writeI64_spec (narrowHigh m r) (r+80) (readI64 (narrowHigh m r) (r+60)) first.1 (by unfold narrowHigh;rw[first.2.1];omega)
  have source:readI64 (narrowHigh m r) (r+60)=readI64 m (r+60):=by
    apply readI64_congr_bytes
    intro i hi
    unfold narrowHigh;rw[first.2.2.2]
    exact ite_eq_right (by omega)
  apply word_eq
  intro i hi
  unfold narrowSaved
  rw[last.2.2.2,source]
  by_cases h:i<4
  · rw[ite_eq_left (by omega),AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega)]
    congr 1;omega
  · rw[ite_eq_right (by omega)]
    unfold narrowHigh
    rw[first.2.2.2,ite_eq_left (by omega),read32_byte _ _ _ (by omega)]
    congr 1;omega
end WNear.Proofs.StateDecodeBorsh.ValueCopies
