import Proofs.StateDecodeBorshMemoryNative
import Proofs.StorePairReadback
import Proofs.PanicAllocateReadback

/-! Canonical425 output words follow from its cached values, even when the
caller output aliases prior descriptor or payload bytes. -/
namespace WNear.Proofs.StateDecodeBorsh.OutputRecord
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

def recordMemory(m:Memory)(out:Nat)(high low usage packed:UInt64)(length:UInt32):=
  let m1:=writeI64 m (out+16) high
  let m2:=writeI64 m1 (out+8) low
  let m3:=writeI64 m2 (out+24) usage
  let m4:=writeI64 m3 (out+32) packed
  let m5:=writeI32 m4 (out+40) length
  writeI32 m5 out 0

private theorem record_bytes(m:Memory)(out:Nat)(high low usage packed:UInt64)(length:UInt32)
    (hw:m.wf)(hb:out+44≤m.byteSize)(j:Nat):
    (recordMemory m out high low usage packed length).read8 j=
      if out≤j ∧j<out+4 then UInt8.ofNat ((0:UInt32).toNat >>>(8*(j-out)))
      else if out+40≤j ∧j<out+44 then UInt8.ofNat (length.toNat >>>(8*(j-(out+40))))
      else if out+32≤j ∧j<out+40 then UInt8.ofNat (packed.toNat >>>(8*(j-(out+32))))
      else if out+24≤j ∧j<out+32 then UInt8.ofNat (usage.toNat >>>(8*(j-(out+24))))
      else if out+8≤j ∧j<out+16 then UInt8.ofNat (low.toNat >>>(8*(j-(out+8))))
      else if out+16≤j ∧j<out+24 then UInt8.ofNat (high.toNat >>>(8*(j-(out+16))))
      else m.read8 j:=by
  let m1:=writeI64 m (out+16) high
  let m2:=writeI64 m1 (out+8) low
  let m3:=writeI64 m2 (out+24) usage
  let m4:=writeI64 m3 (out+32) packed
  let m5:=writeI32 m4 (out+40) length
  have s1:=writeI64_spec m (out+16) high hw (by omega)
  have s2:=writeI64_spec m1 (out+8) low s1.1 (by change _≤(writeI64 _ _ _).byteSize;rw[s1.2.1];omega)
  have s3:=writeI64_spec m2 (out+24) usage s2.1 (by change _≤(writeI64 _ _ _).byteSize;rw[s2.2.1,s1.2.1];omega)
  have s4:=writeI64_spec m3 (out+32) packed s3.1 (by change _≤(writeI64 _ _ _).byteSize;rw[s3.2.1,s2.2.1,s1.2.1];omega)
  have s5:=writeI32_spec m4 (out+40) length s4.1 (by change _≤(writeI64 _ _ _).byteSize;rw[s4.2.1,s3.2.1,s2.2.1,s1.2.1];omega)
  have s6:=writeI32_spec m5 out 0 s5.1 (by change _≤(writeI32 _ _ _).byteSize;rw[s5.2.1,s4.2.1,s3.2.1,s2.2.1,s1.2.1];omega)
  change (writeI32 m5 out 0).read8 j=_
  rw[s6.2.2.2,s5.2.2.2,s4.2.2.2,s3.2.2.2,s2.2.2.2,s1.2.2.2]

private theorem record_word(m:Memory)(out:Nat)(high low usage packed:UInt64)(length:UInt32)
    (hw:m.wf)(hb:out+44≤m.byteSize)(offset:Nat)(ho:offset=8 ∨offset=16 ∨offset=24 ∨offset=32):
    readI64 (recordMemory m out high low usage packed length) (out+offset)=
      (if offset=8 then low else if offset=16 then high else if offset=24 then usage else packed):=by
  rcases ho with rfl|rfl|rfl|rfl
  · apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_left (by omega)]
    have sub:out+8+i-(out+8)=i:=by omega
    simp only[sub,Nat.reduceEqDiff,ite_false,ite_true]
  · apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_left (by omega)]
    have sub:out+16+i-(out+16)=i:=by omega
    simp only[sub,Nat.reduceEqDiff,ite_false,ite_true]
  · apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_left (by omega)]
    have sub:out+24+i-(out+24)=i:=by omega
    simp only[sub,Nat.reduceEqDiff,ite_false,ite_true]
  · apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_right (by omega)]
    rw[ite_eq_left (by omega)]
    have sub:out+32+i-(out+32)=i:=by omega
    simp only[sub,Nat.reduceEqDiff,ite_false]
theorem record_readback(m:Memory)(out:Nat)(high low usage packed:UInt64)(length:UInt32)
    (hw:m.wf)(hb:out+44≤m.byteSize):
    readI32 (recordMemory m out high low usage packed length) out=0 ∧
    readI64 (recordMemory m out high low usage packed length) (out+8)=low ∧
    readI64 (recordMemory m out high low usage packed length) (out+16)=high ∧
    readI64 (recordMemory m out high low usage packed length) (out+24)=usage ∧
    readI64 (recordMemory m out high low usage packed length) (out+32)=packed ∧
    readI32 (recordMemory m out high low usage packed length) (out+40)=length:=by
  have tag:readI32 (recordMemory m out high low usage packed length) out=0:=by
    apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb,ite_eq_left (by omega)]
    rw[Nat.add_sub_cancel_left]
  have len:readI32 (recordMemory m out high low usage packed length) (out+40)=length:=by
    apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw[record_bytes m out high low usage packed length hw hb,ite_eq_right (by omega),ite_eq_left (by omega)]
    have sub:out+40+i-(out+40)=i:=by omega
    rw[sub]
  exact ⟨tag,record_word m out high low usage packed length hw hb 8 (Or.inl rfl),
    record_word m out high low usage packed length hw hb 16 (Or.inr (Or.inl rfl)),
    record_word m out high low usage packed length hw hb 24 (Or.inr (Or.inr (Or.inl rfl))),
    record_word m out high low usage packed length hw hb 32 (Or.inr (Or.inr (Or.inr rfl))),len⟩

end WNear.Proofs.StateDecodeBorsh.OutputRecord

namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 cachedMemory wideHigh wideLow usageValue vectorPacked vectorLength finalMemory

theorem finalMemory_record(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    readI32 (finalMemory p q) p.out425.toNat=0 ∧
    readI64 (finalMemory p q) (p.out425.toNat+8)=wideLow p q ∧
    readI64 (finalMemory p q) (p.out425.toNat+16)=wideHigh p q ∧
    readI64 (finalMemory p q) (p.out425.toNat+24)=usageValue p q ∧
    readI64 (finalMemory p q) (p.out425.toNat+32)=vectorPacked p q ∧
    readI32 (finalMemory p q) (p.out425.toNat+40)=vectorLength p q:=by
  have a40:(p.out425+40).toNat=p.out425.toNat+40:=output_add p hn 40 (by omega)
  have a32:(p.out425+32).toNat=p.out425.toNat+32:=output_add p hn 32 (by omega)
  have a24:(p.out425+24).toNat=p.out425.toNat+24:=output_add p hn 24 (by omega)
  have a8:(p.out425+8).toNat=p.out425.toNat+8:=output_add p hn 8 (by omega)
  have a16:(p.out425+16).toNat=p.out425.toNat+16:=output_add p hn 16 (by omega)
  have equal:finalMemory p q=OutputRecord.recordMemory (cachedMemory p q) p.out425.toNat
      (wideHigh p q) (wideLow p q) (usageValue p q) (vectorPacked p q) (vectorLength p q):=by
    unfold finalMemory output40Memory output32Memory output24Memory output8Memory output16Memory OutputRecord.recordMemory
    rw[a40,a32,a24,a8,a16]
  have spec:=cachedMemory_spec p q hn hd
  rw[equal]
  exact OutputRecord.record_readback (cachedMemory p q) p.out425.toNat (wideHigh p q) (wideLow p q)
    (usageValue p q) (vectorPacked p q) (vectorLength p q) spec.1 (by rw[spec.2.1];exact hn.outBound)
end WNear.Proofs.StateDecodeBorsh
