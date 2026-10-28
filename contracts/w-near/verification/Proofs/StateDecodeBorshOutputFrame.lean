import Proofs.StateDecodeBorshMemoryNative

/-! The final425 cached-output writes affect only their original44-byte span. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 finalMemory cachedMemory
private theorem write32_away(m:Memory)(a:Nat)(v:UInt32)(j:Nat)(hw:m.wf)(hb:a+4≤m.byteSize)
    (hs:j<a ∨a+4≤j):(writeI32 m a v).read8 j=m.read8 j:=by
  rw[(writeI32_spec m a v hw hb).2.2.2]
  exact ite_eq_right (by rcases hs with h|h <;> omega)
private theorem write64_away(m:Memory)(a:Nat)(v:UInt64)(j:Nat)(hw:m.wf)(hb:a+8≤m.byteSize)
    (hs:j<a ∨a+8≤j):(writeI64 m a v).read8 j=m.read8 j:=by
  rw[(writeI64_spec m a v hw hb).2.2.2]
  exact ite_eq_right (by rcases hs with h|h <;> omega)

theorem finalMemory_cached_byte_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hout:j<p.out425.toNat ∨p.out425.toNat+44≤j):
    (finalMemory p q).read8 j=(cachedMemory p q).read8 j:=by
  have bound:=hn.outBound
  have spec0:=cachedMemory_spec p q hn hd
  have a0:(p.out425+16).toNat=p.out425.toNat+16:=output_add p hn 16 (by omega)
  have b0:(p.out425+16).toNat+8≤(cachedMemory p q).byteSize:=by
    rw[spec0.2.1,a0];omega
  have f0:(output16Memory p q).read8 j=(cachedMemory p q).read8 j:=by
    unfold output16Memory
    exact write64_away (cachedMemory p q) (p.out425+16).toNat (wideHigh p q) j spec0.1 b0 (by rw[a0];rcases hout with h|h <;> omega)
  have spec1:=output16Memory_spec p q hn hd
  have a1:(p.out425+8).toNat=p.out425.toNat+8:=output_add p hn 8 (by omega)
  have b1:(p.out425+8).toNat+8≤(output16Memory p q).byteSize:=by
    rw[spec1.2.1,a1];omega
  have f1:(output8Memory p q).read8 j=(output16Memory p q).read8 j:=by
    unfold output8Memory
    exact write64_away (output16Memory p q) (p.out425+8).toNat (wideLow p q) j spec1.1 b1 (by rw[a1];rcases hout with h|h <;> omega)
  have spec2:=output8Memory_spec p q hn hd
  have a2:(p.out425+24).toNat=p.out425.toNat+24:=output_add p hn 24 (by omega)
  have b2:(p.out425+24).toNat+8≤(output8Memory p q).byteSize:=by
    rw[spec2.2.1,a2];omega
  have f2:(output24Memory p q).read8 j=(output8Memory p q).read8 j:=by
    unfold output24Memory
    exact write64_away (output8Memory p q) (p.out425+24).toNat (usageValue p q) j spec2.1 b2 (by rw[a2];rcases hout with h|h <;> omega)
  have spec3:=output24Memory_spec p q hn hd
  have a3:(p.out425+32).toNat=p.out425.toNat+32:=output_add p hn 32 (by omega)
  have b3:(p.out425+32).toNat+8≤(output24Memory p q).byteSize:=by
    rw[spec3.2.1,a3];omega
  have f3:(output32Memory p q).read8 j=(output24Memory p q).read8 j:=by
    unfold output32Memory
    exact write64_away (output24Memory p q) (p.out425+32).toNat (vectorPacked p q) j spec3.1 b3 (by rw[a3];rcases hout with h|h <;> omega)
  have spec4:=output32Memory_spec p q hn hd
  have a4:(p.out425+40).toNat=p.out425.toNat+40:=output_add p hn 40 (by omega)
  have b4:(p.out425+40).toNat+4≤(output32Memory p q).byteSize:=by
    rw[spec4.2.1,a4];omega
  have f4:(output40Memory p q).read8 j=(output32Memory p q).read8 j:=by
    unfold output40Memory
    exact write32_away (output32Memory p q) (p.out425+40).toNat (vectorLength p q) j spec4.1 b4 (by rw[a4];rcases hout with h|h <;> omega)
  have spec5:=output40Memory_spec p q hn hd
  have b5:p.out425.toNat+4≤(output40Memory p q).byteSize:=by
    rw[spec5.2.1];omega
  have f5:(finalMemory p q).read8 j=(output40Memory p q).read8 j:=by
    unfold finalMemory
    exact write32_away (output40Memory p q) p.out425.toNat 0 j spec5.1 b5 (by rcases hout with h|h <;> omega)
  exact f5.trans (f4.trans (f3.trans (f2.trans (f1.trans f0))))
end WNear.Proofs.StateDecodeBorsh
