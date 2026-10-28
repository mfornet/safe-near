import Proofs.StateDecodeBorshWrapperReadback
import Proofs.StateDecodeBorshHeader

/-! Actual162 supply/usage readback from original model header bytes. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 decodedMemory finalMemory

theorem finalMemory_header_scalars(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hout:p.sp162.toNat≤p.out162.toNat)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodeBorsh.widePointer p.toBorsh).toNat)
    (hroot:(StateDecodeBorsh.widePointer p.toBorsh).toNat+24≤q.allocator.toNat ∨
      q.allocator.toNat+4≤(StateDecodeBorsh.widePointer p.toBorsh).toNat):
    readI32 (finalMemory p q) p.out162.toNat=0 ∧
    TotalSupply.U128At (finalMemory p q) (p.out162.toNat+8) state.totalSupply ∧
    readI64 (finalMemory p q) (p.out162.toNat+24)=UInt64.ofNat state.accountStorageUsage:=by
  have old:=StateDecodeBorsh.finalMemory_header_scalars p.toBorsh q hn.child hd state hw h hheap hroot
  have address:p.out425.toNat=(scratch p).toNat+48:=by
    rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have decoded : readI32 (decodedMemory p q) p.out425.toNat=0 ∧
    TotalSupply.U128At (decodedMemory p q) (p.out425.toNat+8) state.totalSupply ∧
    readI64 (decodedMemory p q) (p.out425.toNat+24)=UInt64.ofNat state.accountStorageUsage := by simpa only[decodedMemory] using old
  rw[address] at decoded
  have words:=(final_record_words p q hn hd hout).1
  refine ⟨finalMemory_tag p q hn hd,?_,(words 24 (by omega)).trans decoded.2.2⟩
  unfold TotalSupply.U128At at *
  have a:p.out162.toNat+8+8=p.out162.toNat+16:=by omega
  have b:(scratch p).toNat+48+8+8=(scratch p).toNat+48+16:=by omega
  rw[a,words 8 (by omega),words 16 (by omega)]
  simpa only[b] using decoded.2.1
end WNear.Proofs.StateDecodeBorshWrapper
