import Proofs.StateDecodeBorshValues
import Proofs.StateDecodeBorshOutputRecord
import Proofs.StateDecodePrefixHeader

/-! The original model header supplies the real425 supply/usage values.
No decoded-state or successful-execution predicate is an assumption. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI64 finalMemory wideLow wideHigh usageValue

theorem header_count(p:Layout)(state:WNear.State)(hw:state.WF)
    (h:StateReadHeaderBytes.At p.memory p.pointer.toNat state):count p=1:=
  StateDecodePrefix.count_header p.toPrefix state hw h

theorem header_scalar_values(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    (wideLow p q).toNat+2^64*(wideHigh p q).toNat=state.totalSupply ∧
    usageValue p q=UInt64.ofNat state.accountStorageUsage:=by
  have values:=scalar_values_original p q hn hd hheap hroot
  have n:count p=1:=header_count p state hw h
  have one:(count p).toNat=1:=by rw[n];rfl
  rw[one] at values
  have low:p.pointer.toNat+4+1=p.pointer.toNat+5:=by omega
  have high:p.pointer.toNat+4+1+8=p.pointer.toNat+13:=by omega
  have usage:p.pointer.toNat+20+1=p.pointer.toNat+21:=by omega
  rw[low,high,usage] at values
  have header:=StateReadHeaderBytes.read_header p.memory p.pointer.toNat state hw h
  have supply:=header.2.2.1
  unfold TotalSupply.U128At at supply
  have addr:p.pointer.toNat+5+8=p.pointer.toNat+13:=by omega
  rw[addr] at supply
  exact ⟨by rw[values.1,values.2.1];exact supply,values.2.2.trans header.2.2.2⟩

theorem finalMemory_header_scalars(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    readI32 (finalMemory p q) p.out425.toNat=0 ∧
    TotalSupply.U128At (finalMemory p q) (p.out425.toNat+8) state.totalSupply ∧
    readI64 (finalMemory p q) (p.out425.toNat+24)=UInt64.ofNat state.accountStorageUsage:=by
  have values:=header_scalar_values p q hn hd state hw h hheap hroot
  have record:=finalMemory_record p q hn hd
  refine ⟨record.1,?_,record.2.2.2.1.trans values.2⟩
  unfold TotalSupply.U128At
  have add:p.out425.toNat+8+8=p.out425.toNat+16:=by omega
  rw[add,record.2.1,record.2.2.1]
  exact values.1
end WNear.Proofs.StateDecodeBorsh
