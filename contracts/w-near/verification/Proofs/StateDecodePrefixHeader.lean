import Proofs.StateDecodePrefixPayload
import Proofs.StateReadHeaderBytes

/-! The model's original29-byte header supplies the real accepted vector count
and the accounts-prefix byte in the final allocated316 payload. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] finalMemory payloadAddress StateDecodeRaw.originalFinish

theorem count_header(p:Layout)(state:WNear.State)(hw:state.WF)
    (h:StateReadHeaderBytes.At p.memory p.pointer.toNat state):count p=1:=by
  exact (StateReadHeaderBytes.read_header p.memory p.pointer.toNat state hw h).1

theorem header_payload_byte(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (h:StateReadHeaderBytes.At p.memory p.pointer.toNat state):
    p.memory.read8 (payloadPointer p).toNat=97:=by
  rw[(payload_numbers p hn).1]
  exact (StateReadHeaderBytes.read_header p.memory p.pointer.toNat state hw h).2.1

private theorem byte_zero (m n:Memory)(source destination:Nat)
    (h:n.read8 (destination+0)=m.read8 (source+0))(b:m.read8 source=97):n.read8 destination=97:=by
  simpa only[Nat.add_zero] using h.trans b

theorem final_accounts_prefix(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(payloadPointer p).toNat)
    (hroot:(payloadPointer p).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(payloadPointer p).toNat)
    (hout:p.out.toNat+16≤(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat):
    (finalMemory p q).read8 (payloadAddress p q).toNat=97:=by
  have size:count p=1:=count_header p state hw h
  have positive:0<(count p).toNat:=by rw[size];decide
  have byte:=final_payload_bytes_below_head p q hn hd hheap hroot hout 0 positive
  exact byte_zero p.memory (finalMemory p q) (payloadPointer p).toNat (payloadAddress p q).toNat byte (header_payload_byte p hn state hw h)
end WNear.Proofs.StateDecodePrefix
