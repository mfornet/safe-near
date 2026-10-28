import Proofs.StateReadOuterReleaseVectorFinal

/-! Original storage allocation bounds derive every release address and memory
extent before examining any heap word changed by the prefix allocation. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 decodedMemory outputMemory packedMemory actualDecoder
 actualRelease releaseBase actualVector

theorem outputMemory_shape(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):
    (outputMemory p).wf ∧(outputMemory p).byteSize=(packedMemory p).byteSize ∧
    (outputMemory p).max=(packedMemory p).max:=by
  have shape:=StateDecodeBorshRead.finalMemory_spec (actualDecoder p) (actualAllocation p)
    (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb)
  have wf:(decodedMemory p).wf:=by simpa only [decodedMemory] using shape.1
  have size:(decodedMemory p).byteSize=(packedMemory p).byteSize:=by simpa only [decodedMemory,actualDecoder_memory] using shape.2.1
  have max:(decodedMemory p).max=(packedMemory p).max:=by simpa only [decodedMemory,actualDecoder_memory] using shape.2.2
  have packed:=packed_shape p hn
  have grows:=storage_grows p hn
  have out:=hn.outputBound
  have copy:=ForwardCopyMemory.spec (decodedMemory p) p.out219.toNat (scratch p+48).toNat 40 wf
    (by rw [size,packed.2.1];omega)
  simpa only [outputMemory] using And.intro copy.1 (And.intro (copy.2.1.trans size) (copy.2.2.1.trans max))

theorem release_pointer_span(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):
    p.memory.byteSize≤(actualRelease p).pointer.toNat ∧
    (actualRelease p).pointer.toNat+29≤(outputMemory p).byteSize:=by
  have pointer:=(release_vector p hn state hw hb).1.trans (decoder_record p hn state hb).1
  have above:=StateReadStorageOuter.registered_pointer_above p.toStorage hn.storage hn.allocator
  have span:=storage_final_payload_span p.toStorage hn.storage hn.allocator
  rw [hb,StateReadHeaderBytes.header_length] at span
  have shape:=outputMemory_shape p hn state hw hb
  have packed:=packed_shape p hn
  rw [pointer]
  refine ⟨above,?_⟩
  rw [shape.2.1,packed.2.1]
  simpa only [storageMemory] using span

theorem release_address_numbers(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):
    (actualRelease p).header.toNat+8=(actualRelease p).pointer.toNat ∧
    (actualRelease p).previousAddress.toNat=(actualRelease p).header.toNat+4:=by
  have above:=(release_pointer_span p hn state hw hb).1
  have lower:=hn.spLower
  have bound:=hn.spBound
  have lt:=(actualRelease p).pointer.toNat_lt
  have header:(actualRelease p).header=(actualRelease p).pointer+4294967288:=by
    simp only [actualRelease,releaseBase]
  have previous:(actualRelease p).previousAddress=(actualRelease p).pointer+4294967292:=by
    simp only [actualRelease,releaseBase]
  have hnat:(actualRelease p).header.toNat=(actualRelease p).pointer.toNat-8:=by
    rw [header,UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have pnat:(actualRelease p).previousAddress.toNat=(actualRelease p).pointer.toNat-4:=by
    rw [previous,UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨by omega,by omega⟩
end WNear.Proofs.StateReadOuter
