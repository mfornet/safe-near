import Proofs.StateReadOuterDecoderNative

/-! Actual219's saved storage vector is prepared from canonical548 results. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 storageMemory packedMemory actualDecoder
 preparedStorageMemory StateReadStorageOuter.finalMemory

theorem packed_storage_vector(p:Layout)(hn:Native p)(state:WNear.State)(hb:p.bytes=WNear.header state):
    readI32 (packedMemory p) ((scratch p).toNat+24)=(actualDecoder p).pointer ∧
    readI32 (packedMemory p) ((scratch p).toNat+28)=29 ∧
    readI32 (packedMemory p) ((scratch p).toNat+32)=29:=by
  have nums:=scratch_numbers p hn
  have grows:=storage_grows p hn
  have shape:=storage_wf_width p hn
  have words:=prepared_storage_vector (storageMemory p) (scratch p) shape.1 shape.2 (by omega)
  have record:=prepared_record (storageMemory p) (scratch p) shape.1 shape.2 (by omega)
  have decoder:=decoder_record p hn state hb
  have out:p.out548.toNat=(scratch p).toNat+8:=by
    rw [hn.storageOut,UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by have lt:=p.sp219.toNat_lt;omega)
  have low:=StateReadStorageOuter.finalMemory_low_record p.toStorage hn.storage hn.allocator
  have size:p.size=29:=by rw [hn.storage.register.size,hb,StateReadHeaderBytes.header_length];rfl
  have cap:readI32 (storageMemory p) ((scratch p).toNat+12)=29:=by
    have addr:p.out548.toNat+4=(scratch p).toNat+12:=by omega
    rw [←addr]
    simpa only [storageMemory] using low.2.trans size
  have pointer:readI32 (storageMemory p) ((scratch p).toNat+8)=(actualDecoder p).pointer:=by
    rw [←record.1]
    simpa only [packedMemory] using (actualDecoder_pointer p).symm
  have length:readI32 (storageMemory p) ((scratch p).toNat+16)=29:=by
    rw [←record.2]
    have eq := (actualDecoder_length p).symm.trans decoder.2
    simpa only [packedMemory] using eq
  simpa only [packedMemory] using And.intro (words.1.trans pointer)
    (And.intro (words.2.1.trans cap) (words.2.2.trans length))
end WNear.Proofs.StateReadOuter
