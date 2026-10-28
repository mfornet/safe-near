import Proofs.StateReadOuterStorageWidth
import Proofs.StateReadOuterGeometry

/-! The actual decoder's original native domain follows from219's original
storage domain and canonical model header. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 storageMemory packedMemory actualDecoder
 StateReadStorageOuter.finalMemory StateReadStorageOuter.registeredMemory

theorem storage_grows(p:Layout)(hn:Native p):p.memory.byteSize≤(storageMemory p).byteSize:=by
  simpa only [storageMemory] using storage_final_grows p.toStorage hn.storage hn.allocator

theorem storage_wf_width(p:Layout)(hn:Native p):
    (storageMemory p).wf ∧(storageMemory p).byteSize≤2^32:=by
  have wf:= (StateReadStorageOuter.finalMemory_shape p.toStorage hn.storage hn.allocator).1
  have width:=storage_final_width p.toStorage hn.storage hn.allocator
  exact ⟨by simpa only [storageMemory] using wf,by simpa only [storageMemory] using width⟩

theorem packed_shape(p:Layout)(hn:Native p):
    (packedMemory p).wf ∧(packedMemory p).byteSize=(storageMemory p).byteSize ∧
    (packedMemory p).max=(storageMemory p).max:=by
  have nums:=scratch_numbers p hn
  have shape:=preparedMemory_spec (storageMemory p) (scratch p)
    (storage_wf_width p hn).1
    (storage_wf_width p hn).2
    (by have grows:=storage_grows p hn;omega)
  simpa only [packedMemory] using (And.intro shape.1 (And.intro shape.2.1 shape.2.2.1))

theorem decoder_header(p:Layout)(hn:Native p)(state:WNear.State)(hb:p.bytes=WNear.header state):
    StateReadHeaderBytes.At (packedMemory p)
      (AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p.toStorage)).toVector).toNat state:=by
  have nums:=scratch_numbers p hn
  simpa only [packedMemory,storageMemory] using
    prepared_storage_header p.toStorage (scratch p) hn.storage hn.allocator state hb (by omega)

theorem decoder_record(p:Layout)(hn:Native p)(state:WNear.State)(hb:p.bytes=WNear.header state):
    (actualDecoder p).pointer=
      AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p.toStorage)).toVector ∧
    (actualDecoder p).length=29:=by
  have nums:=scratch_numbers p hn
  have grows:=storage_grows p hn
  have record:=prepared_record (storageMemory p) (scratch p)
    (storage_wf_width p hn).1
    (storage_wf_width p hn).2 (by omega)
  have low:=StateReadStorageOuter.finalMemory_low_record p.toStorage hn.storage hn.allocator
  have out:p.out548.toNat=(scratch p).toNat+8:=by
    rw [hn.storageOut]
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by have lt:=p.sp219.toNat_lt;omega)
  have bound:=StateReadStorageOuter.result_bounds p.toStorage hn.storage hn.allocator
  have sn:=StateReadStorageOuter.stack_numbers p.toStorage hn.storage
  have srcEq:(StateReadStorageOuter.scratch p.toStorage+16+8).toNat=p.sp548.toNat-16+8:=by
    rw [bound.2.2.2.2.2.2,sn.2.2.2]
  have spEq:p.sp548.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.storageSP
  have source:(StateReadStorageOuter.scratch p.toStorage+16+8).toNat+4≤p.out548.toNat:=by
    rw [srcEq,out]
    have lo:=hn.storage.spLower
    omega
  have high:=StateReadStorageOuter.finalMemory_length p.toStorage hn.storage hn.allocator (Or.inl source)
  have size:p.size=29:=by rw [hn.storage.register.size,hb,StateReadHeaderBytes.header_length];rfl
  have hp:readI32 (storageMemory p) ((scratch p).toNat+8)=
      AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p.toStorage)).toVector:=by
    rw [←out];simpa only [storageMemory] using low.1
  have hl:readI32 (storageMemory p) ((scratch p).toNat+16)=29:=by
    have addr:p.out548.toNat+8=(scratch p).toNat+16:=by omega
    rw [←addr];simpa only [storageMemory] using high.trans size
  refine ⟨?_,?_⟩
  · simp only [actualDecoder_pointer,packedMemory] ; exact record.1.trans hp
  · simp only [actualDecoder_length,packedMemory] ; exact record.2.trans hl

theorem decoder_count(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):decodeCount p=1:=by
  have head:=StateReadHeaderBytes.read_header (packedMemory p)
    (AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p.toStorage)).toVector).toNat
    state hw (decoder_header p hn state hb)
  have pointer:=(decoder_record p hn state hb).1
  unfold decodeCount StateDecodeBorshRead.count StateDecodeBorshWrapper.count StateDecodeBorsh.count StateDecodePrefix.count
  rw [actualDecoder_memory,pointer]
  exact head.1

/-- The complete actual161 domain is derived from original219 data. -/
theorem decoder_native(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):StateDecodeBorshRead.Native (actualDecoder p):=by
  have shape:=packed_shape p hn
  have width:=storage_wf_width p hn
  have grows:=storage_grows p hn
  have nums:=scratch_numbers p hn
  have lo:=hn.spLower
  have record:=decoder_record p hn state hb
  have count:=decoder_count p hn state hw hb
  have geo:=actualDecoder_geometry p hn
  have sp:(actualDecoder p).sp161=scratch p:=by
    simpa only [actualDecoder] using hn.decoderSP
  have out:(actualDecoder p).out161=scratch p+40:=by
    simpa only [actualDecoder] using hn.decoderOut
  have outNat:(actualDecoder p).out161.toNat=(scratch p).toNat+40:=by
    rw [out,UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by have lt:=p.sp219.toNat_lt;omega)
  have above:=StateReadStorageOuter.registered_pointer_above p.toStorage hn.storage hn.allocator
  have span:=storage_final_payload_span p.toStorage hn.storage hn.allocator
  rw [hb,StateReadHeaderBytes.header_length] at span
  have payload:(actualDecoder p).pointer.toNat+29≤(packedMemory p).byteSize:=by
    rw [record.1,shape.2.1]
    simpa only [storageMemory] using span
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,geo.slice,geo.wrapperSP,
    geo.wrapperOut,geo.wrapperGlobal,geo.borshSP,geo.borshOut,geo.borshGlobal,
    geo.prefixSP,geo.prefixOut,geo.prefixGlobal,geo.childSP,geo.childOut,geo.childGlobal⟩
  · rw [actualDecoder_memory];exact shape.1
  · rw [actualDecoder_memory,shape.2.1];exact width.2
  · rw [sp];omega
  · rw [sp,actualDecoder_memory,shape.2.1];omega
  · rw [sp];exact scratch_aligned p hn
  · rw [outNat,actualDecoder_memory,shape.2.1];omega
  · rw [sp,record.1];omega
  · change (actualDecoder p).pointer.toNat+4+(decodeCount p).toNat+24≤(actualDecoder p).memory.byteSize
    rw [count,actualDecoder_memory]
    simp only [UInt32.toNat_ofNat] ;omega
  · change 4+(decodeCount p).toNat+24≤(actualDecoder p).length.toNat
    rw [count,record.2];decide
  · change decodeCount p≠0;rw [count];decide
  · change (decodeCount p).toNat<2^31;rw [count];decide
end WNear.Proofs.StateReadOuter
