import Proofs.StateReadOuterAllocationFactory
import Proofs.AllocationGrowthRemainderStorageEnd

/-! The actual548 growing remainder survives219's concrete descriptor copies.
The decoder allocation Native follows from ORIGINAL219 data and header bytes;
there is no input proposition about a future allocator heap or execution. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 packedMemory
  StateReadStorageOuter.finalMemory preparedStorageMemory

 theorem storage_output_root_separated(p:Layout)(hn:Native p):
    p.out548.toNat+12≤p.allocator.toNat:=by
  have nums:=scratch_numbers p hn
  have add:(scratch p+8).toNat=(scratch p).toNat+8:=by
    simpa only[show UInt32.ofNat 8=8 by rfl] using scratch_add p hn 8 (by omega)
  have above:=hn.callbackAbove
  rw[hn.storageOut,add,hn.allocator]
  change (scratch p).toNat+8+12≤1074896
  omega

 theorem packed_byte_frame(p:Layout)(hn:Native p)(j:Nat)
    (above:(scratch p).toNat+36≤j):
    (packedMemory p).read8 j=(storageMemory p).read8 j:=by
  have nums:=scratch_numbers p hn
  have shape:=storage_wf_width p hn
  have grow:=storage_grows p hn
  have lt:=p.sp219.toNat_lt
  have prep:=preparedMemory_local_spec (storageMemory p) (scratch p) shape.1 (by omega) (by omega)
  unfold packedMemory
  exact prep.2.2.2 j (Or.inr above)

 theorem packed_word_frame(p:Layout)(hn:Native p)(address:Nat)
    (above:(scratch p).toNat+36≤address):
    readI32 (packedMemory p) address=readI32 (storageMemory p) address:=by
  apply readI32_congr_bytes
  intro i hi
  exact packed_byte_frame p hn (address+i) (by omega)

 theorem packed_root(p:Layout)(hn:Native p):
    readI32 (packedMemory p) p.allocator.toNat=readI32 (storageMemory p) p.allocator.toNat:=by
  apply packed_word_frame p hn
  have nums:=scratch_numbers p hn
  have above:=hn.callbackAbove
  rw[hn.allocator]
  change (scratch p).toNat+36≤1074896
  omega

 theorem packed_root_nat(p:Layout)(hn:Native p):
    (readI32 (packedMemory p) p.allocator.toNat).toNat=p.memory.byteSize:=by
  have original:=StateReadStorageOuter.finalMemory_root_nat p.toStorage hn.storage hn.allocator
    (Or.inl (storage_output_root_separated p hn))
  have root:=packed_root p hn
  exact (congrArg UInt32.toNat root).trans original

 theorem packed_end_eq(p:Layout)(hn:Native p):
    Allocate.endWord (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat)=
      Allocate.endWord (storageMemory p) (readI32 (storageMemory p) p.allocator.toNat):=by
  have nums:=scratch_numbers p hn
  have bound:=hn.spBound
  have word:=packed_word_frame p hn p.memory.byteSize (by omega)
  have original:=StateReadStorageOuter.finalMemory_root_nat p.toStorage hn.storage hn.allocator
    (Or.inl (storage_output_root_separated p hn))
  exact WNear.Proofs.AllocationGrowthRemainder.end_eq_of_words _ _ _ _ _
    (packed_root_nat p hn) original word

 theorem packed_one_word(p:Layout)(hn:Native p)(size:p.size=29):
    Allocate.SplitNative (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat) 1:=by
  have original:=StateReadStorageOuter.finalMemory_one_word p.toStorage hn.storage hn.allocator size
    (Or.inl (storage_output_root_separated p hn))
  have root:=packed_root p hn
  have endEq:=packed_end_eq p hn
  have shape:=packed_shape p hn
  refine ⟨original.wordsPositive,?_,?_⟩
  · rw[endEq,root]
    exact original.room
  · rw[endEq,shape.2.1]
    exact original.endBound

 theorem packed_end_bound(p:Layout)(hn:Native p):
    (Allocate.endWord (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat)).toNat+8≤(packedMemory p).byteSize:=by
  have original:=StateReadStorageOuter.finalMemory_end_bound p.toStorage hn.storage hn.allocator
    (Or.inl (storage_output_root_separated p hn))
  rw[packed_end_eq p hn,(packed_shape p hn).2.1]
  exact original

 theorem packed_head_flags(p:Layout)(hn:Native p):
    readI32 (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat).toNat&&&3=0:=by
  have nums:=scratch_numbers p hn
  have bound:=hn.spBound
  have word:=packed_word_frame p hn p.memory.byteSize (by omega)
  have original:=StateReadStorageOuter.finalMemory_head_flags p.toStorage hn.storage hn.allocator
  rw[packed_root_nat p hn,word]
  exact original

 theorem packed_candidate_flag(p:Layout)(hn:Native p):
    readI32 (packedMemory p) ((readI32 (packedMemory p) p.allocator.toNat).toNat+8)&&&1=0:=by
  have nums:=scratch_numbers p hn
  have bound:=hn.spBound
  have word:=packed_word_frame p hn (p.memory.byteSize+8) (by omega)
  have original:=StateReadStorageOuter.finalMemory_candidate_flag p.toStorage hn.storage hn.allocator
  rw[packed_root_nat p hn,word]
  exact original

/-- The complete real374 domain is reconstructed from original219 resources,
including its original empty-head growth allocation and canonical stored header. -/
 theorem allocation_native(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (bytes:p.bytes=WNear.header state):StateDecodeVectorCopy.Native (actualAllocation p):=by
  have size:p.size=29:=by
    rw[hn.storage.register.size,bytes,StateReadHeaderBytes.header_length]
    rfl
  apply allocation_native_of_heap p hn (decoder_native p hn state hw bytes) (decoder_count p hn state hw bytes)
    (packed_one_word p hn size) (packed_end_bound p hn) (packed_head_flags p hn) (packed_candidate_flag p hn)
  exact Nat.le_of_eq (packed_root_nat p hn).symm
end WNear.Proofs.StateReadOuter
