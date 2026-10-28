import Proofs.StateReadOuterReleaseVector
import Proofs.StateReadOuterDomain
import Proofs.StateDecodeBorshReadIntervalFrame

/-! The actual161 decode and219 result copy retain the saved storage vector.
Every heap/decoder domain is reconstructed from the original219 input. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 actualDecoder actualAllocation packedMemory
 decodedMemory outputMemory actualVector releaseBase actualRelease

theorem allocation_head_nat(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):
    (AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p).toPositive)).toNat=p.memory.byteSize:=by
  have native:=allocation_native p hn state hw hb
  have pos:=native.vector.raw.allocation
  have head:=AllocatePositive.saved_head_original (actualAllocation p).toPositive pos.wf pos.spLower pos.spBound
  have root:(actualAllocation p).allocator=p.allocator:=by
    simp only [actualAllocation];exact hn.allocationRoot
  rw [head,actualAllocation_memory,root]
  exact packed_root_nat p hn

theorem decoded_vector_byte(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state)(j:Nat)
    (hlo:(scratch p).toNat+24≤j)(hhi:j<(scratch p).toNat+32):
    (decodedMemory p).read8 j=(packedMemory p).read8 j:=by
  have nums:=scratch_numbers p hn
  have sp:(actualDecoder p).sp161=scratch p:=by simpa only [actualDecoder] using hn.decoderSP
  have out:(actualDecoder p).out161.toNat=(scratch p).toNat+40:=by
    have eq:(actualDecoder p).out161=scratch p+40:=by simpa only [actualDecoder] using hn.decoderOut
    rw [eq,UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by have lt:=p.sp219.toNat_lt;omega)
  have root:(actualAllocation p).allocator=p.allocator:=by simp only [actualAllocation];exact hn.allocationRoot
  have frame:=StateDecodeBorshRead.finalMemory_below_head (actualDecoder p) (actualAllocation p)
    (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb) j
    (by rw [sp];omega) (by rw [allocation_head_nat p hn state hw hb];omega)
    (Or.inl (by rw [root,hn.allocator];change j<1074896;have cb:=hn.callbackAbove;omega))
    (Or.inl (by rw [out];omega))
  simpa only [decodedMemory,actualDecoder_memory] using frame

theorem output_vector_byte(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state)(j:Nat)
    (hlo:(scratch p).toNat+24≤j)(hhi:j<(scratch p).toNat+32):
    (outputMemory p).read8 j=(packedMemory p).read8 j:=by
  have shape:=StateDecodeBorshRead.finalMemory_spec (actualDecoder p) (actualAllocation p)
    (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb)
  have size:(decodedMemory p).byteSize=(packedMemory p).byteSize:=by
    simpa only [decodedMemory,actualDecoder_memory] using shape.2.1
  have wf:(decodedMemory p).wf:=by simpa only [decodedMemory] using shape.1
  have nums:=scratch_numbers p hn
  have grows:=storage_grows p hn
  have packed:=packed_shape p hn
  have out:=hn.outputBound
  have copy:=ForwardCopyMemory.spec (decodedMemory p) p.out219.toNat (scratch p+48).toNat 40 wf
    (by rw [size,packed.2.1];omega)
  have below:j<p.out219.toNat:=by have above:=hn.outputAbove;omega
  unfold outputMemory
  exact (copy.2.2.2 j (Or.inl below)).trans (decoded_vector_byte p hn state hw hb j hlo hhi)

theorem release_vector(p:Layout)(hn:Native p)(state:WNear.State)(hw:state.WF)
    (hb:p.bytes=WNear.header state):
    (actualRelease p).pointer=(actualDecoder p).pointer ∧(actualRelease p).length=29:=by
  have nums:=scratch_numbers p hn
  have address:(scratch p+24).toNat=(scratch p).toNat+24:=by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by have lt:=p.sp219.toNat_lt;omega)
  have words:=packed_storage_vector p hn state hb
  have frame(k:Nat)(hk:k=24 ∨k=28):
      readI32 (outputMemory p) ((scratch p).toNat+k)=readI32 (packedMemory p) ((scratch p).toNat+k):=by
    apply readI32_congr_bytes
    intro i hi
    exact output_vector_byte p hn state hw hb _ (by omega) (by omega)
  have pointer:(actualRelease p).pointer=readI32 (outputMemory p) ((scratch p).toNat+24):=by
    simp only [actualRelease,releaseBase,actualVector,VectorDropPositive.pointer,address]
  have length:(actualRelease p).length=readI32 (outputMemory p) ((scratch p).toNat+28):=by
    simp only [actualRelease,releaseBase,actualVector,VectorDropPositive.capacity,address]
  exact ⟨pointer.trans ((frame 24 (Or.inl rfl)).trans words.1),length.trans ((frame 28 (Or.inr rfl)).trans words.2.1)⟩
end WNear.Proofs.StateReadOuter
