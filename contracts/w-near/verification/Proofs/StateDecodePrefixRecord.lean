import Proofs.StateDecodePrefixTag
import Proofs.StateDecodePrefixPayload
import Proofs.StateDecodePrefixAfterAllocationReadback

/-! Canonical vector/slice words follow the actual cached and sequential stores.
Caller output and the final slice descriptor are explicitly disjoint. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem snapshot_word (original current : Memory) (out source offset : Nat)
    (hw : current.wf) (hb : out+8≤current.byteSize) (ho : offset+4≤8) :
    readI32 (writeI64 current out (readI64 original source)) (out+offset)=readI32 original (source+offset) := by
  have spec:=writeI64_spec current out (readI64 original source) hw hb
  have bytes (i : Nat) (hi : i<4) :
      (writeI64 current out (readI64 original source)).read8 (out+offset+i)=original.read8 (source+offset+i) := by
    rw[spec.2.2.2]
    have yes:out≤out+offset+i ∧out+offset+i<out+8:=by omega
    rw[ite_eq_left yes]
    have off:out+offset+i-out=offset+i:=by omega
    rw[off,AllocateLayoutWrapperReadback.readI64_byte _ _ (offset+i) (by omega)]
    simp only[Nat.add_assoc]
  have zero:(writeI64 current out (readI64 original source)).read8 (out+offset)=original.read8 (source+offset):=by
    simpa only[Nat.add_zero] using bytes 0 (by omega)
  simp[readI32,List.range_succ,bytes,zero]

theorem finalMemory_record (p : Layout) (hn : Native p)
    (hstack : p.scratch.toNat+64≤p.out.toNat)
    (hsep : p.out.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat) :
    readI32 (finalMemory p) p.out.toNat=0 ∧
    readI32 (finalMemory p) (p.out.toNat+4)=readI32 p.memory (p.scratch.toNat+48) ∧
    readI32 (finalMemory p) (p.out.toNat+8)=readI32 p.memory (p.scratch.toNat+52) ∧
    readI32 (finalMemory p) (p.out.toNat+12)=readI32 p.memory (p.scratch.toNat+56) ∧
    readI32 (finalMemory p) p.slice.toNat=readI32 p.memory (p.scratch.toNat+8) ∧
    readI32 (finalMemory p) (p.slice.toNat+4)=readI32 p.memory (p.scratch.toNat+12) := by
  have specs:=memory_specs p hn
  have hb:(p.out+12).toNat+4≤p.memory.byteSize:=by rw[out_address p hn];exact hn.outBound
  have high:=writeI32_spec p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56)) hn.wf hb
  have lb:p.out.toNat+4+8≤(highMemory p).byteSize:=by rw[specs.2.1];have h:=hn.outBound;omega
  have low:=writeI64_spec (highMemory p) (p.out.toNat+4) (readI64 (highMemory p) (p.scratch.toNat+48)) specs.1 lb
  have tb:p.out.toNat+4≤(lowMemory p).byteSize:=by rw[specs.2.2.2.1];have h:=hn.outBound;omega
  have tag:=writeI32_spec (lowMemory p) p.out.toNat 0 specs.2.2.1 tb
  have db:p.slice.toNat+8≤(tagMemory p).byteSize:=by rw[specs.2.2.2.2.2];exact hn.sliceBound
  have final:=writeI64_spec (tagMemory p) p.slice.toNat (remainder p) specs.2.2.2.2.1 db
  have high_frame (offset : Nat) (ho : offset+4≤64) :
      readI32 (highMemory p) (p.scratch.toNat+offset)=readI32 p.memory (p.scratch.toNat+offset):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold highMemory
    rw[high.2.2.2]
    have no:¬((p.out+12).toNat≤p.scratch.toNat+offset+i ∧p.scratch.toNat+offset+i<(p.out+12).toNat+4):=by rw[out_address p hn];omega
    exact ite_eq_right no
  have final_frame (address : Nat) (ha : p.out.toNat≤address) (he : address+4≤p.out.toNat+16) :
      readI32 (finalMemory p) address=readI32 (tagMemory p) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold finalMemory
    rw[final.2.2.2]
    have no:¬(p.slice.toNat≤address+i ∧address+i<p.slice.toNat+8):=by rcases hsep with h|h <;> omega
    exact ite_eq_right no
  have tag_frame (address : Nat) (ha : p.out.toNat+4≤address) :
      readI32 (tagMemory p) address=readI32 (lowMemory p) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold tagMemory
    rw[tag.2.2.2]
    have no:¬(p.out.toNat≤address+i ∧address+i<p.out.toNat+4):=by omega
    exact ite_eq_right no
  have lo0:=snapshot_word (highMemory p) (highMemory p) (p.out.toNat+4) (p.scratch.toNat+48) 0 specs.1 lb (by omega)
  have lo4:=snapshot_word (highMemory p) (highMemory p) (p.out.toNat+4) (p.scratch.toNat+48) 4 specs.1 lb (by omega)
  have low0:readI32 (lowMemory p) (p.out.toNat+4)=readI32 p.memory (p.scratch.toNat+48):=by
    have eq:readI32 (lowMemory p) (p.out.toNat+4)=readI32 (highMemory p) (p.scratch.toNat+48):=by simpa only[lowMemory,Nat.add_zero] using lo0
    exact eq.trans (high_frame 48 (by omega))
  have low4:readI32 (lowMemory p) (p.out.toNat+8)=readI32 p.memory (p.scratch.toNat+52):=by
    have eq:readI32 (lowMemory p) (p.out.toNat+8)=readI32 (highMemory p) (p.scratch.toNat+52):=by simpa only[lowMemory,Nat.add_assoc] using lo4
    exact eq.trans (high_frame 52 (by omega))
  have highword:readI32 (highMemory p) (p.out.toNat+12)=readI32 p.memory (p.scratch.toNat+56):=by
    have self:=PanicAllocateReadback.read_write_self p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56)) hn.wf hb
    simpa only[highMemory,out_address p hn] using self
  have low_high:readI32 (lowMemory p) (p.out.toNat+12)=readI32 (highMemory p) (p.out.toNat+12):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold lowMemory
    rw[low.2.2.2]
    have no:¬(p.out.toNat+4≤p.out.toNat+12+i ∧p.out.toNat+12+i<p.out.toNat+4+8):=by omega
    exact ite_eq_right no
  have slice0:=snapshot_word p.memory (tagMemory p) p.slice.toNat (p.scratch.toNat+8) 0 specs.2.2.2.2.1 db (by omega)
  have slice4:=snapshot_word p.memory (tagMemory p) p.slice.toNat (p.scratch.toNat+8) 4 specs.2.2.2.2.1 db (by omega)
  refine ⟨finalMemory_tag0 p hn (by rcases hsep with h|h;left;omega;right;exact h),
    (final_frame _ (by omega) (by omega)).trans ((tag_frame _ (by omega)).trans low0),
    (final_frame _ (by omega) (by omega)).trans ((tag_frame _ (by omega)).trans low4),
    (final_frame _ (by omega) (by omega)).trans ((tag_frame _ (by omega)).trans (low_high.trans highword)),?_,?_⟩
  · simpa only[finalMemory,remainder,Nat.add_zero] using slice0
  · simpa only[finalMemory,remainder,Nat.add_assoc] using slice4
end WNear.Proofs.StateDecodePrefix.Output

namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory copiedMemory

theorem finalMemory_record_below_payload (p : Layout) (hn : Native p)
    (hout : p.outVector.toNat+12≤(pointer p).toNat) :
    readI32 (finalMemory p) p.outVector.toNat=pointer p ∧
    readI32 (finalMemory p) (p.outVector.toNat+4)=p.size ∧
    readI32 (finalMemory p) (p.outVector.toNat+8)=p.size := by
  have copied:=copiedMemory_spec p hn
  have final:=finalMemory_spec p hn
  have word (offset : Nat) (ho : offset+4≤8) :
      readI32 (finalMemory p) (p.outVector.toNat+offset)=readI32 (StateDecodeVector.finalMemory p.toVector) (p.outVector.toNat+offset):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    have a:=final.2.2.2.2 (p.outVector.toNat+offset+i) (Or.inl (by omega))
    have b:=copied.2.2.2 (p.outVector.toNat+offset+i) (Or.inl (by omega))
    exact a.trans b
  have lo:readI32 (finalMemory p) p.outVector.toNat=readI32 (StateDecodeVector.finalMemory p.toVector) p.outVector.toNat:=by simpa only[Nat.add_zero] using word 0 (by omega)
  exact ⟨lo.trans (StateDecodeVector.finalMemory_pointer p.toVector hn.vector),
    (word 4 (by omega)).trans (StateDecodeVector.finalMemory_capacity p.toVector hn.vector),final.2.2.2.1⟩
end WNear.Proofs.StateDecodeVectorCopy

namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 allocatedMemory droppedMemory

theorem allocated_record (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    readI32 (allocatedMemory p q) ((scratch p).toNat+48)=payloadAddress p q ∧
    readI32 (allocatedMemory p q) ((scratch p).toNat+52)=count p ∧
    readI32 (allocatedMemory p q) ((scratch p).toNat+56)=count p := by
  have n:=allocation_copy_native p q hn hd
  have low:=StateDecodeRaw.result_head_bound (allocationInput p q).toRaw n.vector.raw
  rw[allocation_head_eq p q hn hd] at low
  have above:=hd.headAbove
  have endsp:=scratch_end p hn
  have out:(allocationInput p q).outVector.toNat=(scratch p).toNat+48:=by change q.outVector.toNat=_;rw[hd.out];exact scratch_add p hn 48 (by omega)
  have bound:(allocationInput p q).outVector.toNat+12≤(StateDecodeVectorCopy.pointer (allocationInput p q)).toNat:=by rw[out];exact Nat.le_trans (by omega) low
  have words:=StateDecodeVectorCopy.finalMemory_record_below_payload (allocationInput p q) n bound
  rw[out] at words
  unfold allocatedMemory
  change readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) ((scratch p).toNat+48)=_ ∧_ ∧_
  have size:(allocationInput p q).size=count p:=hd.size
  simpa only[size,Nat.add_assoc,Nat.reduceAdd,payloadAddress] using words

theorem dropped_record (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    readI32 (droppedMemory p q) ((scratch p).toNat+48)=payloadAddress p q ∧
    readI32 (droppedMemory p q) ((scratch p).toNat+52)=count p ∧
    readI32 (droppedMemory p q) ((scratch p).toNat+56)=count p ∧
    readI32 (droppedMemory p q) ((scratch p).toNat+8)=payloadPointer p+count p ∧
    readI32 (droppedMemory p q) ((scratch p).toNat+12)=remaining p-count p := by
  have a:=allocatedMemory_spec p q hn hd
  have add:(dropPayloadOut p).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have endsp:=scratch_end p hn
  have hb:(dropPayloadOut p).toNat+8≤(allocatedMemory p q).byteSize:=by rw[add,a.2.1];have h:=hn.spBound;omega
  have shape:=StateDecodeSlices.finalMemory_spec true (allocatedMemory p q) (dropPayloadOut p)
    (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p) a.1 hb
  have frame (offset : Nat) (ho : 16≤offset) :
      readI32 (droppedMemory p q) ((scratch p).toNat+offset)=readI32 (allocatedMemory p q) ((scratch p).toNat+offset):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    have no1:¬((dropPayloadOut p).toNat≤(scratch p).toNat+offset+i ∧(scratch p).toNat+offset+i<(dropPayloadOut p).toNat+4):=by rw[add];omega
    have no2:¬((dropPayloadOut p).toNat+4≤(scratch p).toNat+offset+i ∧(scratch p).toNat+offset+i<(dropPayloadOut p).toNat+8):=by rw[add];omega
    unfold droppedMemory
    rw[shape.2.2.2]
    simp only[ite_eq_right no1,ite_eq_right no2]
  have original:=allocated_record p q hn hd
  have descriptor : readI32 (allocatedMemory p q) p.slice.toNat=payloadPointer p ∧readI32 (allocatedMemory p q) (p.slice.toNat+4)=remaining p := by
    simpa only[allocatedMemory] using afterAllocation_descriptor p q hn hd
  have words:=StateDecodeSlices.finalMemory_words true (allocatedMemory p q) (dropPayloadOut p)
    (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p) a.1 hb
  refine ⟨(frame 48 (by omega)).trans original.1,(frame 52 (by omega)).trans original.2.1,(frame 56 (by omega)).trans original.2.2,?_,?_⟩
  · have low:readI32 (droppedMemory p q) ((scratch p).toNat+8)=StateDecodeSlices.lowWord true (readI32 (allocatedMemory p q) p.slice.toNat) (count p):=by
      simpa only[droppedMemory,add] using words.1
    simpa only[StateDecodeSlices.lowWord,ite_true,descriptor.1] using low
  · have high:readI32 (droppedMemory p q) ((scratch p).toNat+12)=StateDecodeSlices.highWord true (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p):=by
      simpa only[droppedMemory,add,Nat.add_assoc,Nat.reduceAdd] using words.2
    simpa only[StateDecodeSlices.highWord,ite_true,descriptor.2] using high

/-- The full canonical316 vector and advanced remainder descriptor, under
original caller-output/descriptor separation. -/
theorem finalMemory_record (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hsep : p.out.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat) :
    readI32 (finalMemory p q) p.out.toNat=0 ∧
    readI32 (finalMemory p q) (p.out.toNat+4)=payloadAddress p q ∧
    readI32 (finalMemory p q) (p.out.toNat+8)=count p ∧
    readI32 (finalMemory p q) (p.out.toNat+12)=count p ∧
    readI32 (finalMemory p q) p.slice.toNat=payloadPointer p+count p ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=remaining p-count p := by
  have e:=scratch_end p hn
  have h:=hn.outAbove
  have record:=Output.finalMemory_record (outputLayout p q) (output_native p q hn hd.toAllocationDomain) (by change (scratch p).toNat+64≤p.out.toNat;omega) hsep
  have words:=dropped_record p q hn hd.toAllocationDomain
  change readI32 (finalMemory p q) p.out.toNat=0 ∧
    readI32 (finalMemory p q) (p.out.toNat+4)=readI32 (droppedMemory p q) ((scratch p).toNat+48) ∧
    readI32 (finalMemory p q) (p.out.toNat+8)=readI32 (droppedMemory p q) ((scratch p).toNat+52) ∧
    readI32 (finalMemory p q) (p.out.toNat+12)=readI32 (droppedMemory p q) ((scratch p).toNat+56) ∧
    readI32 (finalMemory p q) p.slice.toNat=readI32 (droppedMemory p q) ((scratch p).toNat+8) ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=readI32 (droppedMemory p q) ((scratch p).toNat+12) at record
  rw[words.1,words.2.1,words.2.2.1,words.2.2.2.1,words.2.2.2.2] at record
  exact record
end WNear.Proofs.StateDecodePrefix
