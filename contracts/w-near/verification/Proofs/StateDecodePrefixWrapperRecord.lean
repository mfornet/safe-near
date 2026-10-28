import Proofs.StateDecodePrefixRecord
import Proofs.StateDecodePrefixWrapperBody

/-! Accepted315 snapshots all child vector fields before writing its output.
The final slice is retained only when the caller output is disjoint from it. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_record (p : Layout) (hn : Native p) :
    readI32 (finalMemory p) p.out.toNat=0 ∧
    readI32 (finalMemory p) (p.out.toNat+4)=readI32 p.memory (p.pointer.toNat+4) ∧
    readI32 (finalMemory p) (p.out.toNat+8)=readI32 p.memory (p.pointer.toNat+8) ∧
    readI32 (finalMemory p) (p.out.toNat+12)=readI32 p.memory (p.pointer.toNat+12) := by
  have specs:=memory_specs p hn
  have lb:p.out.toNat+4+8≤p.memory.byteSize:=by have h:=hn.outputBound;omega
  have low0:=AllocateLayoutWrapperReadback.packedCopy_word p.memory (p.out.toNat+4) (p.pointer.toNat+4) 0 hn.wf lb (by omega)
  have low4:=AllocateLayoutWrapperReadback.packedCopy_word p.memory (p.out.toNat+4) (p.pointer.toNat+4) 4 hn.wf lb (by omega)
  have hb:(p.out+12).toNat+4≤(lowMemory p).byteSize:=by rw[add_output p hn,specs.2.1];exact hn.outputBound
  have high:=writeI32_spec (lowMemory p) (p.out+12).toNat (highValue p) specs.1 hb
  have tb:p.out.toNat+4≤(highMemory p).byteSize:=by rw[specs.2.2.2];have h:=hn.outputBound;omega
  have tag:=writeI32_spec (highMemory p) p.out.toNat 0 specs.2.2.1 tb
  have tf (address : Nat) (ha : p.out.toNat+4≤address) :
      readI32 (finalMemory p) address=readI32 (highMemory p) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold finalMemory
    rw[tag.2.2.2]
    have no:¬(p.out.toNat≤address+i ∧address+i<p.out.toNat+4):=by omega
    exact ite_eq_right no
  have hf (offset : Nat) (ho : offset+4≤8) :
      readI32 (highMemory p) (p.out.toNat+4+offset)=readI32 (lowMemory p) (p.out.toNat+4+offset):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold highMemory
    rw[high.2.2.2]
    have no:¬((p.out+12).toNat≤p.out.toNat+4+offset+i ∧p.out.toNat+4+offset+i<(p.out+12).toNat+4):=by rw[add_output p hn];omega
    exact ite_eq_right no
  have l0:readI32 (lowMemory p) (p.out.toNat+4)=readI32 p.memory (p.pointer.toNat+4):=by
    simpa only[lowMemory,lowValue,writeI64,AllocateLayoutWrapperReadback.packedCopy,Nat.add_zero] using low0
  have l4:readI32 (lowMemory p) (p.out.toNat+8)=readI32 p.memory (p.pointer.toNat+8):=by
    simpa only[lowMemory,lowValue,writeI64,AllocateLayoutWrapperReadback.packedCopy,Nat.add_assoc,Nat.reduceAdd] using low4
  have highword:readI32 (highMemory p) (p.out.toNat+12)=readI32 p.memory (p.pointer.toNat+12):=by
    have self:=PanicAllocateReadback.read_write_self (lowMemory p) (p.out+12).toNat (highValue p) specs.1 hb
    simpa only[highMemory,highValue,add_output p hn,add_pointer p hn] using self
  have tagword:=PanicAllocateReadback.read_write_self (highMemory p) p.out.toNat 0 specs.2.2.1 tb
  refine ⟨tagword,?_,?_,(tf _ (by omega)).trans highword⟩
  · have f:readI32 (highMemory p) (p.out.toNat+4)=readI32 (lowMemory p) (p.out.toNat+4):=by simpa only[Nat.add_zero] using hf 0 (by omega)
    exact (tf _ (by omega)).trans (f.trans l0)
  · have f:readI32 (highMemory p) (p.out.toNat+8)=readI32 (lowMemory p) (p.out.toNat+8):=by simpa only[Nat.add_assoc,Nat.reduceAdd] using hf 4 (by omega)
    exact (tf _ (by omega)).trans (f.trans l4)

theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hout : j<p.out.toNat ∨p.out.toNat+16≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have specs:=memory_specs p hn
  have lb:p.out.toNat+4+8≤p.memory.byteSize:=by have h:=hn.outputBound;omega
  have low:=writeI64_spec p.memory (p.out.toNat+4) (lowValue p) hn.wf lb
  have hb:(p.out+12).toNat+4≤(lowMemory p).byteSize:=by rw[add_output p hn,specs.2.1];exact hn.outputBound
  have high:=writeI32_spec (lowMemory p) (p.out+12).toNat (highValue p) specs.1 hb
  have tb:p.out.toNat+4≤(highMemory p).byteSize:=by rw[specs.2.2.2];have h:=hn.outputBound;omega
  have tag:=writeI32_spec (highMemory p) p.out.toNat 0 specs.2.2.1 tb
  have nl:¬(p.out.toNat+4≤j ∧j<p.out.toNat+4+8):=by omega
  have nh:¬((p.out+12).toNat≤j ∧j<(p.out+12).toNat+4):=by rw[add_output p hn];omega
  have nt:¬(p.out.toNat≤j ∧j<p.out.toNat+4):=by omega
  calc
    _=(highMemory p).read8 j:=by unfold finalMemory;rw[tag.2.2.2];exact ite_eq_right nt
    _=(lowMemory p).read8 j:=by unfold highMemory;rw[high.2.2.2];exact ite_eq_right nh
    _=p.memory.read8 j:=by unfold lowMemory;rw[low.2.2.2];exact ite_eq_right nl
end WNear.Proofs.StateDecodePrefixWrapper.Tail

namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic

theorem finalMemory_record (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p)
    (hd : StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hchild : p.out.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat)
    (hout : p.wrapperOut.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.wrapperOut.toNat) :
    readI32 (finalMemory p q) p.wrapperOut.toNat=0 ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+4)=StateDecodePrefix.payloadAddress p.toPrefix q ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+8)=StateDecodePrefix.count p.toPrefix ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+12)=StateDecodePrefix.count p.toPrefix ∧
    readI32 (finalMemory p q) p.slice.toNat=StateDecodePrefix.payloadPointer p.toPrefix+StateDecodePrefix.count p.toPrefix ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=StateDecodePrefix.remaining p.toPrefix-StateDecodePrefix.count p.toPrefix := by
  have child:=StateDecodePrefix.finalMemory_record p.toPrefix q hn.child hd hchild
  have native:=tail_native p q hn hd
  have copied:=Tail.finalMemory_record (tailLayout p q) native
  change readI32 (finalMemory p q) p.wrapperOut.toNat=0 ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+4)=readI32 (StateDecodePrefix.finalMemory p.toPrefix q) ((scratch p).toNat+4) ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+8)=readI32 (StateDecodePrefix.finalMemory p.toPrefix q) ((scratch p).toNat+8) ∧
    readI32 (finalMemory p q) (p.wrapperOut.toNat+12)=readI32 (StateDecodePrefix.finalMemory p.toPrefix q) ((scratch p).toNat+12) at copied
  rw[←hn.childOut] at copied
  have words:=child.2.1
  rw[child.2.1,child.2.2.1,child.2.2.2.1] at copied
  have sf (address : Nat) (ha : p.slice.toNat≤address) (hb : address+4≤p.slice.toNat+8) :
      readI32 (finalMemory p q) address=readI32 (StateDecodePrefix.finalMemory p.toPrefix q) address := by
    apply Allocate.readI32_congr_bytes
    intro i hi
    apply Tail.finalMemory_byte_frame (tailLayout p q) native
    change _<p.wrapperOut.toNat ∨p.wrapperOut.toNat+16≤_
    rcases hout with h|h <;> omega
  exact ⟨copied.1,copied.2.1,copied.2.2.1,copied.2.2.2,
    (sf _ (by omega) (by omega)).trans child.2.2.2.2.1,
    (sf _ (by omega) (by omega)).trans child.2.2.2.2.2⟩
end WNear.Proofs.StateDecodePrefixWrapper
