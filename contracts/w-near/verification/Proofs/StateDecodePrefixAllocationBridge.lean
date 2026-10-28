import Proofs.StateDecodePrefixAllocationMemory
import Proofs.StateDecodeVectorCopyState

/-! Original direct-allocation geometry transfers through the actual316 prefix.
The descriptor/heap separations are original-memory conditions, not future
allocation-domain or execution assumptions. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

structure AllocationDomain (p : Layout) (q : StateDecodeVectorCopy.Layout) : Prop where
  original : StateDecodeVectorCopy.Native q
  memory : q.memory=p.memory
  size : q.size=count p
  sp : q.spVector=scratch p
  out : q.outVector=allocatedOut p
  source : q.source=payloadPointer p
  heapAbove : p.sp.toNat≤q.allocator.toNat
  headAbove : p.sp.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat
  descriptorBeforeHead : p.slice.toNat+8≤(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat
  descriptorRootSep : q.allocator.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤q.allocator.toNat

def allocationInput (p : Layout) (q : StateDecodeVectorCopy.Layout) : StateDecodeVectorCopy.Layout :=
  {q with toVector:={q.toVector with toRaw:={q.toRaw with toPositive:={q.toPositive with memory:=takenPayloadMemory p}}}}

private def nextPositive (p : Layout) (q : StateDecodeVectorCopy.Layout) := (allocationInput p q).toPositive
attribute [local irreducible] readI32 writeI32

private theorem saved_shapes (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    (AllocatePositive.savedMemory q.toPositive).wf ∧
    (AllocatePositive.savedMemory q.toPositive).byteSize=p.memory.byteSize ∧
    (AllocatePositive.savedMemory (nextPositive p q)).wf ∧
    (AllocatePositive.savedMemory (nextPositive p q)).byteSize=p.memory.byteSize := by
  have original:=hd.original.vector.raw.allocation
  have numbers:=AllocatePositive.scratch_numbers q.toPositive original
  have shape:=takenPayload_spec p hn
  have oldBound:(AllocatePositive.scratch q.toPositive).toNat+12+4≤q.memory.byteSize:=by omega
  have old:=writeI32_spec q.memory ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 q.memory q.allocator.toNat) original.wf oldBound
  have newBound:(AllocatePositive.scratch q.toPositive).toNat+12+4≤(takenPayloadMemory p).byteSize:=by rw[shape.2.1,←hd.memory];exact oldBound
  have new:=writeI32_spec (takenPayloadMemory p) ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 (takenPayloadMemory p) q.allocator.toNat) shape.1 newBound
  exact ⟨old.1,old.2.1.trans (hd.memory ▸ rfl),new.1,new.2.1.trans shape.2.1⟩

private theorem saved_root (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    AllocateSearch.head (AllocatePositive.searchLayout (nextPositive p q))=
      AllocateSearch.head (AllocatePositive.searchLayout q.toPositive) := by
  have original:=hd.original.vector.raw.allocation
  have numbers:=AllocatePositive.scratch_numbers q.toPositive original
  have shape:=takenPayload_spec p hn
  have ob:(AllocatePositive.scratch q.toPositive).toNat+12+4≤q.memory.byteSize:=by omega
  have nb:(AllocatePositive.scratch q.toPositive).toNat+12+4≤(takenPayloadMemory p).byteSize:=by rw[shape.2.1,←hd.memory];exact ob
  have old:=PanicAllocateReadback.read_write_self q.memory ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 q.memory q.allocator.toNat) original.wf ob
  have new:=PanicAllocateReadback.read_write_self (takenPayloadMemory p) ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 (takenPayloadMemory p) q.allocator.toNat) shape.1 nb
  have root:=takenPayload_word_frame p hn q.allocator.toNat hd.heapAbove hd.descriptorRootSep
  rw[←hd.memory] at root
  change readI32 (writeI32 _ _ _) (AllocatePositive.scratch q.toPositive+12).toNat=
    readI32 (writeI32 _ _ _) (AllocatePositive.scratch q.toPositive+12).toNat
  simp only[nextPositive,allocationInput,AllocatePositive.scratch] at *
  rw[numbers.2.1,new,old]
  exact root

private theorem saved_word (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (address : Nat) (ha : p.sp.toNat≤address) (hsep : address+4≤p.slice.toNat ∨p.slice.toNat+8≤address) :
    readI32 (AllocatePositive.savedMemory (nextPositive p q)) address=
      readI32 (AllocatePositive.savedMemory q.toPositive) address := by
  have original:=hd.original.vector.raw.allocation
  have numbers:=AllocatePositive.scratch_numbers q.toPositive original
  have shape:=takenPayload_spec p hn
  have parent:=scratch_end p hn
  have vector:=StateDecodeVector.stack_numbers q.toVector hd.original.vector
  have child:=hd.original.vector.raw.childSP
  have childLt:q.sp.toNat≤p.sp.toNat:=by
    have lower:=hd.original.vector.raw.spLower
    have rawLt:=q.spRaw.toNat_lt
    have rawEq:q.spRaw.toNat=q.spVector.toNat-16:=by rw[vector.2.1];exact vector.1
    have vectorEq:q.spVector.toNat=(scratch p).toNat:=congrArg UInt32.toNat hd.sp
    rw[child,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have away:(AllocatePositive.scratch q.toPositive).toNat+12+4≤address:=by
    have sl:=original.spLower
    have scratchEq:(AllocatePositive.scratch q.toPositive).toNat=q.sp.toNat-16:=numbers.1
    omega
  have ob:(AllocatePositive.scratch q.toPositive).toNat+12+4≤q.memory.byteSize:=by omega
  have nb:(AllocatePositive.scratch q.toPositive).toNat+12+4≤(takenPayloadMemory p).byteSize:=by rw[shape.2.1,←hd.memory];exact ob
  have old:=PanicAllocateReadback.read_write_frame q.memory address ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 q.memory q.allocator.toNat) original.wf ob (Or.inr away)
  have new:=PanicAllocateReadback.read_write_frame (takenPayloadMemory p) address ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 (takenPayloadMemory p) q.allocator.toNat) shape.1 nb (Or.inr away)
  have word:=takenPayload_word_frame p hn address ha hsep
  rw[←hd.memory] at word
  exact new.trans (word.trans old.symm)
/-- A reusable selector/heap-word bridge for code transport. -/
theorem allocation_saved_word (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AllocationDomain p q) (address : Nat)
    (ha : p.sp.toNat≤address) (hsep : address+4≤p.slice.toNat ∨p.slice.toNat+8≤address) :
    readI32 (AllocatePositive.savedMemory (allocationInput p q).toPositive) address=
      readI32 (AllocatePositive.savedMemory q.toPositive) address :=
  saved_word p q hn hd address ha hsep

theorem allocation_head_eq (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AllocationDomain p q) :
    AllocateSearch.head (AllocatePositive.searchLayout (allocationInput p q).toPositive)=
      AllocateSearch.head (AllocatePositive.searchLayout q.toPositive) := saved_root p q hn hd

theorem allocation_search_native (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    AllocateSearch.Native (AllocatePositive.searchLayout (nextPositive p q)) := by
  let old:=AllocatePositive.searchLayout q.toPositive
  let next:=AllocatePositive.searchLayout (nextPositive p q)
  have original:AllocateSearch.Native old:=hd.original.vector.raw.allocation.search
  have shape:=saved_shapes p q hn hd
  have headEq:AllocateSearch.head next=AllocateSearch.head old:=saved_root p q hn hd
  have habove:p.sp.toNat≤(AllocateSearch.head old).toNat:=hd.headAbove
  have hbefore:p.slice.toNat+8≤(AllocateSearch.head old).toNat:=hd.descriptorBeforeHead
  have headerRead:=saved_word p q hn hd (AllocateSearch.head old).toNat habove (Or.inr hbefore)
  have flagRead:=saved_word p q hn hd ((AllocateSearch.head old).toNat+8) (by omega)
    (Or.inr (by omega))
  change readI32 next.memory (AllocateSearch.head old).toNat=readI32 old.memory (AllocateSearch.head old).toNat at headerRead
  change readI32 next.memory ((AllocateSearch.head old).toNat+8)=readI32 old.memory ((AllocateSearch.head old).toNat+8) at flagRead
  have finishEq:Allocate.endWord next.memory (AllocateSearch.head old)=Allocate.endWord old.memory (AllocateSearch.head old):=by
    unfold Allocate.endWord
    exact congrArg (fun x:UInt32=>x &&& 4294967292) headerRead
  have rootBound:next.root.toNat+4≤next.memory.byteSize:=by
    change old.root.toNat+4≤(AllocatePositive.savedMemory (nextPositive p q)).byteSize
    rw[shape.2.2.2,←shape.2.1]
    exact original.rootBound
  have split:Allocate.SplitNative next.memory (AllocateSearch.head next) next.words:=by
    rw[headEq]
    refine ⟨original.split.wordsPositive,?_,?_⟩
    · rw[finishEq];exact original.split.room
    · rw[finishEq]
      change _≤(AllocatePositive.savedMemory (nextPositive p q)).byteSize
      rw[shape.2.2.2,←shape.2.1];exact original.split.endBound
  refine ⟨shape.2.2.1,rootBound,?_,split,?_,?_,?_,?_⟩
  · rw[headEq];exact original.headNonzero
  · change (Allocate.endWord next.memory (AllocateSearch.head next)).toNat+8≤next.memory.byteSize
    rw[headEq,finishEq]
    change _≤(AllocatePositive.savedMemory (nextPositive p q)).byteSize
    rw[shape.2.2.2,←shape.2.1];exact original.endBound
  · change readI32 next.memory (AllocateSearch.head next).toNat &&& 3=0
    rw[headEq,headerRead];exact original.headFlags
  · change readI32 next.memory ((AllocateSearch.head next).toNat+8) &&& 1=0
    rw[headEq,flagRead];exact original.candidateFlag
  · change old.vtable.toNat+20≤(AllocatePositive.savedMemory (nextPositive p q)).byteSize
    rw[shape.2.2.2,←shape.2.1];exact original.vtableBound

theorem allocation_positive_native (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    AllocatePositive.Native (nextPositive p q) := by
  have shape:=takenPayload_spec p hn
  have original:=hd.original.vector.raw.allocation
  refine ⟨original.positive,original.rounding,shape.1,?_,original.spLower,?_,?_,allocation_search_native p q hn hd⟩
  · change (takenPayloadMemory p).byteSize≤2^32
    rw[shape.2.1,←hd.memory];exact original.width
  · change q.sp.toNat≤(takenPayloadMemory p).byteSize
    rw[shape.2.1,←hd.memory];exact original.spBound
  · change q.allocator.toNat+4≤(takenPayloadMemory p).byteSize
    rw[shape.2.1,←hd.memory];exact original.allocatorBound

/-- Full actual374 original-domain transfer after the actual183-step prefix. -/
theorem allocation_copy_native (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    StateDecodeVectorCopy.Native (allocationInput p q) := by
  have original:=hd.original
  have shape:=takenPayload_spec p hn
  have raw:StateDecodeRaw.Native (allocationInput p q).toRaw:=by
    refine {original.vector.raw with allocation:=allocation_positive_native p q hn hd,spBound:=?_,outBound:=?_,headAbove:=?_}
    · change q.spRaw.toNat≤(takenPayloadMemory p).byteSize
      rw[shape.2.1,←hd.memory];exact original.vector.raw.spBound
    · change q.outRaw.toNat+8≤(takenPayloadMemory p).byteSize
      rw[shape.2.1,←hd.memory];exact original.vector.raw.outBound
    · change q.spRaw.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout (nextPositive p q))).toNat
      rw[saved_root p q hn hd];exact original.vector.raw.headAbove
  have vector:StateDecodeVector.Native (allocationInput p q).toVector:=by
    refine {original.vector with raw:=raw,spBound:=?_,outBound:=?_}
    · change q.spVector.toNat≤(takenPayloadMemory p).byteSize
      rw[shape.2.1,←hd.memory];exact original.vector.spBound
    · change q.outVector.toNat+12≤(takenPayloadMemory p).byteSize
      rw[shape.2.1,←hd.memory];exact original.vector.outBound
  refine ⟨vector,?_⟩
  change q.source.toNat+q.size.toNat≤(takenPayloadMemory p).byteSize
  rw[shape.2.1,←hd.memory];exact original.sourceBound
end WNear.Proofs.StateDecodePrefix
