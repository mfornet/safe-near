import Proofs.StateDecodeBorshReadNative
import Proofs.StateDecodePrefixAllocationBridge

/-! The original allocator template remains valid after161's two descriptor
stores. Only original native data and original heap-above-SP bounds are used. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 setupMemory

private theorem sub_nat(x:UInt32)(n:Nat)(h:n≤x.toNat)(hn:n<2^32):
    (x-UInt32.ofNat n).toNat=x.toNat-n:=by
  rw[UInt32.toNat_sub,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]
  have lt:=x.toNat_lt
  omega

theorem allocation_stack_below(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    q.sp.toNat≤p.sp.toNat ∧(AllocatePositive.scratch q.toPositive).toNat+16=q.sp.toNat ∧
    (AllocatePositive.scratch q.toPositive).toNat+16≤(scratch p).toNat:=by
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have lo:=hn.spLower
  have pos:=hd.original.vector.raw.allocation
  have ps:=AllocatePositive.scratch_numbers q.toPositive pos
  have vn:=hd.original.vector.spLower
  have rn:=hd.original.vector.raw.spLower
  have raw:q.spRaw.toNat=q.spVector.toNat-16:=by
    rw[hd.original.vector.childSP]
    exact sub_nat q.spVector 16 (by omega) (by omega)
  have positive:q.sp.toNat=q.spRaw.toNat-48:=by
    rw[hd.original.vector.raw.childSP]
    exact sub_nat q.spRaw 48 (by omega) (by omega)
  have vector:q.spVector.toNat=p.sp.toNat-64:=by
    rw[hd.sp,StateDecodePrefix.scratch]
    exact sub_nat p.sp 64 (by omega) (by omega)
  have endstack:(AllocatePositive.scratch q.toPositive).toNat+16=q.sp.toNat:=by
    rw[ps.1]
    have lower:=pos.spLower
    omega
  exact ⟨by omega,endstack,by omega⟩

private theorem saved_shapes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    (AllocatePositive.savedMemory q.toPositive).wf ∧
    (AllocatePositive.savedMemory q.toPositive).byteSize=p.memory.byteSize ∧
    (AllocatePositive.savedMemory (actualAllocation p q).toPositive).wf ∧
    (AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize=p.memory.byteSize:=by
  have old:=hd.original.vector.raw.allocation
  have stack:=AllocatePositive.scratch_numbers q.toPositive old
  have shape:=setupMemory_spec p hn
  have original:=writeI32_spec q.memory ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 q.memory q.allocator.toNat) old.wf (by have h:=stack.2.2.1;omega)
  have next:=writeI32_spec (setupMemory p) ((AllocatePositive.scratch q.toPositive).toNat+12)
    (readI32 (setupMemory p) q.allocator.toNat) shape.1 (by rw[shape.2.1,←hd.memory];have h:=stack.2.2.1;omega)
  have wf:(AllocatePositive.savedMemory (actualAllocation p q).toPositive).wf:=by
    simpa only[actualAllocation,AllocatePositive.savedMemory,AllocatePositive.scratch] using next.1
  have bytes:(AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize=p.memory.byteSize:=by
    have e:=next.2.1.trans shape.2.1
    simpa only[actualAllocation,AllocatePositive.savedMemory,AllocatePositive.scratch] using e
  exact ⟨original.1,original.2.1.trans (congrArg Memory.byteSize hd.memory),wf,bytes⟩

theorem head_eq(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p q).toPositive)=
      AllocateSearch.head (AllocatePositive.searchLayout q.toPositive):=by
  have old:=hd.original.vector.raw.allocation
  have stack:=AllocatePositive.scratch_numbers q.toPositive old
  have shape:=setupMemory_spec p hn
  have ob:(AllocatePositive.scratch q.toPositive).toNat+12+4≤q.memory.byteSize:=by have h:=stack.2.2.1;omega
  have nb:(AllocatePositive.scratch q.toPositive).toNat+12+4≤(setupMemory p).byteSize:=by rw[shape.2.1,←hd.memory];exact ob
  have first:=PanicAllocateReadback.read_write_self q.memory ((AllocatePositive.scratch q.toPositive).toNat+12) (readI32 q.memory q.allocator.toNat) old.wf ob
  have second:=PanicAllocateReadback.read_write_self (setupMemory p) ((AllocatePositive.scratch q.toPositive).toNat+12) (readI32 (setupMemory p) q.allocator.toNat) shape.1 nb
  have alloc:=setupMemory_word_above p hn q.allocator.toNat hd.allocatorAbove
  rw[←hd.memory] at alloc
  have a:readI32 (AllocatePositive.savedMemory (actualAllocation p q).toPositive) (AllocatePositive.scratch q.toPositive+12).toNat=readI32 (setupMemory p) q.allocator.toNat:=by
    rw[stack.2.1]
    simpa only[actualAllocation,AllocatePositive.savedMemory,AllocatePositive.scratch] using second
  have b:readI32 (AllocatePositive.savedMemory q.toPositive) (AllocatePositive.scratch q.toPositive+12).toNat=readI32 q.memory q.allocator.toNat:=by
    simpa only[AllocatePositive.savedMemory,stack.2.1] using first
  have same:AllocatePositive.scratch (actualAllocation p q).toPositive=AllocatePositive.scratch q.toPositive:=by simp only[actualAllocation,AllocatePositive.scratch]
  simp only[AllocateSearch.head,AllocatePositive.searchLayout,same]
  exact a.trans (alloc.trans b.symm)

theorem saved_word(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q)
    (address:Nat)(ha:p.sp161.toNat≤address):
    readI32 (AllocatePositive.savedMemory (actualAllocation p q).toPositive) address=
      readI32 (AllocatePositive.savedMemory q.toPositive) address:=by
  have old:=hd.original.vector.raw.allocation
  have stack:=AllocatePositive.scratch_numbers q.toPositive old
  have below:=allocation_stack_below p q hn hd
  have n:=scratch_numbers p hn
  have shape:=setupMemory_spec p hn
  have ob:(AllocatePositive.scratch q.toPositive).toNat+12+4≤q.memory.byteSize:=by have h:=stack.2.2.1;omega
  have nb:(AllocatePositive.scratch q.toPositive).toNat+12+4≤(setupMemory p).byteSize:=by rw[shape.2.1,←hd.memory];exact ob
  have first:=PanicAllocateReadback.read_write_frame q.memory address ((AllocatePositive.scratch q.toPositive).toNat+12) (readI32 q.memory q.allocator.toNat) old.wf ob (Or.inr (by omega))
  have second:=PanicAllocateReadback.read_write_frame (setupMemory p) address ((AllocatePositive.scratch q.toPositive).toNat+12) (readI32 (setupMemory p) q.allocator.toNat) shape.1 nb (Or.inr (by omega))
  have base:=setupMemory_word_above p hn address ha
  rw[←hd.memory] at base
  have next:readI32 (AllocatePositive.savedMemory (actualAllocation p q).toPositive) address=readI32 (setupMemory p) address:=by
    simpa only[actualAllocation,AllocatePositive.savedMemory,AllocatePositive.scratch] using second
  exact next.trans (base.trans first.symm)

theorem allocation_search_native(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    AllocateSearch.Native (AllocatePositive.searchLayout (actualAllocation p q).toPositive):=by
  let old:=AllocatePositive.searchLayout q.toPositive
  let next:=AllocatePositive.searchLayout (actualAllocation p q).toPositive
  have original:AllocateSearch.Native old:=hd.original.vector.raw.allocation.search
  have shape:=saved_shapes p q hn hd
  have he:AllocateSearch.head next=AllocateSearch.head old:=head_eq p q hn hd
  have ha:p.sp161.toNat≤(AllocateSearch.head old).toNat:=hd.headAbove
  have hr:=saved_word p q hn hd (AllocateSearch.head old).toNat ha
  have fr:=saved_word p q hn hd ((AllocateSearch.head old).toNat+8) (by omega)
  change readI32 next.memory (AllocateSearch.head old).toNat=readI32 old.memory (AllocateSearch.head old).toNat at hr
  change readI32 next.memory ((AllocateSearch.head old).toNat+8)=readI32 old.memory ((AllocateSearch.head old).toNat+8) at fr
  have fe:Allocate.endWord next.memory (AllocateSearch.head old)=Allocate.endWord old.memory (AllocateSearch.head old):=by
    unfold Allocate.endWord
    exact congrArg (fun x:UInt32=>x &&& 4294967292) hr
  have re:next.root=old.root:=by simp only[next,old,AllocatePositive.searchLayout,actualAllocation,AllocatePositive.scratch]
  have we:next.words=old.words:=by simp only[next,old,AllocatePositive.searchLayout,actualAllocation,AllocatePositive.words]
  have root:next.root.toNat+4≤next.memory.byteSize:=by
    rw[re]
    change old.root.toNat+4≤(AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize
    rw[shape.2.2.2,←shape.2.1]
    exact original.rootBound
  have split:Allocate.SplitNative next.memory (AllocateSearch.head next) next.words:=by
    rw[he,we]
    refine ⟨original.split.wordsPositive,?_,?_⟩
    · rw[fe];exact original.split.room
    · rw[fe]
      change _≤(AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize
      rw[shape.2.2.2,←shape.2.1];exact original.split.endBound
  refine ⟨shape.2.2.1,root,?_,split,?_,?_,?_,?_⟩
  · rw[he];exact original.headNonzero
  · change (Allocate.endWord next.memory (AllocateSearch.head next)).toNat+8≤next.memory.byteSize
    rw[he,fe]
    change _≤(AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize
    rw[shape.2.2.2,←shape.2.1];exact original.endBound
  · change readI32 next.memory (AllocateSearch.head next).toNat &&&3=0
    rw[he,hr];exact original.headFlags
  · change readI32 next.memory ((AllocateSearch.head next).toNat+8) &&&1=0
    rw[he,fr];exact original.candidateFlag
  · change next.vtable.toNat+20≤(AllocatePositive.savedMemory (actualAllocation p q).toPositive).byteSize
    have ve:next.vtable=old.vtable:=by simp only[next,old,AllocatePositive.searchLayout]
    rw[ve,shape.2.2.2,←shape.2.1];exact original.vtableBound

theorem allocation_positive_native(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    AllocatePositive.Native (actualAllocation p q).toPositive:=by
  have shape:=setupMemory_spec p hn
  have old:=hd.original.vector.raw.allocation
  refine ⟨?_,?_,?_,?_,?_,?_,?_,allocation_search_native p q hn hd⟩
  · exact old.positive
  · exact old.rounding
  · exact shape.1
  · change (setupMemory p).byteSize≤2^32;rw[shape.2.1,←hd.memory];exact old.width
  · exact old.spLower
  · change q.sp.toNat≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact old.spBound
  · change q.allocator.toNat+4≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact old.allocatorBound

theorem allocation_native(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    StateDecodeVectorCopy.Native (actualAllocation p q):=by
  have original:=hd.original
  have shape:=setupMemory_spec p hn
  have raw:StateDecodeRaw.Native (actualAllocation p q).toRaw:=by
    refine {original.vector.raw with allocation:=allocation_positive_native p q hn hd,spBound:=?_,outBound:=?_,headAbove:=?_}
    · change q.spRaw.toNat≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact original.vector.raw.spBound
    · change q.outRaw.toNat+8≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact original.vector.raw.outBound
    · change q.spRaw.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p q).toPositive)).toNat
      rw[head_eq p q hn hd];exact original.vector.raw.headAbove
  have vector:StateDecodeVector.Native (actualAllocation p q).toVector:=by
    refine {original.vector with raw:=raw,spBound:=?_,outBound:=?_}
    · change q.spVector.toNat≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact original.vector.spBound
    · change q.outVector.toNat+12≤(setupMemory p).byteSize;rw[shape.2.1,←hd.memory];exact original.vector.outBound
  refine ⟨vector,?_⟩
  change q.source.toNat+q.size.toNat≤(setupMemory p).byteSize
  rw[shape.2.1,←hd.memory];exact original.sourceBound

theorem saved_callback_word(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    readI32 (AllocatePositive.savedMemory (actualAllocation p q).toPositive) 1057480=
      readI32 (AllocatePositive.savedMemory q.toPositive) 1057480:=
  saved_word p q hn hd 1057480 (by have h:=hd.callbackAbove;omega)
end WNear.Proofs.StateDecodeBorshRead
