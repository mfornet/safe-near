import Proofs.AllocationGrowthRemainderRoot

/-! The actual687 growing vector path exposes a regular free remainder for the
next one-word search. Only original native data and output/root separation enter. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocationGrowthRemainder
attribute [local irreducible] readI32 writeI32 AllocateRetry.finalMemory finalMemory

def remainderLayout(p:Layout):AllocateRetry.Layout:=AllocateVector.remainderLayout p.toVector

theorem remainder_native(p:Layout)(hn:Native p):AllocateRetry.Native (remainderLayout p):=
  (AllocateVector.copy_native p.toVector (hn.vector p)).inner.allocation

theorem remainder_memory_size(p:Layout)(hn:Native p):
    (remainderLayout p).memory.byteSize=p.memory.byteSize:=
  (AllocateVector.setup_spec p.toVector (hn.vector p)).2.1

theorem finalMemory_remainder_size(p:Layout)(hn:Native p):
    (finalMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=by
  have cv:=hn.vector p
  have cn:=AllocateVector.copy_native p.toVector cv
  have zero:=AllocateZeroedRetry.finalMemory_spec (AllocateVector.layout690 p.toVector).inner.toZeroed cn.inner.allocation
  have retry:=AllocateRetry.finalMemory_spec (remainderLayout p) (remainder_native p hn)
  have record:=AllocateRecord.finalMemory_spec (AllocateVector.layout690 p.toVector).inner cn.inner
  have copy:=AllocateRecordCopy.resultMemory_spec (AllocateVector.layout690 p.toVector) cn
  have vector:=AllocateVector.finalMemory_spec p.toVector cv
  have shape:=allocated_spec p hn
  have output:=outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1
    (hn.outputBound.trans shape.2.1)
  have z:(AllocateRecord.allocatedMemory (AllocateVector.layout690 p.toVector).inner).byteSize=
      (AllocateRetry.finalMemory (remainderLayout p)).byteSize:=zero.2.1.trans retry.2.1.symm
  have c:(AllocateRecordCopy.resultMemory (AllocateVector.layout690 p.toVector)).byteSize=
      (AllocateRetry.finalMemory (remainderLayout p)).byteSize:=copy.2.1.trans (record.2.1.trans z)
  have v:(allocatedMemory p).byteSize=(AllocateRetry.finalMemory (remainderLayout p)).byteSize:=
    vector.2.1.trans c
  unfold finalMemory
  exact output.2.1.trans v

theorem finalMemory_remainder_word(p:Layout)(hn:Native p)(address:Nat)
    (above:p.memory.byteSize≤address)(before:address+4≤(AllocateVector.result p.toVector).toNat):
    readI32 (finalMemory p) address=readI32 (AllocateRetry.finalMemory (remainderLayout p)) address:=by
  apply readI32_congr_bytes
  intro i hi
  exact finalMemory_new_remainder p hn (address+i) (by omega) (by omega)

/-- The next allocation's actual split interval, derived after all687 writes. -/
theorem finalMemory_one_word(p:Layout)(hn:Native p)(size:p.size=29)
    (innerOutput:p.out686.toNat+8≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out686.toNat)
    (output:p.out687.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out687.toNat):
    Allocate.SplitNative (finalMemory p) (readI32 (finalMemory p) p.allocator.toNat) 1:=by
  let q:=remainderLayout p
  have qn:AllocateRetry.Native q:=remainder_native p hn
  have root:=finalMemory_root p hn innerOutput output
  change readI32 (finalMemory p) p.allocator.toNat=readI32 (AllocateRetry.finalMemory q) p.allocator.toNat at root
  have qr:=retry_root q qn
  have qa:q.allocator=p.allocator:=by
    simp only[q,remainderLayout,AllocateVector.remainderLayout,AllocateVector.layout690,AllocateVector.actualRecord]
  rw[qa] at qr
  have interval:=retry_interval q qn
  have bound:=AllocateFlagged.intervals (AllocateRetry.secondLayout q) (AllocateRetry.native_second q qn)
  have pointer:=Allocate.split_pointer_toNat (AllocateRetry.secondLayout q).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout q)) (AllocateRetry.secondLayout q).words
    (AllocateRetry.native_second q qn).split
  change (Allocate.splitPointer (AllocateRetry.secondLayout q).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout q)) (AllocateRetry.secondLayout q).words).toNat=
    (AllocateFlagged.finish (AllocateRetry.secondLayout q)).toNat-(AllocateRetry.secondLayout q).words.toNat*4 at pointer
  have header:=remainder_header_nat (AllocateRetry.secondLayout q) (AllocateRetry.native_second q qn)
  have he:readI32 (finalMemory p) p.allocator.toNat=AllocateFlagged.head (AllocateRetry.secondLayout q):=
    root.trans qr
  have qs:q.size=29:=by
    simp only[q,remainderLayout,AllocateVector.remainderLayout,AllocateVector.layout690,AllocateVector.actualRecord]
    exact size
  have split:=retry_final_split q qn qs
  have word:=finalMemory_remainder_word p hn (AllocateFlagged.head (AllocateRetry.secondLayout q)).toNat
    (by rw[interval.1,remainder_memory_size p hn]) (by
      change (AllocateFlagged.head (AllocateRetry.secondLayout q)).toNat+4≤
        (Allocate.splitPointer (AllocateRetry.secondLayout q).memory (AllocateFlagged.head (AllocateRetry.secondLayout q))
          (AllocateRetry.secondLayout q).words).toNat
      omega)
  have endEq:Allocate.endWord (finalMemory p) (AllocateFlagged.head (AllocateRetry.secondLayout q))=
      Allocate.endWord (AllocateRetry.finalMemory q) (AllocateFlagged.head (AllocateRetry.secondLayout q)):=by
    unfold Allocate.endWord
    rw[word]
  rw[he]
  rw[qa,qr] at split
  refine ⟨split.wordsPositive,?_,?_⟩
  · rw[endEq];exact split.room
  · rw[endEq,finalMemory_remainder_size p hn];exact split.endBound
end WNear.Proofs.AllocateVectorOuter
