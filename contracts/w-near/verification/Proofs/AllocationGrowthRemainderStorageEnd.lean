import Proofs.AllocationGrowthRemainderStorageExtent

/-! Complete final548 one-word split room and backlink bound, without any future
heap-native or word-lookup premise. -/
namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 AllocateRetry.finalMemory

 theorem retry_final_end(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    Allocate.endWord (AllocateRetry.finalMemory p) (readI32 (AllocateRetry.finalMemory p) p.allocator.toNat)=
      AllocateFlagged.header (AllocateRetry.secondLayout p):=by
  rw[retry_root p hn]
  unfold Allocate.endWord
  rw[retry_final_word p hn _ (by rw[(retry_interval p hn).1])]
  exact final_end (AllocateRetry.secondLayout p) (AllocateRetry.native_second p hn)

 theorem retry_final_end_bound(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    (Allocate.endWord (AllocateRetry.finalMemory p) (readI32 (AllocateRetry.finalMemory p) p.allocator.toNat)).toNat+8≤
      (AllocateRetry.finalMemory p).byteSize:=by
  rw[retry_final_end p hn]
  have interval:=AllocateFlagged.intervals (AllocateRetry.secondLayout p) (AllocateRetry.native_second p hn)
  have first:=AllocateRetry.secondMemory_spec p hn
  have last:=AllocateRetry.finalMemory_spec p hn
  rw[last.2.1,←first.2.1]
  omega

 theorem end_eq_of_words(a b:Memory)(headA headB:UInt32)(address:Nat)
    (ha:headA.toNat=address)(hb:headB.toNat=address)(word:readI32 a address=readI32 b address):
    Allocate.endWord a headA=Allocate.endWord b headB:=by
  unfold Allocate.endWord
  rw[ha,hb,word]
end WNear.Proofs.AllocationGrowthRemainder

namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocationGrowthRemainder
attribute [local irreducible] readI32 finalMemory remainderLayout AllocateRetry.finalMemory

 theorem remainder_size(p:Layout): (remainderLayout p).size=p.size:=by
  simp only[remainderLayout,AllocateVector.remainderLayout,AllocateVector.layout690,AllocateVector.actualRecord,
    StateReadRegisterOuter.actualVector,StateReadRegisterOuter.vectorMemoryTemplate,actualRegister,registerTemplate]

 theorem finalMemory_end_eq(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (output:p.out548.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out548.toNat):
    Allocate.endWord (finalMemory p) (readI32 (finalMemory p) p.allocator.toNat)=
      Allocate.endWord (AllocateRetry.finalMemory (remainderLayout p))
        (readI32 (AllocateRetry.finalMemory (remainderLayout p)) (remainderLayout p).allocator.toNat):=by
  have qn:=remainder_native p hn ha
  have first:=retry_interval (remainderLayout p) qn
  have actual:=remainder_interval p hn ha
  have root:=retry_root (remainderLayout p) qn
  have rootNat:(readI32 (AllocateRetry.finalMemory (remainderLayout p)) (remainderLayout p).allocator.toNat).toNat=p.memory.byteSize:=
    (congrArg UInt32.toNat root).trans actual.1
  have word:=finalMemory_remainder_word p hn ha p.memory.byteSize (by omega) (by have:=actual.2;omega)
  exact end_eq_of_words _ _ _ _ _ (finalMemory_root_nat p hn ha output) rootNat word

 theorem finalMemory_end_bound(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (output:p.out548.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out548.toNat):
    (Allocate.endWord (finalMemory p) (readI32 (finalMemory p) p.allocator.toNat)).toNat+8≤(finalMemory p).byteSize:=by
  rw[finalMemory_end_eq p hn ha output,finalMemory_remainder_size p hn ha]
  exact retry_final_end_bound (remainderLayout p) (remainder_native p hn ha)

 theorem finalMemory_one_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)(size:p.size=29)
    (output:p.out548.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out548.toNat):
    Allocate.SplitNative (finalMemory p) (readI32 (finalMemory p) p.allocator.toNat) 1:=by
  have qn:=remainder_native p hn ha
  have qs:(remainderLayout p).size=29:=(remainder_size p).trans size
  have split:=retry_final_split (remainderLayout p) qn qs
  have root:=finalMemory_root_nat p hn ha output
  have actual:=remainder_interval p hn ha
  have qroot:=retry_root (remainderLayout p) qn
  have rootNat:(readI32 (AllocateRetry.finalMemory (remainderLayout p)) (remainderLayout p).allocator.toNat).toNat=p.memory.byteSize:=
    (congrArg UInt32.toNat qroot).trans actual.1
  have room:=split.room
  rw[rootNat] at room
  refine ⟨split.wordsPositive,?_,?_⟩
  · rw[root,finalMemory_end_eq p hn ha output];exact room
  · rw[finalMemory_end_eq p hn ha output,finalMemory_remainder_size p hn ha];exact split.endBound
end WNear.Proofs.StateReadStorageOuter
