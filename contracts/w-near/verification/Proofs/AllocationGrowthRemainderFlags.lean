import Proofs.AllocationGrowthRemainderVector

/-! Actual free-head flags after687, derived through every wrapper write. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocationGrowthRemainder
attribute [local irreducible] readI32 writeI32 AllocateRetry.finalMemory finalMemory

 theorem remainder_head_interval(p:Layout)(hn:Native p):
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat=p.memory.byteSize ∧
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat+12≤
      (AllocateVector.result p.toVector).toNat:=by
  let q:=remainderLayout p
  have qn:=remainder_native p hn
  have interval:=retry_interval q qn
  have bounds:=AllocateFlagged.intervals (AllocateRetry.secondLayout q) (AllocateRetry.native_second q qn)
  have pointer:=Allocate.split_pointer_toNat (AllocateRetry.secondLayout q).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout q)) (AllocateRetry.secondLayout q).words
    (AllocateRetry.native_second q qn).split
  change (Allocate.splitPointer (AllocateRetry.secondLayout q).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout q)) (AllocateRetry.secondLayout q).words).toNat=
    (AllocateFlagged.finish (AllocateRetry.secondLayout q)).toNat-(AllocateRetry.secondLayout q).words.toNat*4 at pointer
  have header:=remainder_header_nat (AllocateRetry.secondLayout q) (AllocateRetry.native_second q qn)
  refine ⟨interval.1.trans (remainder_memory_size p hn),?_⟩
  change (AllocateFlagged.head (AllocateRetry.secondLayout q)).toNat+12≤
    (Allocate.splitPointer (AllocateRetry.secondLayout q).memory (AllocateFlagged.head (AllocateRetry.secondLayout q))
      (AllocateRetry.secondLayout q).words).toNat
  omega

 theorem finalMemory_remainder_flags(p:Layout)(hn:Native p):
    readI32 (finalMemory p) p.memory.byteSize &&&3=0 ∧
    readI32 (finalMemory p) (p.memory.byteSize+8) &&&1=0:=by
  let q:=remainderLayout p
  have qn:=remainder_native p hn
  have bounds:=remainder_head_interval p hn
  have first:=finalMemory_remainder_word p hn p.memory.byteSize (by omega) (by omega)
  have second:=finalMemory_remainder_word p hn (p.memory.byteSize+8) (by omega) (by omega)
  rw[first,second]
  have h:=retry_final_head q qn
  rw[bounds.1] at h
  have flags:=AllocateFlagged.header_aligned (AllocateRetry.secondLayout q) (AllocateRetry.native_second q qn)
  have candidate:=retry_final_candidate_flag q qn
  rw[bounds.1] at candidate
  exact ⟨(congrArg (fun x:UInt32=>x&&&3) h).trans flags,candidate⟩
end WNear.Proofs.AllocateVectorOuter
