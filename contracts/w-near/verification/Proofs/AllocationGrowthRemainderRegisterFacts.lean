import Proofs.AllocationGrowthRemainderReadAddress

/-! Cached original523-to-retry native and interval bridges. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] actualVector AllocateVectorOuter.remainderLayout AllocateVector.remainderLayout

def remainderLayout(p:Layout):AllocateRetry.Layout:=AllocateVector.remainderLayout (actualVector p).toVector

 theorem remainder_native(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    AllocateRetry.Native (remainderLayout p):=by
  have vn:=vector_native p hn ha
  have h:=AllocateVectorOuter.remainder_native (actualVector p) vn
  unfold AllocateVectorOuter.remainderLayout at h
  unfold remainderLayout
  exact h

 theorem remainder_interval(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat=p.memory.byteSize ∧
    p.memory.byteSize+12≤(AllocateVector.result (actualVector p).toVector).toNat:=by
  have vn:=vector_native p hn ha
  have interval:=AllocateVectorOuter.remainder_head_interval (actualVector p) vn
  unfold AllocateVectorOuter.remainderLayout at interval
  have old:(actualVector p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualVector,vectorMemoryTemplate];exact (lengthMemory_footprint p hn).2.1
  have head:(AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat=p.memory.byteSize:=by
    unfold remainderLayout
    exact interval.1.trans old
  have before:p.memory.byteSize+12≤(AllocateVector.result (actualVector p).toVector).toNat:=
    (congrArg (fun n:Nat=>n+12) head.symm).trans_le interval.2
  exact ⟨head,before⟩
end WNear.Proofs.StateReadRegisterOuter
