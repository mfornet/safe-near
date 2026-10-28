import Proofs.AllocationGrowthRemainderStorageAddress
import Proofs.AllocationGrowthRemainderRegisterFacts
import Proofs.AllocationGrowthRemainderStorage

/-! Concrete free-head words in the final548 heap, derived from its original
native growth conditions and the exact subsequent wrapper memories. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocationGrowthRemainder
attribute [local irreducible] readI32 finalMemory actualRegister StateReadRegisterOuter.actualVector AllocateRetry.finalMemory AllocateVectorOuter.remainderLayout AllocateVector.remainderLayout

 theorem remainder_native(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    AllocateRetry.Native (remainderLayout p):=by
  have rn:=register_native p hn ha
  have ca:(actualRegister p).allocator=1074896:=by simp only[actualRegister,registerTemplate];exact ha
  have h:=StateReadRegisterOuter.remainder_native (actualRegister p) rn ca
  unfold StateReadRegisterOuter.remainderLayout at h
  unfold remainderLayout
  exact h

 theorem remainder_interval(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat=p.memory.byteSize ∧
    p.memory.byteSize+12≤(AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat:=by
  have rn:=register_native p hn ha
  have ca:(actualRegister p).allocator=1074896:=by simp only[actualRegister,registerTemplate];exact ha
  have interval:=StateReadRegisterOuter.remainder_interval (actualRegister p) rn ca
  have old:(actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualRegister,registerTemplate];exact (storageMemory_footprint p hn).2.1
  have head:(AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))).toNat=p.memory.byteSize:=by
    unfold StateReadRegisterOuter.remainderLayout at interval
    unfold remainderLayout
    exact interval.1.trans old
  have before:p.memory.byteSize+12≤(AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat:=
    (congrArg (fun n:Nat=>n+12) old.symm).trans_le interval.2
  exact ⟨head,before⟩

 theorem finalMemory_remainder_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)(address:Nat)
    (above:p.memory.byteSize≤address)
    (before:address+4≤(AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat):
    readI32 (finalMemory p) address=readI32 (AllocateRetry.finalMemory (remainderLayout p)) address:=by
  apply readI32_congr_bytes
  intro i hi
  exact finalMemory_remainder_byte p hn ha (address+i) (by omega) (by omega)

 theorem finalMemory_head_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    readI32 (finalMemory p) p.memory.byteSize=AllocateFlagged.header (AllocateRetry.secondLayout (remainderLayout p)):=by
  have interval:=remainder_interval p hn ha
  have word:=finalMemory_remainder_word p hn ha p.memory.byteSize (by omega) (by omega)
  have actual:=retry_final_head (remainderLayout p) (remainder_native p hn ha)
  rw[interval.1] at actual
  exact word.trans actual

 theorem finalMemory_head_flags(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    readI32 (finalMemory p) p.memory.byteSize &&&3=0:=by
  have word:=finalMemory_head_word p hn ha
  exact (congrArg (fun x:UInt32=>x&&&3) word).trans
    (AllocateFlagged.header_aligned _ (AllocateRetry.native_second _ (remainder_native p hn ha)))

 theorem finalMemory_candidate_flag(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    readI32 (finalMemory p) (p.memory.byteSize+8)&&&1=0:=by
  have interval:=remainder_interval p hn ha
  have word:=finalMemory_remainder_word p hn ha (p.memory.byteSize+8) (by omega) (by omega)
  have actual:=retry_final_candidate_flag (remainderLayout p) (remainder_native p hn ha)
  rw[interval.1] at actual
  exact (congrArg (fun x:UInt32=>x&&&1) word).trans actual
end WNear.Proofs.StateReadStorageOuter
