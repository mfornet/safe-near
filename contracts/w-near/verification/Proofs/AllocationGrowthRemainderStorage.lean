import Proofs.AllocationGrowthRemainderRead
import Proofs.StateReadStorageOuterResultOutput

/-! The actual548 option conversion preserves new-page free-list bytes before
the register payload. The result copy remains sequential and alias-aware. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 finalMemory registeredMemory actualRegister StateReadRegisterOuter.actualVector AllocateRetry.finalMemory AllocateVector.remainderLayout

def remainderLayout(p:Layout):AllocateRetry.Layout:=
  AllocateVector.remainderLayout (StateReadRegisterOuter.actualVector (actualRegister p)).toVector

 theorem finalMemory_remainder_byte(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (j:Nat)(above:p.memory.byteSize≤j)
    (before:j<(AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory (remainderLayout p)).read8 j:=by
  have b:=result_bounds p hn ha
  have output:=hn.outputBound
  have copy:(finalMemory p).read8 j=(registeredMemory p).read8 j:=by
    unfold finalMemory
    exact StateReadResult.finalMemory_outside (registeredMemory p) p.out548 (scratch p+16)
      b.1 b.2.1 b.2.2.2.1 b.2.2.2.2.2.1 j (Or.inr (by omega))
  have old:(actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualRegister,registerTemplate]
    exact (storageMemory_footprint p hn).2.1
  have above':(actualRegister p).memory.byteSize≤j:=by rw[old];exact above
  have allocator:(actualRegister p).allocator=1074896:=by simp only[actualRegister,registerTemplate];exact ha
  have child:(registeredMemory p).read8 j=(AllocateRetry.finalMemory (remainderLayout p)).read8 j:=by
    unfold registeredMemory remainderLayout
    exact StateReadRegisterOuter.copiedMemory_remainder_byte (actualRegister p) (register_native p hn ha) allocator
      j above' before
  exact copy.trans child
end WNear.Proofs.StateReadStorageOuter
