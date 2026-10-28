import Proofs.AllocationGrowthRemainderReadRoot
import Proofs.AllocationGrowthRemainderStorage

/-! The allocator root survives548's actual read/copy suffix when the original
548 output record is separated from that root. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 finalMemory registeredMemory actualRegister StateReadRegisterOuter.copiedMemory StateReadRegisterOuter.readInputMemory

 theorem finalMemory_root_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (output:p.out548.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out548.toNat):
    readI32 (finalMemory p) p.allocator.toNat=
      readI32 (StateReadRegisterOuter.readInputMemory (actualRegister p)) p.allocator.toNat:=by
  have rn:=register_native p hn ha
  have nums:=stack_numbers p hn
  have lower:=hn.spLower
  have above:=hn.staticAbove
  have allocator:(actualRegister p).allocator=p.allocator:=by
    simp only[actualRegister,registerTemplate]
  have childOut:(actualRegister p).out523=scratch p+16:=by
    simp only[actualRegister,registerTemplate];exact hn.registerOut
  have childSep:(actualRegister p).out523.toNat+12≤(actualRegister p).allocator.toNat:=by
    rw[childOut,allocator,nums.2.2.2,ha]
    change p.sp548.toNat-16+12≤1074896
    omega
  have childAllocator:(actualRegister p).allocator=1074896:=allocator.trans ha
  have child:=StateReadRegisterOuter.copiedMemory_root_word (actualRegister p) rn childAllocator (Or.inl childSep)
  rw[allocator] at child
  have b:=result_bounds p hn ha
  have copy:readI32 (finalMemory p) p.allocator.toNat=readI32 (registeredMemory p) p.allocator.toNat:=by
    apply readI32_congr_bytes
    intro i hi
    unfold finalMemory
    exact StateReadResult.finalMemory_outside (registeredMemory p) p.out548 (scratch p+16)
      b.1 b.2.1 b.2.2.2.1 b.2.2.2.2.2.1 _ (by rcases output with h|h <;> omega)
  have read:readI32 (registeredMemory p) p.allocator.toNat=
      readI32 (StateReadRegisterOuter.readInputMemory (actualRegister p)) p.allocator.toNat:=by
    unfold registeredMemory
    exact child
  exact copy.trans read
end WNear.Proofs.StateReadStorageOuter
