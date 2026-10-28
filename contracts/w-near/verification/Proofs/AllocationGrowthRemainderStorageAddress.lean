import Proofs.AllocationGrowthRemainderReadAddress

/-! The complete actual548 path retains the newly grown free-head address. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 finalMemory actualRegister StateReadRegisterOuter.readInputMemory

 theorem finalMemory_root_nat(p:Layout)(hn:Native p)(ha:p.allocator=1074896)
    (output:p.out548.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out548.toNat):
    (readI32 (finalMemory p) p.allocator.toNat).toNat=p.memory.byteSize:=by
  have rn:=register_native p hn ha
  have allocator:(actualRegister p).allocator=p.allocator:=by simp only[actualRegister,registerTemplate]
  have ca:(actualRegister p).allocator=1074896:=allocator.trans ha
  have address:=StateReadRegisterOuter.readInputMemory_root_nat (actualRegister p) rn ca
  rw[allocator] at address
  have old:(actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualRegister,registerTemplate];exact (storageMemory_footprint p hn).2.1
  have root:=finalMemory_root_word p hn ha output
  exact (congrArg UInt32.toNat root).trans (address.trans old)
end WNear.Proofs.StateReadStorageOuter
