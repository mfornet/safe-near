import Proofs.AllocationGrowthRemainderFlags
import Proofs.AllocationGrowthRemainderStorageRoot

/-! The actual allocator-root word names the start of the freshly grown page. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocationGrowthRemainder
attribute [local irreducible] readI32 finalMemory AllocateRetry.finalMemory

 theorem finalMemory_root_nat(p:Layout)(hn:Native p)
    (innerOutput:p.out686.toNat+8≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out686.toNat)
    (output:p.out687.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out687.toNat):
    (readI32 (finalMemory p) p.allocator.toNat).toNat=p.memory.byteSize:=by
  let q:=remainderLayout p
  have qn:=remainder_native p hn
  have root:=finalMemory_root p hn innerOutput output
  change readI32 (finalMemory p) p.allocator.toNat=readI32 (AllocateRetry.finalMemory q) p.allocator.toNat at root
  have qa:q.allocator=p.allocator:=by
    simp only[q,remainderLayout,AllocateVector.remainderLayout,AllocateVector.layout690,AllocateVector.actualRecord]
  have qr:=retry_root q qn
  rw[qa] at qr
  have head:=root.trans qr
  exact (congrArg UInt32.toNat head).trans (remainder_head_interval p hn).1
end WNear.Proofs.AllocateVectorOuter
