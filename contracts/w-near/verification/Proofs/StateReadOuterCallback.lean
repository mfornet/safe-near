import Proofs.StateReadOuterNative
import Proofs.AllocationGrowthRemainderShape
import Proofs.StateReadHeaderBytes

/-! The allocator callback word survives548,219's descriptor copies/779, and
both structural allocation templates' stack saves. Only original Native data
are used; no nonempty-heap Native is assumed on the original empty heap. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] readI32 readI64 writeI32 writeI64 storageMemory copiedMemory packedMemory
  preparedStorageMemory AllocatePositive.savedMemory

private theorem saved_word_frame(q:AllocatePositive.Layout)(address:Nat)(hw:q.memory.wf)
    (hb:(AllocatePositive.scratch q).toNat+16≤q.memory.byteSize)
    (hs:(AllocatePositive.scratch q).toNat+16≤address):
    readI32 (AllocatePositive.savedMemory q) address=readI32 q.memory address:=by
  unfold AllocatePositive.savedMemory
  exact PanicAllocateReadback.read_write_frame q.memory address ((AllocatePositive.scratch q).toNat+12)
    (readI32 q.memory q.allocator.toNat) hw (by omega) (Or.inr (by omega))

theorem packed_callback_word(p:Layout)(hn:Native p):
    readI32 (packedMemory p) 1057480=readI32 p.memory 1057480:=by
  have cb:=callback_original_bound p hn
  have n:=scratch_numbers p hn
  have shape:(storageMemory p).wf ∧p.memory.byteSize≤(storageMemory p).byteSize ∧(storageMemory p).max=p.memory.max:=by
    simpa only[storageMemory] using StateReadStorageOuter.finalMemory_shape_original p.toStorage hn.storage hn.allocator
  have prep:=preparedMemory_local_spec (storageMemory p) (scratch p) shape.1
    (by omega)
    (by have w:=p.sp219.toNat_lt;omega)
  have frame:readI32 (packedMemory p) 1057480=readI32 (storageMemory p) 1057480:=by
    apply readI32_congr_bytes
    intro i hi
    unfold packedMemory
    exact prep.2.2.2 _ (Or.inr (by have a:=hn.callbackAbove;omega))
  have original:=StateReadStorageOuter.finalMemory_static_word p.toStorage hn.storage hn.allocator 1057480
    cb.1 cb.2.1 (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr cb.2.2)
  have original2:readI32 (storageMemory p) 1057480=readI32 p.memory 1057480:=by simpa only[storageMemory] using original
  exact frame.trans original2

theorem saved_callback_word(p:Layout)(hn:Native p):
    readI32 (AllocatePositive.savedMemory (actualAllocation p).toPositive) 1057480=
      readI32 (AllocatePositive.savedMemory p.allocationTemplate.toPositive) 1057480:=by
  let q:=p.allocationTemplate.toPositive
  have hsp:=hn.allocationSPBounds
  have n:=scratch_numbers p hn
  have lo:16≤q.sp.toNat:=hsp.1
  have scratchEq:(AllocatePositive.scratch q).toNat=q.sp.toNat-16:=by
    unfold AllocatePositive.scratch
    rw[UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have w:=q.sp.toNat_lt
    omega
  have endEq:(AllocatePositive.scratch q).toNat+16=p.allocationTemplate.sp.toNat:=by
    change (AllocatePositive.scratch q).toNat+16=q.sp.toNat
    omega
  have wf:p.memory.wf:=hn.storage.register.allocation.wf
  have bound:(AllocatePositive.scratch q).toNat+16≤q.memory.byteSize:=by
    change _≤p.allocationTemplate.memory.byteSize
    rw[hn.allocationMemory,endEq];have b:=hn.spBound;omega
  have callback:(AllocatePositive.scratch q).toNat+16≤1057480:=by rw[endEq];have a:=hn.callbackAbove;omega
  have old:=saved_word_frame q 1057480 (by change p.allocationTemplate.memory.wf;rw[hn.allocationMemory];exact wf) bound callback
  have shape:(storageMemory p).wf ∧p.memory.byteSize≤(storageMemory p).byteSize ∧(storageMemory p).max=p.memory.max:=by
    simpa only[storageMemory] using StateReadStorageOuter.finalMemory_shape_original p.toStorage hn.storage hn.allocator
  have prep:=preparedMemory_local_spec (storageMemory p) (scratch p) shape.1
    (by omega)
    (by have w:=p.sp219.toNat_lt;omega)
  have newBound:(AllocatePositive.scratch (actualAllocation p).toPositive).toNat+16≤(actualAllocation p).memory.byteSize:=by
    change (AllocatePositive.scratch q).toNat+16≤(packedMemory p).byteSize
    unfold packedMemory
    rw[prep.2.1]
    rw[endEq]
    have b:=hn.spBound;omega
  have pwf:(packedMemory p).wf:=by simpa only[packedMemory] using prep.1
  have next:=saved_word_frame (actualAllocation p).toPositive 1057480 (by rw[actualAllocation_memory];exact pwf) newBound callback
  have base:=packed_callback_word p hn
  have original:readI32 q.memory 1057480=readI32 p.memory 1057480:=by
    change readI32 p.allocationTemplate.memory 1057480=_
    rw[hn.allocationMemory]
  exact next.trans (base.trans (original.symm.trans old.symm))
end WNear.Proofs.StateReadOuter
