import Proofs.StateReadOuterPackedValues
import Proofs.StateReadStorageOuterPayload
import Proofs.StateReadHeaderBytes

/-! Original storage bytes give the decoder's header after219's descriptor copies.
Only the original scratch address must fit UInt32; grown-memory width is unnecessary. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64
  storageHighMemory storageLowMemory copiedStorageMemory preparedStorageMemory
  PackWords.firstMemory PackWords.packedMemory

/-- Local address validity suffices even when the memory has grown. -/
theorem preparedMemory_local_spec (m : Memory) (r : UInt32) (hw : m.wf)
    (hb : r.toNat+36≤m.byteSize) (ha : r.toNat+36≤2^32) :
    (preparedStorageMemory m r).wf ∧ (preparedStorageMemory m r).byteSize=m.byteSize ∧
    (preparedStorageMemory m r).max=m.max ∧
    ∀j,(j<r.toNat ∨r.toNat+36≤j)→(preparedStorageMemory m r).read8 j=m.read8 j := by
  have add (k : Nat) (hk : k≤32) : (r+UInt32.ofNat k).toNat=r.toNat+k := by
    rw [UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : k<2^32)]
    exact Nat.mod_eq_of_lt (by omega)
  have a32 : ((r+24)+8).toNat=r.toNat+32 := by
    rw [UInt32.add_assoc]; exact add 32 (by omega)
  have a24 : (r+24).toNat=r.toNat+24 := add 24 (by omega)
  have high := writeI32_spec m ((r+24)+8).toNat (readI32 m ((r+8)+8).toNat) hw (by rw [a32];omega)
  have low := writeI64_spec (storageHighMemory m r) (r.toNat+24)
    (readI64 (storageHighMemory m r) (r.toNat+8))
    (by simpa only [storageHighMemory] using high.1)
    (by simpa only [storageHighMemory,high.2.1] using (show r.toNat+24+8≤m.byteSize by omega))
  have highSize : (storageHighMemory m r).byteSize=m.byteSize := by
    simpa only [storageHighMemory] using high.2.1
  have highMax : (storageHighMemory m r).max=m.max := by
    simpa only [storageHighMemory] using high.2.2.1
  have old : (copiedStorageMemory m r).wf ∧ (copiedStorageMemory m r).byteSize=m.byteSize ∧
      (copiedStorageMemory m r).max=m.max ∧
      ∀j,(j<r.toNat ∨r.toNat+36≤j)→(copiedStorageMemory m r).read8 j=m.read8 j := by
    unfold copiedStorageMemory storageLowMemory
    refine ⟨low.1,low.2.1.trans highSize,low.2.2.1.trans highMax,?_⟩
    intro j hj
    rw [low.2.2.2,ite_eq_right (by omega)]
    unfold storageHighMemory
    rw [high.2.2.2,ite_eq_right (by rw [a32];omega)]
  have packed := PackWords.packedMemory_spec (copiedStorageMemory m r) r.toNat (r+24).toNat old.1
    (by rw [old.2.1];omega)
  unfold preparedStorageMemory
  refine ⟨packed.1,packed.2.1.trans old.2.1,packed.2.2.1.trans old.2.2.1,?_⟩
  intro j hj
  rw [packed.2.2.2,ite_eq_right (by omega),ite_eq_right (by omega)]
  exact old.2.2.2 j hj

/-- Canonical storage supplies the full original29-byte header, without a future
header predicate or a bound on the final grown memory. -/
theorem prepared_storage_header (p : StateReadStorageOuter.Layout) (r : UInt32)
    (hn : StateReadStorageOuter.Native p) (ha : p.allocator=1074896)
    (state : WNear.State) (hbytes : p.bytes=WNear.header state)
    (hr : r.toNat+36≤p.memory.byteSize) :
    StateReadHeaderBytes.At
      (preparedStorageMemory (StateReadStorageOuter.finalMemory p) r)
      (AllocateVector.result (StateReadRegisterOuter.actualVector
        (StateReadStorageOuter.actualRegister p)).toVector).toNat state := by
  have shape := StateReadRegisterOuter.copiedMemory_spec (StateReadStorageOuter.actualRegister p)
    (StateReadStorageOuter.register_native p hn ha) ha
  have old : (StateReadStorageOuter.actualRegister p).memory.byteSize=p.memory.byteSize := by
    change (StateReadStorageOuter.storageMemory p).byteSize=p.memory.byteSize
    exact (StateReadStorageOuter.storageMemory_footprint p hn).2.1
  have grows : p.memory.byteSize≤(StateReadStorageOuter.finalMemory p).byteSize := by
    have g := shape.2.1
    rw [old] at g
    have f := StateReadStorageOuter.finalMemory_shape p hn ha
    rw [f.2.1]
    exact g
  have prep := preparedMemory_local_spec (StateReadStorageOuter.finalMemory p) r
    (StateReadStorageOuter.finalMemory_shape p hn ha).1 (by omega)
    (by have width := hn.register.allocation.width;omega)
  have above := StateReadStorageOuter.registered_pointer_above p hn ha
  intro i hi
  rw [prep.2.2.2 _ (Or.inr (by omega))]
  have byte := StateReadStorageOuter.finalMemory_payload p hn ha i
    (by rw [hbytes,StateReadHeaderBytes.header_length];exact hi)
  simpa only [hbytes] using byte
end WNear.Proofs.StateReadOuter
