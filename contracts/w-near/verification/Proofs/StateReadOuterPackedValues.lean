import Proofs.StateReadOuterCopyValues
import Proofs.PackWordsCall

/-! Actual219 prepares its decoder descriptor with the real779 word copies.
Original storage words suffice; no prepared-memory lookup is a premise. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 copiedStorageMemory
attribute [local irreducible] PackWords.firstMemory PackWords.packedMemory

def preparedStorageMemory(m:Memory)(r:UInt32):=
  PackWords.packedMemory (copiedStorageMemory m r) r.toNat (r+24).toNat
attribute [local irreducible] preparedStorageMemory

private theorem plus24(m:Memory)(r:UInt32)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    (r+24).toNat=r.toNat+24:=by
  rw[UInt32.toNat_add]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  exact Nat.mod_eq_of_lt (by omega)

private theorem packed_words(m:Memory)(out source:Nat)(hw:m.wf)(hb:out+8≤m.byteSize)(hs:out+8≤source):
    readI32 (PackWords.packedMemory m out source) out=readI32 m source ∧
    readI32 (PackWords.packedMemory m out source) (out+4)=readI32 m (source+8):=by
  have first:=writeI32_spec m (out+4) (readI32 m (source+8)) hw (by omega)
  have shape:(PackWords.firstMemory m out source).wf:=by unfold PackWords.firstMemory;exact first.1
  have bound:out+4≤(PackWords.firstMemory m out source).byteSize:=by
    unfold PackWords.firstMemory;rw[first.2.1];omega
  have sourceRead:readI32 (PackWords.firstMemory m out source) source=readI32 m source:=by
    unfold PackWords.firstMemory
    exact PanicAllocateReadback.read_write_frame m source (out+4) (readI32 m (source+8)) hw (by omega) (Or.inr (by omega))
  have low:=PanicAllocateReadback.read_write_self (PackWords.firstMemory m out source) out
    (readI32 (PackWords.firstMemory m out source) source) shape bound
  have high:=PanicAllocateReadback.read_write_frame (PackWords.firstMemory m out source) (out+4) out
    (readI32 (PackWords.firstMemory m out source) source) shape bound (Or.inr (by omega))
  have oldHigh:readI32 (PackWords.firstMemory m out source) (out+4)=readI32 m (source+8):=by
    unfold PackWords.firstMemory
    exact PanicAllocateReadback.read_write_self m (out+4) (readI32 m (source+8)) hw (by omega)
  unfold PackWords.packedMemory
  exact ⟨low.trans sourceRead,high.trans oldHigh⟩

theorem prepared_record(m:Memory)(r:UInt32)(hw:m.wf)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    readI32 (preparedStorageMemory m r) r.toNat=readI32 m (r.toNat+8) ∧
    readI32 (preparedStorageMemory m r) (r.toNat+4)=readI32 m (r.toNat+16):=by
  have shape:=copiedMemory_spec m r hw hwidth hb
  have words:=packed_words (copiedStorageMemory m r) r.toNat (r+24).toNat shape.1
    (by rw[shape.2.1];omega) (by rw[plus24 m r hwidth hb];omega)
  have a24:=(plus24 m r hwidth hb)
  have a32:r.toNat+24+8=r.toNat+32:=by omega
  rw[a24,a32] at words
  have original:=copied_record m r hw hwidth hb
  unfold preparedStorageMemory
  rw[a24]
  exact ⟨words.1.trans original.1,words.2.trans original.2.2⟩

theorem preparedMemory_spec(m:Memory)(r:UInt32)(hw:m.wf)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    (preparedStorageMemory m r).wf ∧(preparedStorageMemory m r).byteSize=m.byteSize ∧
    (preparedStorageMemory m r).max=m.max ∧
    ∀j,(j<r.toNat ∨r.toNat+36≤j)→(preparedStorageMemory m r).read8 j=m.read8 j:=by
  have old:=copiedMemory_spec m r hw hwidth hb
  have packed:=PackWords.packedMemory_spec (copiedStorageMemory m r) r.toNat (r+24).toNat old.1
    (by rw[old.2.1];omega)
  unfold preparedStorageMemory
  refine ⟨packed.1,packed.2.1.trans old.2.1,packed.2.2.1.trans old.2.2.1,?_⟩
  intro j hj
  rw[packed.2.2.2,ite_eq_right (by omega),ite_eq_right (by omega)]
  exact old.2.2.2 j (by omega)

theorem prepared_storage_vector(m:Memory)(r:UInt32)(hw:m.wf)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    readI32 (preparedStorageMemory m r) (r.toNat+24)=readI32 m (r.toNat+8) ∧
    readI32 (preparedStorageMemory m r) (r.toNat+28)=readI32 m (r.toNat+12) ∧
    readI32 (preparedStorageMemory m r) (r.toNat+32)=readI32 m (r.toNat+16):=by
  have old:=copiedMemory_spec m r hw hwidth hb
  have packed:=PackWords.packedMemory_spec (copiedStorageMemory m r) r.toNat (r+24).toNat old.1
    (by rw[old.2.1];omega)
  have frame(k:Nat)(hk:24≤k):readI32 (preparedStorageMemory m r) (r.toNat+k)=readI32 (copiedStorageMemory m r) (r.toNat+k):=by
    unfold preparedStorageMemory
    apply Wasm.Near.MeteredLogic.readI32_congr_bytes
    intro i hi
    rw[packed.2.2.2,ite_eq_right (by omega),ite_eq_right (by omega)]
  have original:=copied_record m r hw hwidth hb
  exact ⟨(frame 24 (by omega)).trans original.1,(frame 28 (by omega)).trans original.2.1,(frame 32 (by omega)).trans original.2.2⟩
end WNear.Proofs.StateReadOuter
