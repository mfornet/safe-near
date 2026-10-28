import Proofs.StateReadOuterCopies
import Proofs.AllocateLayoutWrapperReadback
import Proofs.PanicAllocateReadback
import NearVM.MemoryListWordRules

/-! Original packed storage words survive219's actual high-then-low copies.
The only address assumptions are bounds in the original memory. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 copiedStorageMemory storageHighMemory storageLowMemory

attribute [local irreducible] AllocateLayoutWrapperReadback.packedCopy

private theorem address_add(m:Memory)(r:UInt32)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize)(k:Nat)(hk:k≤32):
    (r+UInt32.ofNat k).toNat=r.toNat+k:=by
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega :k<2^32)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem packed_eq(m:Memory)(out source:Nat):
    writeI64 m out (readI64 m source)=AllocateLayoutWrapperReadback.packedCopy m out source:=by
  unfold writeI64 AllocateLayoutWrapperReadback.packedCopy
  rfl

private theorem copied_eq(m:Memory)(r:UInt32)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    copiedStorageMemory m r=AllocateLayoutWrapperReadback.packedCopy
      (writeI32 m (r.toNat+32) (readI32 m (r.toNat+16))) (r.toNat+24) (r.toNat+8):=by
  have a32:((r+24)+8).toNat=r.toNat+32:=by rw[UInt32.add_assoc];exact address_add m r hwidth hb 32 (by omega)
  have a16:((r+8)+8).toNat=r.toNat+16:=by rw[UInt32.add_assoc];exact address_add m r hwidth hb 16 (by omega)
  unfold copiedStorageMemory storageLowMemory storageHighMemory
  rw[a32,a16]
  rw[packed_eq]

theorem copied_record(m:Memory)(r:UInt32)(hw:m.wf)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    readI32 (copiedStorageMemory m r) (r.toNat+24)=readI32 m (r.toNat+8) ∧
    readI32 (copiedStorageMemory m r) (r.toNat+28)=readI32 m (r.toNat+12) ∧
    readI32 (copiedStorageMemory m r) (r.toNat+32)=readI32 m (r.toNat+16):=by
  let h:=writeI32 m (r.toNat+32) (readI32 m (r.toNat+16))
  have hs:=writeI32_spec m (r.toNat+32) (readI32 m (r.toNat+16)) hw (by omega)
  have bound:r.toNat+24+8≤h.byteSize:=by rw[hs.2.1];omega
  have low:=AllocateLayoutWrapperReadback.packedCopy_word h (r.toNat+24) (r.toNat+8) 0 hs.1 bound (by omega)
  have high:=AllocateLayoutWrapperReadback.packedCopy_word h (r.toNat+24) (r.toNat+8) 4 hs.1 bound (by omega)
  simp only[Nat.add_zero] at low
  have a:r.toNat+24+4=r.toNat+28:=by omega
  have b:r.toNat+8+4=r.toNat+12:=by omega
  rw[a,b] at high
  have l:=PanicAllocateReadback.read_write_frame m (r.toNat+8) (r.toNat+32) (readI32 m (r.toNat+16)) hw (by omega) (Or.inl (by omega))
  have u:=PanicAllocateReadback.read_write_frame m (r.toNat+12) (r.toNat+32) (readI32 m (r.toNat+16)) hw (by omega) (Or.inl (by omega))
  have packed:=AllocateLayoutWrapperReadback.packedCopy_spec h (r.toNat+24) (r.toNat+8) hs.1 bound
  have self:=PanicAllocateReadback.read_write_self m (r.toNat+32) (readI32 m (r.toNat+16)) hw (by omega)
  have length:readI32 (AllocateLayoutWrapperReadback.packedCopy h (r.toNat+24) (r.toNat+8)) (r.toNat+32)=readI32 h (r.toNat+32):=by
    apply Wasm.Near.MeteredLogic.readI32_congr_bytes
    intro i hi
    rw[packed.2.2.2,ite_eq_right (by omega)]
  rw[copied_eq m r hwidth hb]
  exact ⟨low.trans l,high.trans u,length.trans self⟩

theorem copiedMemory_spec(m:Memory)(r:UInt32)(hw:m.wf)(hwidth:m.byteSize≤2^32)(hb:r.toNat+36≤m.byteSize):
    (copiedStorageMemory m r).wf ∧(copiedStorageMemory m r).byteSize=m.byteSize ∧
    (copiedStorageMemory m r).max=m.max ∧
    ∀j,(j<r.toNat+24 ∨r.toNat+36≤j)→(copiedStorageMemory m r).read8 j=m.read8 j:=by
  have high:=writeI32_spec m (r.toNat+32) (readI32 m (r.toNat+16)) hw (by omega)
  have packed:=AllocateLayoutWrapperReadback.packedCopy_spec (writeI32 m (r.toNat+32) (readI32 m (r.toNat+16)))
    (r.toNat+24) (r.toNat+8) high.1 (by rw[high.2.1];omega)
  rw[copied_eq m r hwidth hb]
  refine ⟨packed.1,packed.2.1.trans high.2.1,packed.2.2.1.trans high.2.2.1,?_⟩
  intro j hj
  rw[packed.2.2.2,ite_eq_right (by omega),high.2.2.2,ite_eq_right (by omega)]
end WNear.Proofs.StateReadOuter
