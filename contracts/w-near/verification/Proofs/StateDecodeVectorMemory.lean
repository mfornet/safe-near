import Proofs.StateDecodeVectorNative
import Proofs.AllocateLayoutWrapperReadback
import Proofs.AllocateSplitReadback

/-! Original allocation words are cached before373's zero-length store.
The output may overlap the raw allocation record without changing the snapshot. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI64 writeI32

private theorem snapshot_word (original current:Memory) (out source offset:Nat)
    (hw:current.wf) (hb:out+8≤current.byteSize) (ho:offset+4≤8) :
    readI32 (writeI64 current out (readI64 original source)) (out+offset)=readI32 original (source+offset) := by
  have spec:=writeI64_spec current out (readI64 original source) hw hb
  have bytes (i:Nat) (hi:i<4) :
      (writeI64 current out (readI64 original source)).read8 (out+offset+i)=original.read8 (source+offset+i) := by
    rw[spec.2.2.2]
    have yes:out≤out+offset+i ∧out+offset+i<out+8:=by omega
    rw[ite_eq_left yes]
    have off:out+offset+i-out=offset+i:=by omega
    rw[off,AllocateLayoutWrapperReadback.readI64_byte _ _ (offset+i) (by omega)]
    simp only[Nat.add_assoc]
  have zero:(writeI64 current out (readI64 original source)).read8 (out+offset)=original.read8 (source+offset):=by
    simpa only[Nat.add_zero] using bytes 0 (by omega)
  simp[readI32,List.range_succ,bytes,zero]

theorem finalMemory_shape (p:Layout) (hn:Native p) :
    (finalMemory p).wf ∧(finalMemory p).byteSize=p.memory.byteSize ∧(finalMemory p).max=p.memory.max := by
  have a:=allocated_spec p hn
  have zbound:p.outVector.toNat+8+4≤(memoryAllocated p).byteSize:=by rw[a.2.1];exact hn.outBound
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 zbound
  have bound:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1]
    have h:=hn.outBound
    omega
  have f:=writeI64_spec (zeroMemory p) p.outVector.toNat (packed p) z.1 bound
  exact ⟨f.1,f.2.1.trans (z.2.1.trans a.2.1),f.2.2.1.trans (z.2.2.1.trans a.2.2.1)⟩

theorem finalMemory_pointer (p:Layout) (hn:Native p) :
    readI32 (finalMemory p) p.outVector.toNat=StateDecodeRaw.result p.toRaw := by
  have a:=allocated_spec p hn
  have nums:=stack_numbers p hn
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 (by rw[a.2.1];exact hn.outBound)
  have bound:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1]
    have h:=hn.outBound;omega
  have word:=snapshot_word (memoryAllocated p) (zeroMemory p) p.outVector.toNat ((scratch p).toNat+8) 0 z.1 bound (by omega)
  have original:readI32 (memoryAllocated p) ((scratch p).toNat+8)=StateDecodeRaw.result p.toRaw:=by rw[←nums.2.2.1];exact a.2.2.2.1
  have one:readI32 (finalMemory p) p.outVector.toNat=readI32 (memoryAllocated p) ((scratch p).toNat+8):=by
    simpa only[finalMemory,packed,Nat.add_zero] using word
  exact one.trans original

theorem finalMemory_capacity (p:Layout) (hn:Native p) :
    readI32 (finalMemory p) (p.outVector.toNat+4)=p.size := by
  have a:=allocated_spec p hn
  have nums:=stack_numbers p hn
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 (by rw[a.2.1];exact hn.outBound)
  have bound:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1]
    have h:=hn.outBound;omega
  have word:=snapshot_word (memoryAllocated p) (zeroMemory p) p.outVector.toNat ((scratch p).toNat+8) 4 z.1 bound (by omega)
  have original:readI32 (memoryAllocated p) ((scratch p).toNat+8+4)=p.size:=by rw[←nums.2.2.1];exact a.2.2.2.2
  have one:readI32 (finalMemory p) (p.outVector.toNat+4)=readI32 (memoryAllocated p) ((scratch p).toNat+8+4):=by
    simpa only[finalMemory,packed] using word
  exact one.trans original

theorem finalMemory_length (p:Layout) (hn:Native p) :
    readI32 (finalMemory p) (p.outVector.toNat+8)=0 := by
  have a:=allocated_spec p hn
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 (by rw[a.2.1];exact hn.outBound)
  have bound:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1]
    have h:=hn.outBound;omega
  have f:=writeI64_spec (zeroMemory p) p.outVector.toNat (packed p) z.1 bound
  have self:=PanicAllocateReadback.read_write_self (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 (by rw[a.2.1];exact hn.outBound)
  calc
    _=readI32 (zeroMemory p) (p.outVector.toNat+8):=by
      apply Allocate.readI32_congr_bytes
      intro i hi
      have no:¬(p.outVector.toNat≤p.outVector.toNat+8+i ∧p.outVector.toNat+8+i<p.outVector.toNat+8):=by omega
      unfold finalMemory
      rw[f.2.2.2]
      exact ite_eq_right no
    _=0:=self
end WNear.Proofs.StateDecodeVector
