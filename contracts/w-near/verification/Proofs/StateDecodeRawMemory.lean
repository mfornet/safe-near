import Proofs.StateDecodeRawNative
import Proofs.StateDecodeSlicesResult

/-! Exact real770/769/767 record writes. The middle wrapper reloads its high
source after its low store; only the actual fixed-stack separation justifies
that reload. Caller output may alias any earlier record or payload. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 allocatedMemory AllocatePositive.finalMemory

theorem record_numbers (p : Layout) (hn : Native p) :
    (out770 p).toNat=p.spRaw.toNat-40 ∧
    (scratch p+16).toNat=p.spRaw.toNat-16 ∧
    (scratch p).toNat+20=(scratch p+16).toNat+4 := by
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have hi:=p.spRaw.toNat_lt
  have first : (out770 p).toNat=p.spRaw.toNat-40 := by
    rw [out770,UInt32.toNat_add,n.2.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have second : (scratch p+16).toNat=p.spRaw.toNat-16 := by
    rw [UInt32.toNat_add,n.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  refine ⟨first,second,?_⟩
  rw [n.1,second]
  omega

theorem allocated_spec (p : Layout) (hn : Native p) :
    (allocatedMemory p).wf ∧ (allocatedMemory p).byteSize=p.memory.byteSize ∧
    (allocatedMemory p).max=p.memory.max ∧ result p≠0 := by
  have a:=allocation_native p hn
  have s:=AllocatePositive.finalMemory_spec (actualPositive p) a
  have ls:=layout_spec p hn
  unfold allocatedMemory
  refine ⟨s.1,s.2.1.trans ls.2.1,s.2.2.trans ls.2.2,?_⟩
  exact (AllocatePositive.result_nonzero_and_span (actualPositive p) a).1

theorem memory770_spec (p : Layout) (hn : Native p) :
    (memory770 p).wf ∧ (memory770 p).byteSize=p.memory.byteSize ∧
    (memory770 p).max=p.memory.max ∧
    readI32 (memory770 p) (out770 p).toNat=result p ∧
    readI32 (memory770 p) ((out770 p).toNat+4)=p.size := by
  have s:=allocated_spec p hn
  have n:=record_numbers p hn
  have lo:=hn.spLower
  have hi:=hn.spBound
  have bound : (out770 p).toNat+8≤(allocatedMemory p).byteSize := by rw [s.2.1,n.1];omega
  have sh:=StateDecodeSlices.finalMemory_spec false (allocatedMemory p) (out770 p) (result p) p.size p.size s.1 bound
  have words:=StateDecodeSlices.finalMemory_words false (allocatedMemory p) (out770 p) (result p) p.size p.size s.1 bound
  have eq : memory770 p=StateDecodeSlices.finalMemory false (allocatedMemory p) (out770 p) (result p) p.size p.size:=rfl
  rw [eq]
  exact ⟨sh.1,sh.2.1.trans s.2.1,sh.2.2.1.trans s.2.2.1,words.1,words.2⟩

theorem memory769_spec (p : Layout) (hn : Native p) :
    (memory769 p).wf ∧ (memory769 p).byteSize=p.memory.byteSize ∧
    (memory769 p).max=p.memory.max ∧
    readI32 (memory769 p) (scratch p+16).toNat=result p ∧
    readI32 (memory769 p) ((scratch p+16).toNat+4)=p.size := by
  have s:=memory770_spec p hn
  have n:=record_numbers p hn
  have lo:=hn.spLower
  have hi:=hn.spBound
  have lb : (scratch p+16).toNat+4≤(memory770 p).byteSize := by rw [s.2.1,n.2.1];omega
  have low:=writeI32_spec (memory770 p) (scratch p+16).toNat (readI32 (memory770 p) (out770 p).toNat) s.1 lb
  have sourceFrame:=PanicAllocateReadback.read_write_frame (memory770 p) ((out770 p).toNat+4)
    (scratch p+16).toNat (readI32 (memory770 p) (out770 p).toNat) s.1 lb (Or.inl (by rw[n.1,n.2.1];omega))
  have source : readI32 (lowMemory769 p) ((out770 p).toNat+4)=p.size := sourceFrame.trans s.2.2.2.2
  have hb : (scratch p+16).toNat+4+4≤(lowMemory769 p).byteSize := by
    change _≤(writeI32 _ _ _).byteSize
    rw [low.2.1,s.2.1,n.2.1];omega
  have high:=writeI32_spec (lowMemory769 p) ((scratch p+16).toNat+4)
    (readI32 (lowMemory769 p) ((out770 p).toNat+4)) low.1 hb
  have lowSelf:=PanicAllocateReadback.read_write_self (memory770 p) (scratch p+16).toNat
    (readI32 (memory770 p) (out770 p).toNat) s.1 lb
  have lowFrame:=PanicAllocateReadback.read_write_frame (lowMemory769 p) (scratch p+16).toNat
    ((scratch p+16).toNat+4) (readI32 (lowMemory769 p) ((out770 p).toNat+4)) low.1 hb (Or.inl (by omega))
  have highSelf:=PanicAllocateReadback.read_write_self (lowMemory769 p) ((scratch p+16).toNat+4)
    (readI32 (lowMemory769 p) ((out770 p).toNat+4)) low.1 hb
  exact ⟨high.1,high.2.1.trans (low.2.1.trans s.2.1),high.2.2.1.trans (low.2.2.1.trans s.2.2.1),
    lowFrame.trans (lowSelf.trans s.2.2.2.1),highSelf.trans source⟩

theorem cached_words (p : Layout) (hn : Native p) : cachedPointer p=result p ∧ cachedLength p=p.size := by
  have s:=memory769_spec p hn
  refine ⟨s.2.2.2.1,?_⟩
  unfold cachedLength
  rw [(record_numbers p hn).2.2]
  exact s.2.2.2.2

/-- Both767 words were cached before the output writes, so these exact final
readbacks need no caller-output separation from the source records or heap. -/
theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧
    (finalMemory p).max=p.memory.max ∧
    readI32 (finalMemory p) p.outRaw.toNat=result p ∧
    readI32 (finalMemory p) (p.outRaw.toNat+4)=p.size ∧
    ∀j,j<p.outRaw.toNat ∨ p.outRaw.toNat+8≤j → (finalMemory p).read8 j=(memory769 p).read8 j := by
  have s:=memory769_spec p hn
  have cache:=cached_words p hn
  have lb : p.outRaw.toNat+4≤(memory769 p).byteSize := by rw [s.2.1];have h:=hn.outBound;omega
  have low:=writeI32_spec (memory769 p) p.outRaw.toNat (cachedPointer p) s.1 lb
  have hb : p.outRaw.toNat+4+4≤(writeI32 (memory769 p) p.outRaw.toNat (cachedPointer p)).byteSize := by
    rw [low.2.1,s.2.1];exact hn.outBound
  have high:=writeI32_spec (writeI32 (memory769 p) p.outRaw.toNat (cachedPointer p)) (p.outRaw.toNat+4) (cachedLength p) low.1 hb
  have lowSelf:=PanicAllocateReadback.read_write_self (memory769 p) p.outRaw.toNat (cachedPointer p) s.1 lb
  have lowFrame:=PanicAllocateReadback.read_write_frame (writeI32 (memory769 p) p.outRaw.toNat (cachedPointer p)) p.outRaw.toNat
    (p.outRaw.toNat+4) (cachedLength p) low.1 hb (Or.inl (by omega))
  have highSelf:=PanicAllocateReadback.read_write_self (writeI32 (memory769 p) p.outRaw.toNat (cachedPointer p))
    (p.outRaw.toNat+4) (cachedLength p) low.1 hb
  refine ⟨high.1,high.2.1.trans (low.2.1.trans s.2.1),high.2.2.1.trans (low.2.2.1.trans s.2.2.1),
    lowFrame.trans (lowSelf.trans cache.1),highSelf.trans cache.2,?_⟩
  intro j hj
  unfold finalMemory
  rw [high.2.2.2 j,ite_eq_right (show ¬(p.outRaw.toNat+4≤j ∧ j<p.outRaw.toNat+4+4) by omega),
    low.2.2.2 j,ite_eq_right (show ¬(p.outRaw.toNat≤j ∧ j<p.outRaw.toNat+4) by omega)]
end WNear.Proofs.StateDecodeRaw
