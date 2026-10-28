import Proofs.AllocateRetryState
import NearVM.MemoryListWordRules

/-! Original retry conditions derive the native domain of the actual second search. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem scratch_numbers (p : Layout) (hn : Native p) :
    (scratch p).toNat=p.sp.toNat-16 ∧ (scratch p+12).toNat=(scratch p).toNat+12 ∧
    (scratch p).toNat+16≤p.memory.byteSize ∧ scratch p+16=p.sp := by
  have spLt := p.sp.toNat_lt
  have spLower := hn.spLower
  have spBound := hn.spBound
  have first : (scratch p).toNat=p.sp.toNat-16 := by
    rw [scratch,AllocatePositive.scratch,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  refine ⟨first,?_,by omega,UInt32.sub_add_cancel p.sp 16⟩
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem saved_shape (p : Layout) (hn : Native p) :
    (savedMemory p).wf ∧ (savedMemory p).byteSize=p.memory.byteSize ∧ (savedMemory p).max=p.memory.max := by
  have bound := (scratch_numbers p hn).2.2.1
  have h := writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf (by omega)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem saved_size (p : Layout) (hn : Native p) : (savedMemory p).size=p.memory.size := by
  have h := (saved_shape p hn).2.1
  change (savedMemory p).size*65536=p.memory.size*65536 at h
  omega

theorem saved_root (p : Layout) (hn : Native p) : readI32 (savedMemory p) ((scratch p).toNat+12)=0 := by
  have bound := (scratch_numbers p hn).2.2.1
  have h := PanicAllocateReadback.read_write_self p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf (by omega)
  simpa only [savedMemory,AllocatePositive.savedMemory,scratch,AllocatePositive.scratch,hn.empty] using h

/-- No native property of the second search is assumed: it follows from the
original empty head, growth, and the actual two sequential link stores. -/
theorem native_second (p : Layout) (hn : Native p) : AllocateFlagged.Native (secondLayout p) := by
  have shape := saved_shape p hn
  have bounds := scratch_numbers p hn
  have recordBound : (growthLayout p).record.toNat+16≤(growthLayout p).memory.byteSize := by
    change (scratch p).toNat+16≤(savedMemory p).byteSize
    rw [shape.2.1]
    exact bounds.2.2.1
  have empty : readI32 (growthLayout p).memory ((growthLayout p).record.toNat+12)=0 := saved_root p hn
  have width : (growthLayout p).memory.byteSize≤2^32 := by change (savedMemory p).byteSize≤2^32;rw [shape.2.1];exact hn.width
  have positive : 0<(growthLayout p).memory.size := by change 0<(savedMemory p).size;rw [saved_size p hn];exact hn.oldPositive
  have pages : (growthLayout p).memory.size+(AllocateGrowth.delta (growthLayout p)).toNat<65536 := by
    change (savedMemory p).size+(AllocateGrowth.delta (growthLayout p)).toNat<65536
    rw [saved_size p hn]
    exact hn.pagesBound
  have vt : (AllocatePositive.searchLayout p.toLayout).vtable.toNat+20≤(growthLayout p).memory.byteSize := by
    change 1057464+20≤(savedMemory p).byteSize
    rw [shape.2.1]
    exact hn.vtableBound
  exact retry_native (AllocatePositive.searchLayout p.toLayout) (growthLayout p) hn.growth recordBound empty width positive pages hn.wordsPositive hn.room vt

theorem Native.second (p : Layout) (hn : Native p) : AllocateFlagged.Native (secondLayout p) := native_second p hn

private theorem retry_word_frame (p : AllocateGrowth.Layout) (hn : AllocateGrowth.Native p)
    (address : Nat) (hrecord : p.record.toNat+16≤p.memory.byteSize) (haddress : address+4≤p.memory.byteSize)
    (hsep : p.record.toNat+16≤address ∨ address+4≤p.record.toNat) :
    readI32 (retryMemory p) address=readI32 p.memory address := by
  have grow := hn.grown_spec p
  have growBytes := (Memory.grow_spec hn.wf hn.grow).2.2.2.2
  have headerNat := growth_header_nat p hn
  have fresh := AllocateGrowth.freshMemory_spec p.grown (AllocateGrowth.header p) (AllocateGrowth.blockBytes p) grow.1 grow.2.2.1
  have recordBound : p.record.toNat+8≤(AllocateGrowth.committedMemory p).byteSize := by
    change p.record.toNat+8≤(AllocateGrowth.freshMemory _ _ _).byteSize
    rw [fresh.2.1]
    exact grow.2.2.2
  have record := AllocateGrowth.recordMemory_spec (AllocateGrowth.committedMemory p) p.record (AllocateGrowth.header p) fresh.1 recordBound
  have growth := AllocateGrowth.finalMemory_spec p hn
  have hh : (AllocateGrowth.header p).toNat+12≤(AllocateGrowth.finalMemory p).byteSize := by rw [growth.2.1,←grow.2.1];exact grow.2.2.1
  have first := writeI32_spec (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+8)
    (readI32 (AllocateGrowth.finalMemory p) (p.record.toNat+12)) growth.1 (by omega)
  have second := writeI32_spec (writeI32 (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+8)
    (readI32 (AllocateGrowth.finalMemory p) (p.record.toNat+12))) (p.record.toNat+12) (AllocateGrowth.header p)
    first.1 (by rw [first.2.1,growth.2.1];omega)
  apply readI32_congr_bytes
  intro i hi
  have jold : address+i<p.memory.byteSize := by omega
  have awayHeader : ¬((AllocateGrowth.header p).toNat+8≤address+i ∧ address+i<(AllocateGrowth.header p).toNat+8+4) := by rw [headerNat];omega
  have awayRecord : ¬(p.record.toNat+12≤address+i ∧ address+i<p.record.toNat+12+4) := by rcases hsep with h|h <;> omega
  have recordOutside : address+i<p.record.toNat ∨ p.record.toNat+8≤address+i := by rcases hsep with h|h <;> omega
  change (writeI32 (writeI32 (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+8)
    (readI32 (AllocateGrowth.finalMemory p) (p.record.toNat+12))) (p.record.toNat+12) (AllocateGrowth.header p)).read8 (address+i)=_
  rw [second.2.2.2,ite_eq_right awayRecord,first.2.2.2,ite_eq_right awayHeader]
  change (AllocateGrowth.recordMemory (AllocateGrowth.committedMemory p) p.record (AllocateGrowth.header p)).read8 (address+i)=_
  rw [record.2.2.2 _ recordOutside]
  change (AllocateGrowth.freshMemory p.grown (AllocateGrowth.header p) (AllocateGrowth.blockBytes p)).read8 (address+i)=_
  rw [fresh.2.2.2 _ (Or.inl (by rw [headerNat];exact jold)),growBytes,ite_eq_left jold]

/-- Original scratch/vtable separation preserves the callback selector through
memory growth, fresh-header initialization, result-record and retry-link writes. -/
theorem callback_word (p : Layout) (hn : Native p) :
    readI32 (secondLayout p).memory (1057464+16)=readI32 (savedMemory p) (1057464+16) := by
  have shape := saved_shape p hn
  have bounds := scratch_numbers p hn
  have hr : (growthLayout p).record.toNat+16≤(growthLayout p).memory.byteSize := by
    change (scratch p).toNat+16≤(savedMemory p).byteSize
    rw [shape.2.1]
    exact bounds.2.2.1
  have ha : 1057464+16+4≤(growthLayout p).memory.byteSize := by
    change 1057464+16+4≤(savedMemory p).byteSize
    rw [shape.2.1]
    exact hn.vtableBound
  exact retry_word_frame (growthLayout p) hn.growth (1057464+16) hr ha hn.callbackSep
end WNear.Proofs.AllocateRetry
