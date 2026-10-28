import Proofs.AllocateRetryPayload
import Proofs.AllocateFlaggedOldFrame

namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 writeI64

theorem retryMemory_byte_frame (p : AllocateGrowth.Layout) (hn : AllocateGrowth.Native p)
    (j : Nat) (hrecord : p.record.toNat+16≤p.memory.byteSize) (hj : j<p.memory.byteSize)
    (hsep : p.record.toNat+16≤j ∨ j<p.record.toNat) :
    (retryMemory p).read8 j=p.memory.read8 j := by
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
  have jold : j<p.memory.byteSize := hj
  have awayHeader : ¬((AllocateGrowth.header p).toNat+8≤j ∧ j<(AllocateGrowth.header p).toNat+8+4) := by rw [headerNat];omega
  have awayRecord : ¬(p.record.toNat+12≤j ∧ j<p.record.toNat+12+4) := by rcases hsep with h|h <;> omega
  have recordOutside : j<p.record.toNat ∨ p.record.toNat+8≤j := by rcases hsep with h|h <;> omega
  change (writeI32 (writeI32 (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+8)
    (readI32 (AllocateGrowth.finalMemory p) (p.record.toNat+12))) (p.record.toNat+12) (AllocateGrowth.header p)).read8 (j)=_
  rw [second.2.2.2,ite_eq_right awayRecord,first.2.2.2,ite_eq_right awayHeader]
  change (AllocateGrowth.recordMemory (AllocateGrowth.committedMemory p) p.record (AllocateGrowth.header p)).read8 (j)=_
  rw [record.2.2.2 _ recordOutside]
  change (AllocateGrowth.freshMemory p.grown (AllocateGrowth.header p) (AllocateGrowth.blockBytes p)).read8 (j)=_
  rw [fresh.2.2.2 _ (Or.inl (by rw [headerNat];exact jold)),growBytes,ite_eq_left jold]


/-- Successful growth and retry retain original bytes above the shadow stack,
except the allocator head cell. -/
theorem finalMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.memory.byteSize) (hsp : p.sp.toNat≤j)
    (ha : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have saved := saved_shape p hn
  have nums := scratch_numbers p hn
  have lower := hn.spLower
  have searched := searchedMemory_spec p hn
  have cb : p.allocator.toNat+4≤(searchedMemory p).byteSize := by
    rw [searched.2.1];have := hn.allocatorBound;omega
  have last := writeI32_spec (searchedMemory p) p.allocator.toNat
    (readI32 (searchedMemory p) ((scratch p).toNat+12)) searched.1 cb
  unfold finalMemory
  rw [last.2.2.2 j,ite_eq_right (by omega)]
  have headEq : AllocateSearch.head (secondLayout p)=AllocateGrowth.header (growthLayout p) := by
    change readI32 (retryMemory (growthLayout p)) ((scratch p)+12).toNat=_
    rw [nums.2.1]
    exact (retry_reads (growthLayout p) hn.growth
      (by change (scratch p).toNat+16≤(savedMemory p).byteSize;rw [saved.2.1];exact nums.2.2.1)
      (saved_root p hn)).1
  have hhead : j<(AllocateSearch.head (secondLayout p)).toNat := by
    rw [headEq,growth_header_nat (growthLayout p) hn.growth]
    change j<(savedMemory p).byteSize
    rw [saved.2.1];exact hj
  change (AllocateFlagged.finalMemory (secondLayout p)).read8 j=_
  rw [AllocateFlagged.finalMemory_below_head (secondLayout p) (native_second p hn) j hhead]
  have pre := retryMemory_byte_frame (growthLayout p) hn.growth j
    (by change (scratch p).toNat+16≤(savedMemory p).byteSize;rw [saved.2.1];exact nums.2.2.1)
    (by change j<(savedMemory p).byteSize;rw [saved.2.1];exact hj)
    (Or.inl (by change (scratch p).toNat+16≤j;omega))
  rw [show (secondLayout p).memory=retryMemory (growthLayout p) from rfl,pre]
  have sv := writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat)
    hn.wf (by omega)
  change (writeI32 p.memory ((scratch p).toNat+12) _).read8 j=_
  rw [sv.2.2.2 j,ite_eq_right (by omega)]

theorem result_above_original (p : Layout) (hn : Native p) :
    p.memory.byteSize≤(result p).toNat := by
  have nums := scratch_numbers p hn
  have saved := saved_shape p hn
  have second := native_second p hn
  have headEq : AllocateSearch.head (secondLayout p)=AllocateGrowth.header (growthLayout p) := by
    change readI32 (retryMemory (growthLayout p)) ((scratch p)+12).toNat=_
    rw [nums.2.1]
    exact (retry_reads (growthLayout p) hn.growth
      (by change (scratch p).toNat+16≤(savedMemory p).byteSize;rw [saved.2.1];exact nums.2.2.1)
      (saved_root p hn)).1
  have headNat : (AllocateSearch.head (secondLayout p)).toNat=p.memory.byteSize := by
    rw [headEq,growth_header_nat (growthLayout p) hn.growth]
    exact saved.2.1
  have ptr := Allocate.split_pointer_toNat (secondLayout p).memory (AllocateSearch.head (secondLayout p))
    (secondLayout p).words second.split
  have room := second.split.room
  change (AllocateSearch.head (secondLayout p)).toNat+80+(secondLayout p).words.toNat*4≤
    (Allocate.endWord (secondLayout p).memory (AllocateSearch.head (secondLayout p))).toNat at room
  change p.memory.byteSize≤(Allocate.splitPointer (secondLayout p).memory
    (AllocateSearch.head (secondLayout p)) (secondLayout p).words).toNat
  rw [ptr]
  omega

end WNear.Proofs.AllocateRetry
