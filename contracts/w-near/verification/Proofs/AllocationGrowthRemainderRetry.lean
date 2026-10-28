import Proofs.AllocationGrowthRemainderRoom
import Proofs.AllocateRetryPayload

/-! The original successful growth domain provides a whole fresh page before
splitting, hence enough actual remainder for the decoder's next allocation. -/
namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

private theorem tagged_mask(x:UInt32)(h:x &&&3=0):
    (x|||2)&&&4294967292=x:=by
  have flags:=congrArg UInt32.toBitVec h
  simp only[UInt32.toBitVec_and] at flags
  apply UInt32.toBitVec_inj.mp
  have dist:=BitVec.and_or_distrib_left (x:=x.toBitVec)
    (y:=(4294967292:UInt32).toBitVec) (z:=(3:UInt32).toBitVec)
  simp only[show (4294967292:UInt32).toBitVec||| (3:UInt32).toBitVec=BitVec.allOnes 32 by rfl,
    BitVec.and_allOnes,flags,show (0:UInt32).toBitVec=0#32 by rfl,BitVec.or_zero] at dist
  simp only[UInt32.toBitVec_and,UInt32.toBitVec_or,BitVec.and_or_distrib_right,←dist,
    show (2:UInt32).toBitVec &&& (4294967292:UInt32).toBitVec=0#32 by rfl,BitVec.or_zero]

/-- Exact first and last addresses of the actual second-search free block. -/
theorem retry_interval(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    (AllocateFlagged.head (AllocateRetry.secondLayout p)).toNat=p.memory.byteSize ∧
    (AllocateFlagged.finish (AllocateRetry.secondLayout p)).toNat=
      p.memory.byteSize+(AllocateGrowth.delta (AllocateRetry.growthLayout p)).toNat*65536:=by
  let g:=AllocateRetry.growthLayout p
  have shape:=AllocateRetry.saved_shape p hn
  have bounds:=AllocateRetry.scratch_numbers p hn
  have hb:g.record.toNat+16≤g.memory.byteSize:=by
    change (AllocateRetry.scratch p).toNat+16≤(AllocateRetry.savedMemory p).byteSize
    rw[shape.2.1];exact bounds.2.2.1
  have he:readI32 g.memory (g.record.toNat+12)=0:=AllocateRetry.saved_root p hn
  have reads:=AllocateRetry.retry_reads g hn.growth hb he
  have headerNat: (AllocateGrowth.header g).toNat=p.memory.byteSize:=
    (AllocateRetry.growth_header_nat g hn.growth).trans shape.2.1
  have bytesNat:(AllocateGrowth.blockBytes g).toNat=(AllocateGrowth.delta g).toNat*65536:=
    AllocateGrowth.pageBytes_toNat (AllocateGrowth.delta g) hn.growth.pagesBound
  have pages:p.memory.size+(AllocateGrowth.delta g).toNat<65536:=hn.pagesBound
  have endLt:p.memory.byteSize+(AllocateGrowth.delta g).toNat*65536<2^32:=by
    change p.memory.size*65536+(AllocateGrowth.delta g).toNat*65536<2^32
    omega
  have endNat:(AllocateGrowth.header g+AllocateGrowth.blockBytes g).toNat=
      p.memory.byteSize+(AllocateGrowth.delta g).toNat*65536:=by
    rw[UInt32.toNat_add,headerNat,bytesNat,Nat.mod_eq_of_lt endLt]
  have align:(AllocateGrowth.header g+AllocateGrowth.blockBytes g)&&&3=0:=by
    apply UInt32.toNat_inj.mp
    simp only[UInt32.toNat_and,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    change (AllocateGrowth.header g+AllocateGrowth.blockBytes g).toNat &&&(2^2-1)=0
    rw[Nat.and_two_pow_sub_one_eq_mod,endNat]
    change (p.memory.size*65536+(AllocateGrowth.delta g).toNat*65536)%4=0
    omega
  have rootNat:(g.record+12).toNat=g.record.toNat+12:=by
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have width:=hn.width
    have hb':g.record.toNat+16≤p.memory.byteSize:=by rw[←shape.2.1];exact hb
    omega
  have head:AllocateFlagged.head (AllocateRetry.secondLayout p)=AllocateGrowth.header g:=by
    change readI32 (AllocateRetry.retryMemory g) (g.record+12).toNat=_
    rw[rootNat];exact reads.1
  refine ⟨(congrArg UInt32.toNat head).trans headerNat,?_⟩
  change (Allocate.endWord (AllocateRetry.secondLayout p).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout p))).toNat=_
  rw[head]
  change (readI32 (AllocateRetry.retryMemory g) (AllocateGrowth.header g).toNat &&&4294967292).toNat=_
  rw[reads.2.1,tagged_mask _ align]
  exact endNat

/-- Size 29 rounds to eight words, derived from the original size and rounding
condition rather than a condition on any later allocator invocation. -/
theorem retry_words29(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p)(size:p.size=29):
    (AllocateRetry.secondLayout p).words.toNat=8:=by
  have h:=DeallocateAlign.quotient570_toNat p.size hn.rounding
  change (AllocateRetry.secondLayout p).words.toNat=(p.size.toNat+3)/4 at h
  rw[size] at h
  exact h

theorem retry_next_one_word(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p)(size:p.size=29):
    Allocate.SplitNative (AllocateRetry.searchedMemory p)
      (AllocateFlagged.head (AllocateRetry.secondLayout p)) 1:=by
  apply next_one_word (AllocateRetry.secondLayout p) (AllocateRetry.native_second p hn)
    (retry_words29 p hn size)
  have interval:=retry_interval p hn
  rw[interval.1,interval.2]
  have positive:=hn.growth.pagesPositive
  omega
end WNear.Proofs.AllocationGrowthRemainder
