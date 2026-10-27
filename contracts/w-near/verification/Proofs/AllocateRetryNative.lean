import Proofs.AllocateRetryMemory

/-! The successful growth result supplies the actual flags-two retry domain.
Every premise concerns original scalars, heap size, or successful memory growth. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
attribute [local irreducible] readI32 writeI32 writeI64 AllocateGrowth.delta AllocateGrowth.header AllocateGrowth.blockBytes AllocateGrowth.finalMemory retryMemory relinkMemory

def retryLayout (template : AllocateSearch.Layout) (p : AllocateGrowth.Layout) : AllocateSearch.Layout :=
  {template with memory:=retryMemory p,root:=p.record+12,words:=p.words}

private theorem aligned_mask (x : UInt32) (h : x&&&3=0) : x&&&4294967292=x := by
  have flags := congrArg UInt32.toBitVec h
  simp only [UInt32.toBitVec_and] at flags
  apply UInt32.toBitVec_inj.mp
  have dist := BitVec.and_or_distrib_left (x:=x.toBitVec) (y:=(4294967292:UInt32).toBitVec) (z:=(3:UInt32).toBitVec)
  simp only [show (4294967292:UInt32).toBitVec ||| (3:UInt32).toBitVec=BitVec.allOnes 32 by decide,
    BitVec.and_allOnes,flags,show (0:UInt32).toBitVec=0#32 by rfl,BitVec.or_zero] at dist
  exact dist.symm

private theorem tagged_masks (x : UInt32) (h : x&&&3=0) :
    (x|||2)&&&4294967292=x ∧ (x|||2)&&&3=2 := by
  have flags := congrArg UInt32.toBitVec h
  simp only [UInt32.toBitVec_and] at flags
  constructor
  · apply UInt32.toBitVec_inj.mp
    have mask := congrArg UInt32.toBitVec (aligned_mask x h)
    simp only [UInt32.toBitVec_and] at mask
    simp only [UInt32.toBitVec_and,UInt32.toBitVec_or,BitVec.and_or_distrib_right,mask,
      show (2:UInt32).toBitVec &&& (4294967292:UInt32).toBitVec=0#32 by decide,BitVec.or_zero]
  · apply UInt32.toBitVec_inj.mp
    simp only [UInt32.toBitVec_and,UInt32.toBitVec_or,BitVec.and_or_distrib_right,flags,
      show (2:UInt32).toBitVec &&& (3:UInt32).toBitVec=(2:UInt32).toBitVec by decide,show (0:UInt32).toBitVec=0#32 by rfl,BitVec.zero_or]

/-- Original page sizes and request room imply all native facts of the real
flags-two second search. Its end may equal the grown memory boundary. -/
theorem retry_native (template : AllocateSearch.Layout) (p : AllocateGrowth.Layout)
    (hn : AllocateGrowth.Native p)
    (hb : p.record.toNat+16≤p.memory.byteSize) (hw : p.memory.byteSize≤2^32)
    (hp : 0<p.memory.size) (hpages : p.memory.size+(AllocateGrowth.delta p).toNat<65536)
    (hwords : 0<p.words.toNat)
    (hroom : 80+p.words.toNat*4≤(AllocateGrowth.delta p).toNat*65536)
    (hvt : template.vtable.toNat+20≤p.memory.byteSize) :
    AllocateFlagged.Native (retryLayout template p) := by
  let q := retryLayout template p
  let finish := AllocateGrowth.header p+AllocateGrowth.blockBytes p
  have old : (AllocateGrowth.oldPages p).toNat=p.memory.size := by
    simp only [AllocateGrowth.oldPages]
    apply Nat.mod_eq_of_lt
    have h := hn.oldPagesBound
    omega
  have headerNat : (AllocateGrowth.header p).toNat=p.memory.size*65536 := by
    rw [AllocateGrowth.header,AllocateGrowth.pageBytes_toNat _ (by rw [old];exact hn.oldPagesBound),old]
  have bytesNat : (AllocateGrowth.blockBytes p).toNat=(AllocateGrowth.delta p).toNat*65536 := by
    simpa only [AllocateGrowth.blockBytes] using AllocateGrowth.pageBytes_toNat (AllocateGrowth.delta p) hn.pagesBound
  have finishNat : finish.toNat=(p.memory.size+(AllocateGrowth.delta p).toNat)*65536 := by
    rw [UInt32.toNat_add,headerNat,bytesNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have align : finish&&&3=0 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_and,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    change finish.toNat &&& (2^2-1)=0
    rw [Nat.and_two_pow_sub_one_eq_mod,finishNat]
    omega
  have masks := tagged_masks finish align
  have rootNat : (p.record+12).toNat=p.record.toNat+12 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    omega
  have reads := retry_reads p hn hb
  have originalShape := AllocateGrowth.finalMemory_spec p hn
  have recordBound : p.record.toNat+16≤(AllocateGrowth.finalMemory p).byteSize := by rw [originalShape.2.1];omega
  have shape := relink_spec (AllocateGrowth.finalMemory p) p.record (AllocateGrowth.header p) originalShape.1 recordBound
  have size : q.memory.byteSize=(p.memory.size+(AllocateGrowth.delta p).toNat)*65536 := by
    simp only [q,retryLayout]
    rw [retryMemory,shape.2.1,originalShape.2.1]
    change p.memory.size*65536+(AllocateGrowth.delta p).toNat*65536=_
    exact (Nat.add_mul _ _ _).symm
  have head : AllocateSearch.head q=AllocateGrowth.header p := by
    change readI32 (retryMemory p) (p.record+12).toNat=_
    rw [rootNat];exact reads.1
  have endEq : Allocate.endWord q.memory (AllocateSearch.head q)=finish := by
    rw [head]
    change readI32 (retryMemory p) (AllocateGrowth.header p).toNat &&&4294967292=finish
    rw [reads.2.1]
    exact masks.1
  change AllocateFlagged.Native q
  have wf : q.memory.wf := by simpa only [q,retryLayout,retryMemory] using shape.1
  have oldLe : p.memory.byteSize≤(p.memory.size+(AllocateGrowth.delta p).toNat)*65536 := by
    change p.memory.size*65536≤_
    rw [Nat.add_mul]
    exact Nat.le_add_right _ _
  refine ⟨wf,?_,?_,⟨hwords,?_,?_⟩,?_,?_,?_,?_⟩
  · change (p.record+12).toNat+4≤q.memory.byteSize
    rw [rootNat,size]
    apply Nat.le_trans (m:=p.memory.byteSize) _ oldLe
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hb
  · change AllocateSearch.head q≠0
    rw [head]
    intro hz
    have h:=congrArg UInt32.toNat hz
    rw [headerNat] at h
    change p.memory.size*65536=0 at h
    exact (Nat.ne_of_gt (Nat.mul_pos hp (by decide))) h
  · change (AllocateSearch.head q).toNat+80+p.words.toNat*4≤(Allocate.endWord q.memory (AllocateSearch.head q)).toNat
    rw [endEq,head,headerNat,finishNat]
    simpa only [Nat.add_assoc,Nat.add_mul] using Nat.add_le_add_left hroom (p.memory.size*65536)
  · rw [endEq,finishNat,size]
  · change (Allocate.endWord q.memory (AllocateSearch.head q)).toNat≤q.memory.byteSize
    rw [endEq,finishNat,size]
  · change readI32 q.memory (AllocateSearch.head q).toNat &&&3=2
    rw [head]
    change readI32 (retryMemory p) (AllocateGrowth.header p).toNat &&&3=2
    rw [reads.2.1];exact masks.2
  · change readI32 q.memory ((AllocateSearch.head q).toNat+8)&&&1=0
    rw [head]
    change readI32 (retryMemory p) ((AllocateGrowth.header p).toNat+8)&&&1=0
    rw [reads.2.2];rfl
  · change template.vtable.toNat+20≤q.memory.byteSize
    rw [size]
    exact hvt.trans oldLe
end WNear.Proofs.AllocateRetry
