import Proofs.AllocateFlaggedMemory

/-! The actual flags-two split leaves an ordinary free-list remainder: its old
head points to the new allocated header with flags cleared. -/
namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.AllocateFlagged
open WNear.Proofs.AllocateSearch (Layout)
attribute [local irreducible] readI32 writeI32

private theorem aligned_clear_two(value:UInt32)(h:value &&&3=0):
    ((value|||2)&&&4294967293)=value:=by
  have hz:value &&&2=0:=by
    calc
      value &&&2=(value &&&3)&&&2:=by rw[UInt32.and_assoc];rfl
      _=0:=by rw[h];rfl
  have zero:=congrArg UInt32.toBitVec hz
  simp only[UInt32.toBitVec_and] at zero
  change value.toBitVec &&& (2:BitVec 32)=0 at zero
  apply UInt32.toBitVec_inj.mp
  simp only[UInt32.toBitVec_and,UInt32.toBitVec_or]
  change ((value.toBitVec ||| (2:BitVec 32)) &&& (4294967293:BitVec 32))=value.toBitVec
  have full:(2:BitVec 32)|||4294967293=BitVec.allOnes 32:=rfl
  have part:=BitVec.and_or_distrib_left (x:=value.toBitVec) (y:=2) (z:=4294967293)
  rw[full,BitVec.and_allOnes,zero] at part
  change value.toBitVec=(0:BitVec 32)|||(value.toBitVec &&& (4294967293:BitVec 32)) at part
  rw[show (0:BitVec 32)=0#32 by rfl,BitVec.zero_or] at part
  rw[BitVec.and_or_distrib_right,←part]
  rw[show (2:BitVec 32) &&&4294967293=0#32 by rfl,BitVec.or_zero]

private theorem frame(p:Layout)(m:Memory)(shape:Shape p m)(address target:Nat)(value:UInt32)
    (hb:address+4≤p.memory.byteSize)(hs:target+4≤address ∨address+4≤target):
    readI32 (writeI32 m address value) target=readI32 m target:=
  PanicAllocateReadback.read_write_frame m target address value shape.wf (by rw[shape.size];exact hb) hs

/-- Real final free-head word, including the actual flag-transfer clear. -/
theorem final_head(p:Layout)(hn:Native p):
    readI32 (AllocateFlagged.finalMemory p) (head p).toNat=AllocateFlagged.header p:=by
  have b:=intervals p hn
  have shape:=linked_shape p hn
  have self:=PanicAllocateReadback.read_write_self (linkedMemory p) (head p).toNat (linkedWord p &&&4294967293) shape.wf (by rw[shape.size];omega)
  have flagged:=frame p (clearedFlagMemory p) (clearedFlag_shape p hn) (AllocateFlagged.header p).toNat (head p).toNat
    (readI32 (clearedFlagMemory p) (AllocateFlagged.header p).toNat|||2) (by omega) (Or.inl (by omega))
  have mark:=frame p (flaggedMemory p) (flagged_shape p hn) (AllocateFlagged.header p).toNat (head p).toNat
    (readI32 (flaggedMemory p) (AllocateFlagged.header p).toNat|||1) (by omega) (Or.inl (by omega))
  have value:linkedWord p &&&4294967293=AllocateFlagged.header p:=by
    rw[linked_word p hn]
    exact aligned_clear_two (AllocateFlagged.header p) (header_aligned p hn)
  exact mark.trans (flagged.trans (self.trans value))

/-- The remainder's next-candidate word has its in-use bit cleared. -/
theorem final_candidate(p:Layout)(hn:Native p):
    readI32 (AllocateFlagged.finalMemory p) ((head p).toNat+8)=
      readI32 p.memory ((head p).toNat+8) &&&4294967294:=by
  have b:=intervals p hn
  have self:=PanicAllocateReadback.read_write_self (previousMemory p) ((head p).toNat+8)
    (readI32 (previousMemory p) ((head p).toNat+8)&&&4294967294) (previous_shape p hn).wf
    (by rw[(previous_shape p hn).size];omega)
  have link:=frame p (unflaggedMemory p) (unflagged_shape p hn) (head p).toNat ((head p).toNat+8) (linkedWord p) (by omega) (Or.inr (by omega))
  have clear:=frame p (linkedMemory p) (linked_shape p hn) (head p).toNat ((head p).toNat+8) (linkedWord p &&&4294967293) (by omega) (Or.inr (by omega))
  have flag:=frame p (clearedFlagMemory p) (clearedFlag_shape p hn) (AllocateFlagged.header p).toNat ((head p).toNat+8)
    (readI32 (clearedFlagMemory p) (AllocateFlagged.header p).toNat|||2) (by omega) (Or.inl (by omega))
  have mark:=frame p (flaggedMemory p) (flagged_shape p hn) (AllocateFlagged.header p).toNat ((head p).toNat+8)
    (readI32 (flaggedMemory p) (AllocateFlagged.header p).toNat|||1) (by omega) (Or.inl (by omega))
  have original:=previous_candidate p hn
  have value:(readI32 (previousMemory p) ((head p).toNat+8)&&&4294967294)=
      readI32 p.memory ((head p).toNat+8)&&&4294967294:=congrArg (fun x:UInt32=>x&&&4294967294) original
  exact mark.trans (flag.trans (clear.trans (link.trans (self.trans value))))

theorem final_head_flags(p:Layout)(hn:Native p):
    readI32 (AllocateFlagged.finalMemory p) (head p).toNat &&&3=0:=by
  rw[final_head p hn];exact header_aligned p hn

theorem final_candidate_flag(p:Layout)(hn:Native p):
    readI32 (AllocateFlagged.finalMemory p) ((head p).toNat+8) &&&1=0:=by
  rw[final_candidate p hn,UInt32.and_assoc]
  rw[show (4294967294:UInt32) &&& 1=0 by rfl,UInt32.and_zero]

theorem final_end(p:Layout)(hn:Native p):
    Allocate.endWord (AllocateFlagged.finalMemory p) (head p)=AllocateFlagged.header p:=by
  unfold Allocate.endWord
  rw[final_head p hn]
  have aligned:=header_aligned p hn
  have v:AllocateFlagged.header p &&&4294967292=AllocateFlagged.header p:=by
    apply UInt32.toBitVec_inj.mp
    have h:=congrArg UInt32.toBitVec aligned
    simp only[UInt32.toBitVec_and] at h
    change (AllocateFlagged.header p).toBitVec &&& (3:BitVec 32)=0 at h
    change (AllocateFlagged.header p).toBitVec &&& (4294967292:BitVec 32)=(AllocateFlagged.header p).toBitVec
    have full:(3:BitVec 32)|||4294967292=BitVec.allOnes 32:=rfl
    have part:=BitVec.and_or_distrib_left (x:=(AllocateFlagged.header p).toBitVec) (y:=3) (z:=4294967292)
    rw[full,BitVec.and_allOnes,h] at part
    change (AllocateFlagged.header p).toBitVec=(0:BitVec 32)|||((AllocateFlagged.header p).toBitVec &&& (4294967292:BitVec 32)) at part
    rw[show (0:BitVec 32)=0#32 by rfl,BitVec.zero_or] at part
    exact part.symm
  exact v
end WNear.Proofs.AllocationGrowthRemainder
