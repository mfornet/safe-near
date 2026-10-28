import Proofs.AllocateSearchMemory
import NearVM.MeteredByteMemoryRules

/-! Exact allocated-header and successor-backlink words of the actual direct
split. Every read uses the real sequential memory, with no outcome premise. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

private theorem frame(p:Layout)(m:Memory)(shape:Shape p m)(address target:Nat)(value:UInt32)
    (hb:address+4≤p.memory.byteSize)(hs:target+4≤address ∨address+4≤target):
    readI32 (writeI32 m address value) target=readI32 m target:=
  PanicAllocateReadback.read_write_frame m target address value shape.wf (by rw[shape.size];exact hb) hs

 theorem final_allocated_header(p:Layout)(hn:Native p):
    readI32 (finalMemory p) (header p).toNat=finish p|||1:=by
  have b:=intervals p hn
  have shape:=linked_shape p hn
  have self:=PanicAllocateReadback.read_write_self (linkedMemory p) (header p).toNat
    (readI32 (linkedMemory p) (header p).toNat|||1) shape.wf (by rw[shape.size];omega)
  unfold finalMemory Allocate.markedMemory
  exact self.trans (congrArg (fun x:UInt32=>x|||1) (linked_reads p hn).2)

 theorem final_allocated_flag(p:Layout)(hn:Native p):
    readI32 (finalMemory p) (header p).toNat&&&1=1:=by
  rw[final_allocated_header p hn]
  apply UInt32.toBitVec_inj.mp
  simp only[UInt32.toBitVec_and,UInt32.toBitVec_or,BitVec.and_or_distrib_right,
    show (1:UInt32).toBitVec &&& (1:UInt32).toBitVec=(1:UInt32).toBitVec by rfl]
  have align:finish p &&&1=0:=by
    change (readI32 p.memory (head p).toNat&&&4294967292)&&&1=0
    rw[UInt32.and_assoc,show (4294967292:UInt32)&&&1=0 by rfl,UInt32.and_zero]
  have zero:=congrArg UInt32.toBitVec align
  simp only[UInt32.toBitVec_and] at zero
  rw[zero,show (0:UInt32).toBitVec=0#32 by rfl,BitVec.zero_or]

 theorem final_successor_backlink(p:Layout)(hn:Native p):
    readI32 (finalMemory p) ((finish p).toNat+4)=
      Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p):=by
  have b:=intervals p hn
  have self:=PanicAllocateReadback.read_write_self (initializedMemory p) ((finish p).toNat+4)
    (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p))
    (initialized_shape p hn).wf (by rw[(initialized_shape p hn).size];omega)
  have previous:=frame p (backlinkedMemory p) (backlinked_shape p hn) ((header p).toNat+4) ((finish p).toNat+4)
    (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega) (Or.inr (by omega))
  have unflagged:=frame p (previousMemory p) (previous_shape p hn) ((head p).toNat+8) ((finish p).toNat+4)
    (readI32 (previousMemory p) ((head p).toNat+8)&&&4294967294) (by omega) (Or.inr (by omega))
  have linked:=frame p (unflaggedMemory p) (unflagged_shape p hn) (head p).toNat ((finish p).toNat+4)
    (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)) (by omega) (Or.inr (by omega))
  have marked:=frame p (linkedMemory p) (linked_shape p hn) (header p).toNat ((finish p).toNat+4)
    (readI32 (linkedMemory p) (header p).toNat|||1) (by omega) (Or.inr (by omega))
  exact marked.trans (linked.trans (unflagged.trans (previous.trans self)))

private theorem masked_tag(raw value:UInt32)(aligned:value&&&3=0):
    ((raw&&&3)|||value)&&&4294967292=value:=by
  apply UInt32.toBitVec_inj.mp
  have flags:=congrArg UInt32.toBitVec aligned
  simp only[UInt32.toBitVec_and] at flags
  have part:=BitVec.and_or_distrib_left (x:=value.toBitVec) (y:=(4294967292:UInt32).toBitVec) (z:=(3:UInt32).toBitVec)
  simp only[show (4294967292:UInt32).toBitVec||| (3:UInt32).toBitVec=BitVec.allOnes 32 by rfl,
    BitVec.and_allOnes,flags,show (0:UInt32).toBitVec=0#32 by rfl,BitVec.or_zero] at part
  simp only[UInt32.toBitVec_and,UInt32.toBitVec_or,BitVec.and_or_distrib_right,BitVec.and_assoc,
    show (3:UInt32).toBitVec &&& (4294967292:UInt32).toBitVec=0#32 by rfl,BitVec.and_zero,BitVec.zero_or]
  exact part.symm

 theorem final_successor_previous(p:Layout)(hn:Native p):
    readI32 (finalMemory p) ((finish p).toNat+4)&&&4294967292=header p:=by
  rw[final_successor_backlink p hn]
  unfold Allocate.taggedValue
  exact masked_tag _ _ (header_aligned p hn)

 theorem final_allocated_byte_flag(p:Layout)(hn:Native p):
    readByteWord (finalMemory p) (header p).toNat&&&1=1:=by
  have b:=intervals p hn
  have shape:=linked_shape p hn
  have write:=writeI32_spec (linkedMemory p) (header p).toNat
    (readI32 (linkedMemory p) (header p).toNat|||1) shape.wf (by rw[shape.size];omega)
  have word:(finish p|||1).toNat%2=1:=by
    have h:=congrArg UInt32.toNat (final_allocated_flag p hn)
    rw[final_allocated_header p hn] at h
    simp only[UInt32.toNat_and,UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod,Nat.and_one_is_mod] at h
    exact h
  rw[readByteWord_eq]
  unfold finalMemory Allocate.markedMemory
  rw[write.2.2.2,ite_eq_left (show (header p).toNat≤(header p).toNat ∧(header p).toNat<(header p).toNat+4 by omega),
    (linked_reads p hn).2]
  simp only[Nat.sub_self,Nat.mul_zero,Nat.shiftRight_zero]
  apply UInt32.toNat_inj.mp
  simp only[UInt32.toNat_and,UInt32.toNat_ofNat,UInt32.toNat_ofNat',UInt8.toNat_ofNat',Nat.reducePow,Nat.reduceMod,Nat.and_one_is_mod]
  omega
end WNear.Proofs.AllocateSearch
