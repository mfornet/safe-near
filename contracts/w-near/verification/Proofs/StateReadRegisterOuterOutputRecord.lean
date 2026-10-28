import Proofs.StateReadRegisterOuterOutput
import Proofs.StateReadRegisterOuterReadRecord
import Proofs.AllocateLayoutWrapperReadback

/-! Canonical f523 record follows from the proved sequential result with the
precise first-write/source-low separation required by the actual instructions. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64

private theorem word_of_packed_eq (first second : Memory) (out source offset : Nat)
    (ho : offset+4≤8) (heq : readI64 first out=readI64 second source) :
    readI32 first (out+offset)=readI32 second (source+offset) := by
  have bytes (i : Nat) (hi : i<4) : first.read8 (out+offset+i)=second.read8 (source+offset+i) := by
    have eq := congrArg (fun v : UInt64=>UInt8.ofNat (v.toNat >>> (8*(offset+i)))) heq
    rw [AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega),
      AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega)] at eq
    simpa only [Nat.add_assoc] using eq
  have zero : first.read8 (out+offset)=second.read8 (source+offset) := by
    simpa only [Nat.add_zero] using bytes 0 (by decide)
  simp [readI32,List.range_succ,bytes,zero]

theorem copiedMemory_record (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (hs : (scratch p).toNat+40≤(p.out523+8).toNat ∨ (p.out523+8).toNat+4≤(scratch p).toNat+32) :
    readI32 (copiedMemory p) p.out523.toNat=AllocateVector.result (actualVector p).toVector ∧
    readI32 (copiedMemory p) (p.out523.toNat+4)=p.size ∧
    readI32 (copiedMemory p) (p.out523.toNat+8)=p.size := by
  have record := read_final_record p hn ha
  have packed := copiedMemory_low_original p hn ha hs
  have lo := word_of_packed_eq (copiedMemory p) (readFinalMemory p) p.out523.toNat ((scratch p).toNat+32) 0 (by decide) packed
  have hi := word_of_packed_eq (copiedMemory p) (readFinalMemory p) p.out523.toNat ((scratch p).toNat+32) 4 (by decide) packed
  have high := (copiedMemory_spec p hn ha).2.2.2.2.1
  have address := (copy_bounds p hn).2.1
  rw [address] at high
  refine ⟨?_,?_,high.trans record.2.2.1⟩
  · simpa only [Nat.add_zero] using lo.trans record.1
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using hi.trans record.2.1
end WNear.Proofs.StateReadRegisterOuter
