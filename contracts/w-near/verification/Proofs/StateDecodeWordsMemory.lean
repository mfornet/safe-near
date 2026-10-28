import Proofs.StateDecodeWordsBody
import Proofs.StorePairReadback

/-! Exact packed result, sequential aliases, and byte footprint of the decoders. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI64 writeI64

theorem finalMemory_spec (wide : Bool) (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (hb : out.toNat+(widthNat wide+1)≤memory.byteSize)
    (ha : wide=true → (out+9).toNat=out.toNat+9) :
    (finalMemory wide memory out source).wf ∧
    (finalMemory wide memory out source).byteSize=memory.byteSize ∧
    (finalMemory wide memory out source).max=memory.max ∧
    ∀ j,(finalMemory wide memory out source).read8 j=
      if j=out.toNat then 0
      else if wide=true ∧ out.toNat+9≤j ∧ j<out.toNat+17 then
        UInt8.ofNat ((readI64 (lowMemory memory out source) (source+8).toNat).toNat >>> (8*(j-(out.toNat+9))))
      else if out.toNat+1≤j ∧ j<out.toNat+9 then
        UInt8.ofNat ((readI64 memory source.toNat).toNat >>> (8*(j-(out.toNat+1))))
      else memory.read8 j := by
  cases wide
  · change out.toNat+9≤memory.byteSize at hb
    have low := writeI64_spec memory (out.toNat+1) (readI64 memory source.toNat) hwf (by omega)
    change (lowMemory memory out source).wf ∧ (lowMemory memory out source).byteSize=memory.byteSize ∧
      (lowMemory memory out source).max=memory.max ∧ _ at low
    have lowRead (j : Nat) : (lowMemory memory out source).read8 j=
        if out.toNat+1≤j ∧ j<out.toNat+1+8 then
          UInt8.ofNat ((readI64 memory source.toNat).toNat >>> (8*(j-(out.toNat+1)))) else memory.read8 j := low.2.2.2 j
    have status := writeByte_spec (lowMemory memory out source) out.toNat 0 low.1 (by rw [show (lowMemory memory out source).byteSize=memory.byteSize from low.2.1];omega)
    refine ⟨status.1,status.2.1.trans low.2.1,status.2.2.1.trans low.2.2.1,?_⟩
    intro j
    change (writeByte (lowMemory memory out source) out.toNat 0).read8 j=_
    rw [status.2.2.2,lowRead]
    simp only [Nat.add_assoc,Nat.reduceAdd]
    by_cases hj:j=out.toNat
    · subst j;simp
    · have no : ¬(out.toNat≤j ∧ j<out.toNat+1) := by omega
      simp only [ite_eq_right no,hj,ite_false,Bool.false_eq_true,false_and]
  · change out.toNat+17≤memory.byteSize at hb
    have low := writeI64_spec memory (out.toNat+1) (readI64 memory source.toNat) hwf (by omega)
    change (lowMemory memory out source).wf ∧ (lowMemory memory out source).byteSize=memory.byteSize ∧
      (lowMemory memory out source).max=memory.max ∧ _ at low
    have lowRead (j : Nat) : (lowMemory memory out source).read8 j=
        if out.toNat+1≤j ∧ j<out.toNat+1+8 then
          UInt8.ofNat ((readI64 memory source.toNat).toNat >>> (8*(j-(out.toNat+1)))) else memory.read8 j := low.2.2.2 j
    have ha:=ha rfl
    have b : (out+9).toNat+8≤(lowMemory memory out source).byteSize := by rw [show (lowMemory memory out source).byteSize=memory.byteSize from low.2.1,ha];omega
    have high := writeI64_spec (lowMemory memory out source) (out+9).toNat
      (readI64 (lowMemory memory out source) (source+8).toNat) low.1 b
    change (copiedMemory true memory out source).wf ∧ (copiedMemory true memory out source).byteSize=(lowMemory memory out source).byteSize ∧
      (copiedMemory true memory out source).max=(lowMemory memory out source).max ∧ _ at high
    have highRead (j : Nat) : (copiedMemory true memory out source).read8 j=
        if (out+9).toNat≤j ∧ j<(out+9).toNat+8 then
          UInt8.ofNat ((readI64 (lowMemory memory out source) (source+8).toNat).toNat >>> (8*(j-(out+9).toNat)))
        else (lowMemory memory out source).read8 j := high.2.2.2 j
    have status := writeByte_spec (copiedMemory true memory out source) out.toNat 0 high.1
      (by rw [show (copiedMemory true memory out source).byteSize=(lowMemory memory out source).byteSize from high.2.1,low.2.1];omega)
    refine ⟨status.1,status.2.1.trans (high.2.1.trans low.2.1),status.2.2.1.trans (high.2.2.1.trans low.2.2.1),?_⟩
    intro j
    change (writeByte (copiedMemory true memory out source) out.toNat 0).read8 j=_
    rw [status.2.2.2,highRead,lowRead,ha]
    simp only [Nat.add_assoc,Nat.reduceAdd]
    by_cases hj:j=out.toNat
    · subst j;simp
    · have no : ¬(out.toNat≤j ∧ j<out.toNat+1) := by omega
      simp only [ite_eq_right no,hj,ite_false,true_and]

theorem finalMemory_status (wide : Bool) (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (hb : out.toNat+(widthNat wide+1)≤memory.byteSize)
    (ha : wide=true → (out+9).toNat=out.toNat+9) :
    (finalMemory wide memory out source).read8 out.toNat=0 := by
  rw [(finalMemory_spec wide memory out source hwf hb ha).2.2.2]
  simp

theorem finalMemory_low (wide : Bool) (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (hb : out.toNat+(widthNat wide+1)≤memory.byteSize)
    (ha : wide=true → (out+9).toNat=out.toNat+9) :
    readI64 (finalMemory wide memory out source) (out.toNat+1)=readI64 memory source.toNat := by
  have spec := finalMemory_spec wide memory out source hwf hb ha
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [spec.2.2.2]
  have ne : out.toNat+1+i≠out.toNat := by omega
  have no : ¬(wide=true ∧ out.toNat+9≤out.toNat+1+i ∧ out.toNat+1+i<out.toNat+17) := by omega
  have yes : out.toNat+1≤out.toNat+1+i ∧ out.toNat+1+i<out.toNat+9 := by omega
  simp only [ne,ite_false,ite_eq_right no,yes,true_and,ite_true,Nat.add_sub_cancel_left]

theorem finalMemory_high (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (hb : out.toNat+17≤memory.byteSize) (ha : (out+9).toNat=out.toNat+9) :
    readI64 (finalMemory true memory out source) (out.toNat+9)=readI64 (lowMemory memory out source) (source+8).toNat := by
  have spec := finalMemory_spec true memory out source hwf hb (fun _=>ha)
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [spec.2.2.2]
  have ne : out.toNat+9+i≠out.toNat := by omega
  have yes : true=true ∧ out.toNat+9≤out.toNat+9+i ∧ out.toNat+9+i<out.toNat+17 := ⟨rfl,by omega,by omega⟩
  simp only [ne,ite_false,yes,true_and,ite_true,Nat.add_sub_cancel_left]

theorem finalMemory_outside (wide : Bool) (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (hb : out.toNat+(widthNat wide+1)≤memory.byteSize)
    (ha : wide=true → (out+9).toNat=out.toNat+9) (j : Nat)
    (hj : j<out.toNat ∨out.toNat+(widthNat wide+1)≤j) :
    (finalMemory wide memory out source).read8 j=memory.read8 j := by
  rw [(finalMemory_spec wide memory out source hwf hb ha).2.2.2]
  cases wide <;> simp only [widthNat,ite_true,ite_false,Bool.false_eq_true,true_and,false_and] at hj ⊢ <;>
    split_ifs <;> first | rfl | omega
end WNear.Proofs.StateDecodeWords
