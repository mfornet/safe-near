import Proofs.ZeroFillLoop

/-! Exact installed memory and byte semantics of the deployed fill loop. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] iterationStore written writeByte

def filledMemory (memory : Memory) (ptr value : UInt32) : Nat → Memory
  | 0 => memory
  | n+1 => filledMemory (writeByte memory ptr.toNat value) (ptr+1) value n

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem iteration_memory (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32)
    (hm : s.mems[index]?=some memory) :
    (iterationStore s op index memory ptr value).mems[index]?=some (writeByte memory ptr.toNat value) := by
  unfold iterationStore written
  rw [mems_paid]
  apply storeByte_memory
  rw [mems_paid]
  exact hm

theorem loopAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory)
    (ptr value count : UInt32) (n : Nat) (hm : s.mems[index]?=some memory) :
    (loopAfter s op index memory ptr value count n).mems[index]?=some (filledMemory memory ptr value n) := by
  induction n generalizing s memory ptr count with
  | zero => exact hm
  | succ n ih =>
    exact ih _ (writeByte memory ptr.toNat value) (ptr+1) (nextCount count) (iteration_memory s op index memory ptr value hm)

private theorem byte_read (memory : Memory) (address : Nat) (value : UInt32)
    (hw : memory.wf) (hb : address+1≤memory.byteSize) (j : Nat) :
    (writeByte memory address value).read8 j=if j=address then UInt8.ofNat value.toNat else memory.read8 j := by
  rw [(writeByte_spec memory address value hw hb).2.2.2 j]
  by_cases h : j=address
  · subst j;simp
  · rw [ite_eq_right (show ¬(address≤j ∧ j<address+1) by omega),ite_eq_right h]

/-- The exact fill interval, including a possible final pointer wrap after the last store. -/
theorem filledMemory_spec (memory : Memory) (ptr value : UInt32) (n : Nat)
    (hw : memory.wf) (hb : ptr.toNat+n≤memory.byteSize) (hwidth : ptr.toNat+n≤2^32) :
    (filledMemory memory ptr value n).wf ∧
    (filledMemory memory ptr value n).byteSize=memory.byteSize ∧
    (filledMemory memory ptr value n).max=memory.max ∧
    ∀ j, (filledMemory memory ptr value n).read8 j=
      if ptr.toNat≤j ∧ j<ptr.toNat+n then UInt8.ofNat value.toNat else memory.read8 j := by
  induction n generalizing memory ptr with
  | zero =>
    refine ⟨hw,rfl,rfl,?_⟩
    intro j
    simp only [filledMemory,Nat.add_zero,ite_eq_right (show ¬(ptr.toNat≤j ∧ j<ptr.toNat) by omega)]
  | succ n ih =>
    have byteBound : ptr.toNat+1≤memory.byteSize := by omega
    have first := writeByte_spec memory ptr.toNat value hw byteBound
    cases n with
    | zero =>
      refine ⟨first.1,first.2.1,first.2.2.1,?_⟩
      intro j
      rw [show filledMemory memory ptr value (0+1)=writeByte memory ptr.toNat value from rfl,byte_read memory ptr.toNat value hw byteBound]
      congr 1
      apply propext
      omega
    | succ n =>
      have next : (ptr+1).toNat=ptr.toNat+1 := by
        simp only [UInt32.toNat_add,UInt32.toNat_ofNat,Nat.reducePow]
        omega
      have span : (ptr+1).toNat+(n+1)≤(writeByte memory ptr.toNat value).byteSize := by rw [next,first.2.1];omega
      have width : (ptr+1).toNat+(n+1)≤2^32 := by rw [next];omega
      have tail := ih (writeByte memory ptr.toNat value) (ptr+1) first.1 span width
      refine ⟨tail.1,tail.2.1.trans first.2.1,tail.2.2.1.trans first.2.2.1,?_⟩
      intro j
      rw [show filledMemory memory ptr value (n+1+1)=filledMemory (writeByte memory ptr.toNat value) (ptr+1) value (n+1) from rfl,
        tail.2.2.2 j,byte_read memory ptr.toNat value hw byteBound,next]
      split <;> split <;> (try split) <;> first | rfl | omega

end WNear.Proofs.ZeroFill
