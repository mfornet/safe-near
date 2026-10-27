import Proofs.DeallocateCoreState

/-! Original code and exact memory frames of the actual previous-free allocator path. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] DeallocateListState.after

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (hr : Code s inst p)
    (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) : Code t inst p := by
  exact ⟨by rw [hm]; exact hr.module, hr.memoryIndex, hr.index568, by rw [hf]; exact hr.function568,
    hr.index570, by rw [hf]; exact hr.function570, hr.index575, by rw [hf]; exact hr.function575,
    hr.index576, by rw [hf]; exact hr.function576⟩

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs = s.funcs := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules = s.modules := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem code_paid (s : Store NearState) (op n inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (paid s op n) inst p := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih.transport _ _ _ p rfl rfl

private theorem code_aligned (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (Deallocate.aligned s op) inst p := by
  apply hr.transport s (Deallocate.aligned s op) inst p <;> simp only [Deallocate.aligned, DeallocateAlign.after570, DeallocateAlign.bodyAfter570, DeallocateAlign.after568, DeallocateAlign.entered568, DeallocateAlign.entered570, paid_funcs, paid_modules, paid_mems, chargedStore]
private theorem code_sized (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (Deallocate.sized s op) inst p := by
  apply hr.transport s (Deallocate.sized s op) inst p <;> simp only [Deallocate.sized, DeallocateListSize.after, DeallocateListSize.entered, paid_funcs, paid_modules, paid_mems, chargedStore]
private theorem code_store (s : Store NearState) (index address inst : Nat) (memory : Memory) (value : UInt32)
    (p : Layout) (hr : Code s inst p) : Code (storeI32 s index address memory value) inst p := hr.transport _ _ inst p rfl rfl

theorem guarded_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (guarded s op) inst p := code_paid s op 6 inst p hr

theorem aligned_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (aligned s op) inst p := code_aligned (guarded s op) op inst p (guarded_code s op inst p hr)

theorem saved_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (saved s op) inst p := code_paid (aligned s op) op 3 inst p (aligned_code s op inst p hr)

theorem marked_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (marked s op p) inst p := code_store (paid (saved s op) op 9) p.memoryIndex p.header.toNat inst p.memory (readI32 p.memory p.header.toNat &&& 4294967294) p (code_paid (saved s op) op 9 inst p (saved_code s op inst p hr))

theorem sized_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (sized s op p) inst p := code_sized (marked s op p) op inst p (marked_code s op inst p hr)

theorem zeroed_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (zeroed s op p) inst p := code_store (paid (sized s op p) op 3) p.memoryIndex p.pointer.toNat inst (markedMemory p) 0 p (code_paid (sized s op p) op 3 inst p (sized_code s op inst p hr))

theorem previousSelected_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (previousSelected s op p) inst p := code_paid (zeroed s op p) op 15 inst p (zeroed_code s op inst p hr)

private theorem unlink_fields (s : Store NearState) (op : Nat) (q : DeallocateListState.Layout) :
    (DeallocateListState.after (unlinkEntered (paid s op 1) op) op q).funcs = s.funcs ∧
    (DeallocateListState.after (unlinkEntered (paid s op 1) op) op q).modules = s.modules := by
  have fields := DeallocateListState.after_fields (unlinkEntered (paid s op 1) op) op q
  have hf : (unlinkEntered (paid s op 1) op).funcs = s.funcs := by simp only [unlinkEntered, chargedStore, paid_funcs]
  have hm : (unlinkEntered (paid s op 1) op).modules = s.modules := by simp only [unlinkEntered, chargedStore, paid_modules]
  exact ⟨fields.1.trans hf, fields.2.1.trans hm⟩

theorem unlinked_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (unlinked s op p) inst p := by
  have fields := unlink_fields (previousSelected s op p) op (unlinkLayout p)
  exact (previousSelected_code s op inst p hr).transport (previousSelected s op p) (unlinked s op p) inst p fields.1 fields.2

theorem flagChecked_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (flagChecked s op p) inst p := code_paid (unlinked s op p) op 6 inst p (unlinked_code s op inst p hr)

theorem previousSized_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (previousSized s op p) inst p := code_sized (flagChecked s op p) op inst p (flagChecked_code s op inst p hr)

theorem restored_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (restored s op p) inst p := code_paid (previousSized s op p) op 3 inst p (previousSized_code s op inst p hr)

theorem after_code (s : Store NearState) (op inst : Nat) (p : Layout) (hr : Code s inst p) :
    Code (after s op p) inst p := code_store (paid (restored s op p) op 3) p.memoryIndex p.allocator.toNat inst (unlinkedMemory p) (oldHead p) p (code_paid (restored s op p) op 3 inst p (restored_code s op inst p hr))

theorem marked_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (marked s op p).mems[p.memoryIndex]? = some (markedMemory p) := by
  have initial : (paid (saved s op) op 9).mems[p.memoryIndex]? = some p.memory := by
    simpa only [saved, aligned, guarded, paid_mems, Deallocate.aligned, DeallocateAlign.after570, DeallocateAlign.bodyAfter570, DeallocateAlign.after568, DeallocateAlign.entered568, DeallocateAlign.entered570, paid_funcs, paid_modules, paid_mems, chargedStore] using hm
  exact storeI32_memory (paid (saved s op) op 9) p.memoryIndex p.header.toNat p.memory
    (readI32 p.memory p.header.toNat &&& 4294967294) initial

theorem zeroed_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (zeroed s op p).mems[p.memoryIndex]? = some (zeroMemory p) := by
  have initial : (paid (sized s op p) op 3).mems[p.memoryIndex]? = some (markedMemory p) := by
    simpa only [sized, Deallocate.sized, DeallocateListSize.after, DeallocateListSize.entered, paid_funcs, paid_modules, paid_mems, chargedStore] using marked_memory s op p hm
  exact storeI32_memory (paid (sized s op p) op 3) p.memoryIndex p.pointer.toNat (markedMemory p) 0 initial

theorem previousSelected_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (previousSelected s op p).mems[p.memoryIndex]? = some (zeroMemory p) := zeroed_memory s op p hm

theorem unlinked_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (unlinked s op p).mems[p.memoryIndex]? = some (unlinkedMemory p) := by
  have initial : (unlinkEntered (paid (previousSelected s op p) op 1) op).mems[(unlinkLayout p).memoryIndex]? =
      some (unlinkLayout p).memory := by
    simpa only [unlinkEntered, paid, chargedStore, unlinkLayout] using previousSelected_memory s op p hm
  have index : (unlinkLayout p).memoryIndex = p.memoryIndex := rfl
  simpa only [unlinked, unlinkedMemory, index] using
    DeallocateListState.after_memory (unlinkEntered (paid (previousSelected s op p) op 1) op) op (unlinkLayout p) initial

theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have initial : (paid (restored s op p) op 3).mems[p.memoryIndex]? = some (unlinkedMemory p) := by
    simpa only [restored, previousSized, flagChecked, Deallocate.sized, DeallocateListSize.after, DeallocateListSize.entered, paid_funcs, paid_modules, paid_mems, chargedStore] using unlinked_memory s op p hm
  exact storeI32_memory (paid (restored s op p) op 3) p.memoryIndex p.allocator.toNat (unlinkedMemory p) (oldHead p) initial

end WNear.Proofs.DeallocateCore
