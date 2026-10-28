import Proofs.AllocateRecordCopyState
import Proofs.AllocateRecordResources

/-! Exact copied memory and code frames for the real690 sequential copy. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 allocated copyDone after AllocateRecord.after

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory) :
    (allocated cfg s p).mems[p.inner.memoryIndex]?=some (allocatedMemory p) := by
  unfold allocated allocatedMemory
  apply AllocateRecord.after_memory
  simpa only [recordEntered,arguments,reserved,chargedStore,setGlobal,mems_paid] using hm

theorem copied_memory (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory)
    (hm : s.mems[index]?=some memory) :
    (copied s op index out source memory).mems[index]?=some (finalMemory memory out source) := by
  have first : (copyWord s op index 0 8 out source memory).mems[index]?=some (firstMemory memory out source) := by
    unfold copyWord firstMemory
    apply storeI32_memory
    rw [mems_paid];exact hm
  unfold copied copyWord
  apply storeI32_memory
  rw [mems_paid]
  exact first

theorem copyDone_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory) :
    (copyDone cfg s p).mems[p.inner.memoryIndex]?=some (resultMemory p) := by
  unfold copyDone resultMemory
  exact copied_memory (allocated cfg s p) cfg.regularOpCost p.inner.memoryIndex p.out p.inner.sp (allocatedMemory p) (allocated_memory cfg s p hm)

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory) :
    (after cfg s p).mems[p.inner.memoryIndex]?=some (resultMemory p) := by
  rw [after,mems_global,mems_paid]
  exact copyDone_memory cfg s p hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_global (s : Store NearState) (index : Nat) (value : Value) : fields (setGlobal s index value)=fields s := rfl
private theorem fields_charge (s : Store NearState) (cost : Nat) : fields (chargedStore s cost)=fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) : fields (storeI32 s index address memory value)=fields s := rfl
private theorem fields_project {s t : Store NearState} (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
private theorem fields_record (cfg : WasmConfig) (s : Store NearState) (p : AllocateRecord.Layout) : fields (AllocateRecord.after cfg s p)=fields s := by
  have h := AllocateRecord.after_fields cfg s p
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (allocated cfg s p)=fields s := by
  rw [allocated,fields_record,recordEntered,fields_charge,fields_charge,arguments,fields_paid,reserved,fields_global,fields_paid]

theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs=s.funcs ∧ (arguments s op p).modules=s.modules ∧ (arguments s op p).tables=s.tables := by
  apply fields_project
  rw [arguments,fields_paid,reserved,fields_global,fields_paid]
theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables :=
  fields_project (fields_allocated cfg s p)
theorem copyDone_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (copyDone cfg s p).funcs=s.funcs ∧ (copyDone cfg s p).modules=s.modules ∧ (copyDone cfg s p).tables=s.tables := by
  apply fields_project
  rw [copyDone,copied,copyWord,fields_store,fields_paid,copyWord,fields_store,fields_paid,fields_allocated]
theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables := by
  have h := copyDone_fields cfg s p
  have eq : fields (after cfg s p)=fields (copyDone cfg s p) := by rw [after,fields_global,fields_paid]
  exact fields_project (eq.trans (Prod.ext h.1 (Prod.ext h.2.1 h.2.2)))

theorem allocated_spec (p : Layout) (hn : Native p) :
    (allocatedMemory p).wf ∧ p.inner.memory.byteSize≤(allocatedMemory p).byteSize ∧ (allocatedMemory p).max=p.inner.memory.max := by
  have h := AllocateRecord.finalMemory_spec p.inner hn.inner
  have before := AllocateRecord.allocated_spec p.inner hn.inner
  exact ⟨h.1,by change p.inner.memory.byteSize≤(AllocateRecord.finalMemory p.inner).byteSize;rw [h.2.1];exact before.2.1,h.2.2.1⟩

theorem resultMemory_spec (p : Layout) (hn : Native p) :
    (resultMemory p).wf ∧ (resultMemory p).byteSize=(allocatedMemory p).byteSize ∧ (resultMemory p).max=p.inner.memory.max := by
  have shape := allocated_spec p hn
  have result := finalMemory_shape (allocatedMemory p) p.out p.inner.sp shape.1 (hn.outputBound.trans shape.2.1)
  exact ⟨result.1,result.2.1,result.2.2.trans shape.2.2⟩
end WNear.Proofs.AllocateRecordCopy
