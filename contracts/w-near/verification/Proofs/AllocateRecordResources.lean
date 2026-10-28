import Proofs.AllocateRecordGas

/-! Whole sequential memory and canonical two-word output of689. No output/heap
separation is imposed: record writes occur after the allocation and memset. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] allocated selected after writeI32
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocated cfg s p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
  unfold allocated allocatedMemory
  apply AllocateForwardRetry.callAfter313_memory
  rw [mems_paid];exact hm
 theorem recordStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32)
    (hm : s.mems[index]?=some memory) :
    (recordStore s op index memory out pointer size).mems[index]?=some (recordMemory memory out.toNat pointer size) := by
  have a := storeI32_memory (paid s op 3) index (out.toNat+4) memory size (by rw [mems_paid];exact hm)
  unfold recordStore recordMemory
  apply storeI32_memory
  rw [mems_paid];exact a
 theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold after finalMemory
  apply recordStore_memory
  rw [selected,mems_paid]
  exact allocated_memory cfg s p hm

 theorem allocated_spec (p : Layout) (hn : Native p) :
    (allocatedMemory p).wf ∧ p.memory.byteSize≤(allocatedMemory p).byteSize ∧
    (allocatedMemory p).max=p.memory.max := by
  have h := AllocateZeroedRetry.finalMemory_spec p.toZeroed hn.allocation
  have hw : (allocatedMemory p).wf := by simpa only [allocatedMemory] using h.1
  have hs : (allocatedMemory p).byteSize=p.memory.byteSize+(AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry)).toNat*65536 := by
    simpa only [allocatedMemory] using h.2.1
  have hm : (allocatedMemory p).max=p.memory.max := by simpa only [allocatedMemory] using h.2.2.1
  exact ⟨hw,by rw [hs];omega,hm⟩
 theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=(allocatedMemory p).byteSize ∧
    (finalMemory p).max=p.memory.max ∧ readI32 (finalMemory p) p.out.toNat=result p ∧
    readI32 (finalMemory p) (p.out.toNat+4)=p.size ∧
    ∀ j, (j<p.out.toNat ∨ p.out.toNat+8≤j) → (finalMemory p).read8 j=(allocatedMemory p).read8 j := by
  have a := allocated_spec p hn
  have hb : p.out.toNat+8≤(allocatedMemory p).byteSize := by have := hn.outputBound;omega
  have h := InterfaceInstall.installMemory_spec (allocatedMemory p) p.out.toNat (result p) p.size a.1 hb
  exact ⟨h.1,h.2.1,h.2.2.1.trans a.2.2,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    fields (storeI32 s index address memory v)=fields s := rfl
private theorem fields_pack (s t : Store NearState) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    fields t=fields s := Prod.ext hf (Prod.ext hm ht)
private theorem fields313 (cfg : WasmConfig) (s : Store NearState) (p : AllocateZeroedRetry.Layout) :
    fields (AllocateForwardRetry.callAfter313 cfg s p)=fields s := by
  have h := AllocateForwardRetry.callAfter313_fields cfg s p
  exact fields_pack s (AllocateForwardRetry.callAfter313 cfg s p) h.1 h.2.1 h.2.2
 theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables := by
  have eq : fields (allocated cfg s p)=fields s := by
    rw [allocated,fields313,fields_paid]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩
 theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables := by
  have aa := allocated_fields cfg s p
  have eq : fields (after cfg s p)=fields (allocated cfg s p) := by
    rw [after,recordStore,fields_store,fields_paid,fields_store,fields_paid,selected,fields_paid]
  exact ⟨(congrArg (fun x=>x.1) eq).trans aa.1,(congrArg (fun x=>x.2.1) eq).trans aa.2.1,
    (congrArg (fun x=>x.2.2) eq).trans aa.2.2⟩
end WNear.Proofs.AllocateRecord
