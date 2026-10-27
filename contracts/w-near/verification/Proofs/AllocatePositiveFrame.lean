import Proofs.AllocatePositiveState
import Proofs.AllocateSearchCallFrame

/-! Exact native memory and code/global frames of f581's positive fitting path. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] reserved prefixed searched found updated after readI32 writeI32 Allocate.prefixAfter Allocate.roundedStore AllocateSearch.callAfter

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem prefix_memory (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory)
    (hm : s.mems[index]?=some memory) :
    (Allocate.prefixAfter s op index scratch allocator memory).mems[index]?=
      some (writeI32 memory (scratch.toNat+12) (readI32 memory allocator.toNat)) := by
  have h := congrArg (fun t=>t.mems) (Allocate.roundedStore_resources s op)
  simp only at h
  unfold Allocate.prefixAfter Allocate.savedHead
  apply storeI32_memory
  rw [mems_paid,h]
  exact hm

 theorem prefixed_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (prefixed s op p).mems[p.memoryIndex]?=some (savedMemory p) := by
  unfold prefixed
  apply prefix_memory
  rw [mems_paid,reserved]
  simpa only [setGlobal,mems_paid] using hm

 theorem searched_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (searched s op p).mems[p.memoryIndex]?=some (searchedMemory p) := by
  unfold searched
  apply AllocateSearch.callAfter_memory
  rw [mems_paid]
  exact prefixed_memory s op p hm

 theorem found_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (found s op p).mems[p.memoryIndex]?=some (searchedMemory p) := by
  rw [found,mems_paid]
  exact searched_memory s op p hm

 theorem updated_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (updated s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold updated finalMemory
  apply storeI32_memory
  rw [mems_paid]
  exact found_memory s op p hm

 theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  rw [after,mems_paid,mems_global,mems_paid]
  exact updated_memory s op p hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s := rfl
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
private theorem fields_mask (s t : Store NearState) (h : {t with host:=s.host}=s) : fields t=fields s := by
  have z := congrArg fields h
  simpa only [fields] using z
private theorem fields_pack (s t : Store NearState) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    fields t=fields s := Prod.ext hf (Prod.ext hm ht)
private theorem prefix_fields (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :
    fields (Allocate.prefixAfter s op index scratch allocator memory)=fields s := by
  have h := fields_mask s (Allocate.roundedStore s op) (Allocate.roundedStore_resources s op)
  simp only [Allocate.prefixAfter,Allocate.savedHead,fields_store,fields_paid]
  exact h
private theorem search_fields (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) :
    fields (AllocateSearch.callAfter s op p)=fields s := by
  have h := AllocateSearch.callAfter_fields s op p
  exact fields_pack s (AllocateSearch.callAfter s op p) h.1 h.2.1 h.2.2.1
private theorem fields_reserved (s : Store NearState) (op : Nat) (p : Layout) : fields (reserved s op p)=fields s := by
  rw [reserved,fields_global,fields_paid]
private theorem fields_prefixed (s : Store NearState) (op : Nat) (p : Layout) : fields (prefixed s op p)=fields s := by
  rw [prefixed,prefix_fields,fields_paid,fields_reserved]
private theorem fields_searched (s : Store NearState) (op : Nat) (p : Layout) : fields (searched s op p)=fields s := by
  rw [searched,search_fields,fields_paid,fields_prefixed]
private theorem fields_found (s : Store NearState) (op : Nat) (p : Layout) : fields (found s op p)=fields s := by
  rw [found,fields_paid,fields_searched]
private theorem fields_updated (s : Store NearState) (op : Nat) (p : Layout) : fields (updated s op p)=fields s := by
  rw [updated,fields_store,fields_paid,fields_found]

 theorem reserved_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (reserved s op p).funcs=s.funcs ∧ (reserved s op p).modules=s.modules ∧ (reserved s op p).tables=s.tables :=
  fields_project s _ (fields_reserved s op p)
 theorem prefixed_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (prefixed s op p).funcs=s.funcs ∧ (prefixed s op p).modules=s.modules ∧ (prefixed s op p).tables=s.tables :=
  fields_project s _ (fields_prefixed s op p)
 theorem searched_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (searched s op p).funcs=s.funcs ∧ (searched s op p).modules=s.modules ∧ (searched s op p).tables=s.tables :=
  fields_project s _ (fields_searched s op p)
 theorem found_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (found s op p).funcs=s.funcs ∧ (found s op p).modules=s.modules ∧ (found s op p).tables=s.tables :=
  fields_project s _ (fields_found s op p)
 theorem updated_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (updated s op p).funcs=s.funcs ∧ (updated s op p).modules=s.modules ∧ (updated s op p).tables=s.tables :=
  fields_project s _ (fields_updated s op p)
 theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs=s.funcs ∧ (after s op p).modules=s.modules ∧ (after s op p).tables=s.tables := by
  apply fields_project
  rw [after,fields_paid,fields_global,fields_paid,fields_updated]

private theorem prefix_globals (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :
    (Allocate.prefixAfter s op index scratch allocator memory).globals=s.globals := by
  have h := congrArg (fun t=>t.globals) (Allocate.roundedStore_resources s op)
  simp only at h
  simp only [Allocate.prefixAfter,Allocate.savedHead,storeI32_globals,globals_paid]
  exact h

 theorem prefixed_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (prefixed s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  simp only [prefixed,prefix_globals,globals_paid,reserved,setGlobal]
 theorem searched_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (searched s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [searched,(AllocateSearch.callAfter_fields _ op _).2.2.2,globals_paid,prefixed_globals]
 theorem found_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (found s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [found,globals_paid,searched_globals]
 theorem updated_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (updated s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [updated,storeI32_globals,globals_paid,found_globals]
 theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after s op p).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  rw [after,globals_paid]
  simp only [setGlobal,globals_paid]
  rw [updated_globals]
  simpa only [setGlobal,hv] using restore

end WNear.Proofs.AllocatePositive
