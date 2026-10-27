import Proofs.AllocateSearchCall
import Proofs.AllocateSearchMemory

/-! Exact sequential memory and code/global frames of the complete f580 call. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 minimumDone initialized linked splitAfter candidateAfter searched searchAfter callAfter
  controlAfter Allocate.committed Allocate.initializedStore Allocate.copiedEndStore Allocate.clearedStore

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem minimum_mems (s : Store NearState) (op : Nat) : (minimumDone s op).mems=s.mems := by
  exact congrArg (fun t=>t.mems) (minimumDone_resources s op)

private theorem candidate_mems (s : Store NearState) (op : Nat) : (candidateAfter s op).mems=s.mems := by
  exact congrArg (fun t=>t.mems) (candidateAfter_resources s op)

theorem initialized_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (initialized s op p).mems[p.memoryIndex]?=some (initializedMemory p) := by
  have clear := Allocate.clearedStore_memory (minimumDone s op) op p.memoryIndex p.memory (header p)
    (by rw [minimum_mems];exact hm)
  unfold initialized Allocate.initializedStore Allocate.copiedEndStore
  apply storeI32_memory
  rw [mems_paid]
  exact clear

theorem splitAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (splitAfter s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  have control := controlAfter_memory (initialized s op p) op p (initialized_memory s op p hm)
  have linkedMem : (linked s op p).mems[p.memoryIndex]?=some (linkedMemory p) := by
    simpa only [linked] using control
  unfold splitAfter
  exact Allocate.committed_memory (linked s op p) op p.memoryIndex (linkedMemory p) (header p) linkedMem

theorem searchAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (searchAfter s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold searchAfter searched
  rw [mems_paid]
  apply splitAfter_memory
  rw [candidate_mems,mems_paid,initialAfter,mems_paid]
  exact hm

theorem callAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact searchAfter_memory (entered s op) op p hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_store32 (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    fields (storeI32 s index address memory v)=fields s := rfl
private theorem fields_store64 (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt64) :
    fields (storeI64 s index address memory v)=fields s := rfl
private theorem fields_minimum (s : Store NearState) (op : Nat) : fields (minimumDone s op)=fields s := by
  have h := congrArg fields (minimumDone_resources s op)
  simp only [fields] at h ⊢
  exact h
private theorem fields_candidate (s : Store NearState) (op : Nat) : fields (candidateAfter s op)=fields s := by
  have h := congrArg fields (candidateAfter_resources s op)
  simp only [fields] at h ⊢
  exact h
private theorem fields_initialized (s : Store NearState) (op : Nat) (p : Layout) : fields (initialized s op p)=fields s := by
  simp only [initialized,Allocate.initializedStore,Allocate.copiedEndStore,Allocate.clearedStore,
    fields_store32,fields_store64,fields_paid,fields_minimum]
private theorem fields_control (s : Store NearState) (op : Nat) (p : Layout) : fields (controlAfter s op p)=fields s := by
  have h := controlAfter_fields s op p
  simp only [fields]
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))
private theorem fields_commit (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    fields (Allocate.committed s op index memory header)=fields s := by
  have h := congrArg fields (Allocate.committed_resources s op index memory header)
  simp only [fields] at h ⊢
  exact h
private theorem fields_split (s : Store NearState) (op : Nat) (p : Layout) : fields (splitAfter s op p)=fields s := by
  simp only [splitAfter,fields_commit,linked,fields_control,fields_initialized]
private theorem fields_search (s : Store NearState) (op : Nat) (p : Layout) : fields (searchAfter s op p)=fields s := by
  simp only [searchAfter,searched,fields_paid,fields_split,fields_candidate,initialAfter]

theorem callAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter s op p).funcs=s.funcs ∧ (callAfter s op p).modules=s.modules ∧
    (callAfter s op p).tables=s.tables ∧ (callAfter s op p).globals=s.globals := by
  have h : fields (callAfter s op p)=fields s := by
    rw [callAfter,fields_search]
    rfl
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,
    congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

end WNear.Proofs.AllocateSearch
