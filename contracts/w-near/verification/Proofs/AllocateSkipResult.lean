import Proofs.AllocateSkipCall
import Proofs.AllocateSearchCallFrame

/-! Exact installed postmemory and code/global frames of the actual one-hop search. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid)
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] after callAfter resumed hopped advanced candidateAfter AllocateSearch.searched
  AllocateSearch.splitAfter AllocateSearch.initialized AllocateSearch.minimumDone AllocateSearch.linked
  AllocateSearch.controlAfter Allocate.committed readI32 writeI32

def resultMemory (p : Layout) := AllocateSearch.finalMemory (nextLayout p)
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem searched_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (AllocateSearch.searched s op p).mems[p.memoryIndex]?=some (AllocateSearch.finalMemory p) := by
  unfold AllocateSearch.searched
  apply splitAfter_memory
  rw [candidate_mems]
  exact hm
 theorem after_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after s op p).mems[p.memoryIndex]?=some (resultMemory p) := by
  rw [after,mems_paid]
  apply searched_memory
  apply resumed_memory
  simpa only [before,initialAfter,paid,chargedStore] using hm
 theorem callAfter_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter s op p).mems[p.memoryIndex]?=some (resultMemory p) := by
  unfold callAfter
  exact after_memory (entered s op) op p hm
 theorem resultMemory_spec (p : Layout) (hn : Native p) :
    (resultMemory p).wf ∧ (resultMemory p).byteSize=p.memory.byteSize ∧ (resultMemory p).max=p.memory.max := by
  have next := nextMemory_spec p hn
  have h := AllocateSearch.final_shape (nextLayout p) (native_next p hn)
  exact ⟨h.wf,h.size.trans next.2.1,h.max.trans next.2.2⟩
 theorem result_nonzero_and_span (p : Layout) (hn : Native p) :
    pointer (nextLayout p)≠0 ∧ (pointer (nextLayout p)).toNat+p.words.toNat*4≤(resultMemory p).byteSize := by
  have nextNative := native_next p hn
  have h := Allocate.split_result (nextLayout p).memory (head (nextLayout p)) p.words nextNative.split
  exact ⟨h.2.1,h.2.2.1.trans_eq (AllocateSearch.final_shape (nextLayout p) nextNative).size.symm⟩

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

private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n)=fields s := rfl
private theorem fields_searched (s : Store NearState) (op : Nat) (p : Layout) : fields (AllocateSearch.searched s op p)=fields s := by
  rw [AllocateSearch.searched,fields_split,fields_candidate]
private theorem fields_resumed (s : Store NearState) (op : Nat) (p : Layout) : fields (resumed s op p)=fields s := by
  rw [resumed,fields_paid,hopped,advanced,fields_charge,fields_store32,fields_paid,fields_candidate]
 theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs=s.funcs ∧ (after s op p).modules=s.modules ∧ (after s op p).tables=s.tables ∧ (after s op p).globals=s.globals := by
  have h : fields (after s op p)=fields s := by
    rw [after,fields_paid,fields_searched,fields_resumed,before,fields_paid,initialAfter,fields_paid]
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩
 theorem callAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter s op p).funcs=s.funcs ∧ (callAfter s op p).modules=s.modules ∧ (callAfter s op p).tables=s.tables ∧ (callAfter s op p).globals=s.globals := by
  unfold callAfter
  exact after_fields (entered s op) op p
end
end WNear.Proofs.AllocateSkip
