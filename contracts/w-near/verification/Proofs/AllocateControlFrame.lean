import Proofs.AllocateControlBody

/-! Exact resource effects of the real 53-opcode end-split control phase. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] readI32 writeI32

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem controlAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some (initializedMemory p)) :
    (controlAfter s op p).mems[p.memoryIndex]? = some (linkedMemory p) := by
  have first : (afterBacklink s op p).mems[p.memoryIndex]? = some (backlinkedMemory p) := by
    unfold afterBacklink backlinkStore Allocate.taggedStore
    apply storeI32_memory
    rw [mems_paid,mems_paid]
    exact hm
  have second : (previousStore (afterBacklink s op p) op p).mems[p.memoryIndex]? = some (previousMemory p) := by
    unfold previousStore Allocate.taggedStore
    apply storeI32_memory
    rw [mems_paid]
    exact first
  have third : (unflaggedStore (afterBacklink s op p) op p).mems[p.memoryIndex]? = some (unflaggedMemory p) := by
    unfold unflaggedStore maskStore
    apply storeI32_memory
    rw [mems_paid]
    exact second
  unfold controlAfter
  rw [mems_paid]
  unfold linkedStore taggedTeeStore
  apply storeI32_memory
  rw [mems_paid]
  exact third

theorem controlAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (53*op+rest)) : (controlAfter s op p).host.gas.Credits rest := by
  have c1 : (afterBacklink s op p).host.gas.Credits (28*op+rest) := by
    unfold afterBacklink backlinkStore Allocate.taggedStore
    rw [storeI32_host]
    exact paid_credits (paid s op 17) op 8 _ (paid_credits s op 17 _ (hc.mono (by omega)))
  have c2 : (previousStore (afterBacklink s op p) op p).host.gas.Credits (20*op+rest) := by
    unfold previousStore Allocate.taggedStore
    rw [storeI32_host]
    exact paid_credits _ op 8 _ (c1.mono (by omega))
  have c3 : (unflaggedStore (afterBacklink s op p) op p).host.gas.Credits (14*op+rest) := by
    unfold unflaggedStore maskStore
    rw [storeI32_host]
    exact paid_credits _ op 6 _ (c2.mono (by omega))
  have c4 : (linkedStore (afterBacklink s op p) op p).host.gas.Credits (5*op+rest) := by
    unfold linkedStore taggedTeeStore
    rw [storeI32_host]
    exact paid_credits _ op 9 _ (c3.mono (by omega))
  exact paid_credits _ op 5 rest c4

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    fields (storeI32 s index address memory value) = fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t = fields s) :
    t.funcs = s.funcs ∧ t.modules = s.modules ∧ t.tables = s.tables ∧ t.globals = s.globals :=
  ⟨congrArg (fun x => x.1) h,congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2.1) h,congrArg (fun x => x.2.2.2) h⟩

theorem controlAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (controlAfter s op p).funcs = s.funcs ∧ (controlAfter s op p).modules = s.modules ∧
    (controlAfter s op p).tables = s.tables ∧ (controlAfter s op p).globals = s.globals := by
  have h : fields (controlAfter s op p) = fields s := by
    simp only [controlAfter,linkedStore,taggedTeeStore,unflaggedStore,maskStore,previousStore,
      afterBacklink,backlinkStore,Allocate.taggedStore,fields_paid,fields_store]
  exact fields_project s _ h

private def hostView (seed host : NearState) := {host with gas := seed.gas,gasProfile := seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    hostView seed (chargedStore s cost).host = hostView seed s.host := by
  simp only [hostView,chargedStore,chargeHost]
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host = hostView seed s.host := by
  induction n with
  | zero => rfl
  | succ n ih => exact (view_charge seed (paid s op n) op).trans ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    hostView seed (storeI32 s index address memory value).host = hostView seed s.host := rfl

theorem controlAfter_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(controlAfter s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  have h : hostView s.host (controlAfter s op p).host = hostView s.host s.host := by
    simp only [controlAfter,linkedStore,taggedTeeStore,unflaggedStore,maskStore,previousStore,
      afterBacklink,backlinkStore,Allocate.taggedStore,view_paid,view_store]
  exact h

end WNear.Proofs.AllocateSearch
