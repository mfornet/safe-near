import Proofs.AllocateLayoutWrapperState

/-! Actual wrapper stage memories, immutable code and complete gas credits. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem paid_host_congr (s t : Store NearState) (op n : Nat) (h : s.host = t.host) : (paid s op n).host = (paid t op n).host := by
  induction n with | zero => exact h | succ n ih => exact congrArg (fun host => (chargeHost host op).1) ih

theorem reserved_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (reserved s op p).mems[p.memoryIndex]? = some p.memory := by simpa only [reserved,setGlobal,paid_mems] using hm
theorem alignment_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (alignmentStore s op p).mems[p.memoryIndex]? = some (alignmentMemory p) := by
  have mm : (paid (reserved s op p) op 3).mems[p.memoryIndex]? = some p.memory := by rw [paid_mems]; exact reserved_memory s op p hm
  exact storeI32_memory _ _ _ _ _ mm
theorem setup_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (setupStore s op p).mems[p.memoryIndex]? = some (setupMemory p) := by
  have mm : (paid (alignmentStore s op p) op 3).mems[p.memoryIndex]? = some (alignmentMemory p) := by rw [paid_mems]; exact alignment_memory s op p hm
  exact storeI32_memory _ _ _ _ _ mm
theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some (setupMemory p) := by simpa only [arguments,paid_mems] using setup_memory s op p hm
theorem laidOut_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (laidOut s op p).mems[p.memoryIndex]? = some (laidOutMemory p) := AllocateLayout.called_memory (arguments s op p) op (leafLayout p) (arguments_memory s op p hm)
theorem copied_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (copied s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have mm : (paid (laidOut s op p) op 4).mems[p.memoryIndex]? = some (laidOutMemory p) := by rw [paid_mems]; exact laidOut_memory s op p hm
  exact storeI64_memory _ _ _ _ _ mm
theorem after_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by simpa only [after,setGlobal,paid_mems] using copied_memory s op p hm

theorem reserved_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (reserved s op p).funcs = s.funcs ∧ (reserved s op p).modules = s.modules ∧ (reserved s op p).tables = s.tables := by
  simp only [reserved,setGlobal,paid,chargedStore,and_self]
theorem alignment_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (alignmentStore s op p).funcs = s.funcs ∧ (alignmentStore s op p).modules = s.modules ∧ (alignmentStore s op p).tables = s.tables := by
  simpa only [alignmentStore,constantStore,storeI32_funcs,storeI32_modules,storeI32_tables,paid,chargedStore] using reserved_fields s op p
theorem setup_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (setupStore s op p).funcs = s.funcs ∧ (setupStore s op p).modules = s.modules ∧ (setupStore s op p).tables = s.tables := by
  simpa only [setupStore,InterfaceSetBody.storeWord,storeI32_funcs,storeI32_modules,storeI32_tables,paid,chargedStore] using alignment_fields s op p
theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs = s.funcs ∧ (arguments s op p).modules = s.modules ∧ (arguments s op p).tables = s.tables := by
  simpa only [arguments,paid,chargedStore] using setup_fields s op p
theorem laidOut_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (laidOut s op p).funcs = s.funcs ∧ (laidOut s op p).modules = s.modules ∧ (laidOut s op p).tables = s.tables := by
  have a := AllocateLayout.called_fields (arguments s op p) op (leafLayout p)
  have b := arguments_fields s op p
  exact ⟨a.1.trans b.1,a.2.1.trans b.2.1,a.2.2.trans b.2.2⟩
theorem copied_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (copied s op p).funcs = s.funcs ∧ (copied s op p).modules = s.modules ∧ (copied s op p).tables = s.tables := by
  simpa only [copied,copyStore,storeI64_funcs,storeI64_modules,storeI64_tables,paid,chargedStore] using laidOut_fields s op p

theorem reserved_global (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (reserved s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [reserved,setGlobal,paid_globals]
  simp [Array.getElem?_modify,hg]
theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simpa only [arguments,setupStore,InterfaceSetBody.storeWord,alignmentStore,constantStore,storeI32_globals,paid_globals] using reserved_global s op p hg
theorem laidOut_globals (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (laidOut s op p).globals = (arguments s op p).globals :=
  AllocateLayout.called_globals (arguments s op p) op (leafLayout p) (arguments_global s op p hg) rfl
theorem copied_global (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (copied s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [copied,copyStore,storeI64_globals,paid_globals,laidOut_globals s op p hg]
  exact arguments_global s op p hg

theorem reserved_host (s : Store NearState) (op : Nat) (p : Layout) : (reserved s op p).host = (paid s op 5).host := rfl
theorem alignment_host (s : Store NearState) (op : Nat) (p : Layout) : (alignmentStore s op p).host = (paid s op 8).host := by
  have h := paid_host_congr (reserved s op p) (paid s op 5) op 3 (reserved_host s op p)
  simpa only [alignmentStore,constantStore,storeI32_host,ValueReturnBorrow.paid_add] using h
theorem setup_host (s : Store NearState) (op : Nat) (p : Layout) : (setupStore s op p).host = (paid s op 11).host := by
  have h := paid_host_congr (alignmentStore s op p) (paid s op 8) op 3 (alignment_host s op p)
  simpa only [setupStore,InterfaceSetBody.storeWord,storeI32_host,ValueReturnBorrow.paid_add] using h
theorem arguments_host (s : Store NearState) (op : Nat) (p : Layout) : (arguments s op p).host = (paid s op 15).host := by
  have h := paid_host_congr (setupStore s op p) (paid s op 11) op 4 (setup_host s op p)
  simpa only [arguments,ValueReturnBorrow.paid_add] using h

theorem arguments_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (15 * op + rest)) :
    (arguments s op p).host.gas.Credits rest := by rw [arguments_host]; exact paid_credits s op 15 rest hc
theorem laidOut_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (59 * op + rest)) :
    (laidOut s op p).host.gas.Credits rest := AllocateLayout.called_credits (arguments s op p) op rest (leafLayout p)
      (arguments_credits s op (44 * op + rest) p (hc.mono (by omega)))
theorem copied_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (63 * op + rest)) :
    (copied s op p).host.gas.Credits rest := paid_credits (laidOut s op p) op 4 rest
      (laidOut_credits s op (4 * op + rest) p (hc.mono (by omega)))
theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (67 * op + rest)) :
    (after s op p).host.gas.Credits rest := paid_credits (copied s op p) op 4 rest
      (copied_credits s op (4 * op + rest) p (hc.mono (by omega)))

end WNear.Proofs.AllocateLayoutWrapper
