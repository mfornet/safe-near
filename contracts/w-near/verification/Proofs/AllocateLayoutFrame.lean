import Proofs.AllocateLayoutState
import Proofs.StorePairAddresses

/-! Derived memory, code and gas frames of the accepted alignment-one leaf. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem reserved_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (reserved s op p).mems[p.memoryIndex]? = some p.memory := by simpa only [reserved,setGlobal,paid_mems] using hm
theorem guarded_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (guarded s op p).mems[p.memoryIndex]? = some p.memory := by simpa only [guarded,paid_mems] using reserved_memory s op p hm
theorem loaded_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (loaded s op p).mems[p.memoryIndex]? = some p.memory := by simpa only [loaded,paid_mems] using guarded_memory s op p hm
theorem high_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (high s op p).mems[p.memoryIndex]? = some (highMemory p) := by
  have mm : (paid (loaded s op p) op 3).mems[p.memoryIndex]? = some p.memory := by rw [paid_mems]; exact loaded_memory s op p hm
  exact storeI32_memory _ _ _ _ _ mm
theorem low_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (low s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have mm : (paid (high s op p) op 11).mems[p.memoryIndex]? = some (highMemory p) := by rw [paid_mems]; exact high_memory s op p hm
  exact storeI32_memory _ _ _ _ _ mm
theorem after_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by simpa only [after,setGlobal,paid_mems] using low_memory s op p hm

theorem reserved_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (reserved s op p).funcs = s.funcs ∧ (reserved s op p).modules = s.modules ∧ (reserved s op p).tables = s.tables := by
  simp only [reserved,setGlobal,paid,chargedStore,and_self]
theorem guarded_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (guarded s op p).funcs = s.funcs ∧ (guarded s op p).modules = s.modules ∧ (guarded s op p).tables = s.tables := by
  simpa only [guarded,paid,chargedStore] using reserved_fields s op p
theorem loaded_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (loaded s op p).funcs = s.funcs ∧ (loaded s op p).modules = s.modules ∧ (loaded s op p).tables = s.tables := by
  simpa only [loaded,paid,chargedStore] using guarded_fields s op p
theorem high_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (high s op p).funcs = s.funcs ∧ (high s op p).modules = s.modules ∧ (high s op p).tables = s.tables := by
  simpa only [high,storeI32_funcs,storeI32_modules,storeI32_tables,paid,chargedStore] using loaded_fields s op p
theorem low_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (low s op p).funcs = s.funcs ∧ (low s op p).modules = s.modules ∧ (low s op p).tables = s.tables := by
  simpa only [low,roundedStore,storeI32_funcs,storeI32_modules,storeI32_tables,paid,chargedStore] using high_fields s op p
theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧ (after s op p).tables = s.tables := by
  simpa only [after,setGlobal,paid,chargedStore] using low_fields s op p

theorem reserved_global (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (reserved s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [reserved,setGlobal,paid_globals]
  simp [Array.getElem?_modify,hg]
theorem low_global (s : Store NearState) (op : Nat) (p : Layout) (hg : s.globals[p.globalIndex]? = some p.global) :
    (low s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simpa only [low,roundedStore,high,loaded,guarded,storeI32_globals,paid_globals] using reserved_global s op p hg

private theorem paid_host_congr (s t : Store NearState) (op n : Nat) (h : s.host = t.host) :
    (paid s op n).host = (paid t op n).host := by
  induction n with
  | zero => exact h
  | succ n ih => exact congrArg (fun host => (chargeHost host op).1) ih

theorem reserved_host (s : Store NearState) (op : Nat) (p : Layout) : (reserved s op p).host = (paid s op 5).host := rfl

theorem guarded_host (s : Store NearState) (op : Nat) (p : Layout) : (guarded s op p).host = (paid s op 12).host := by
  have h := paid_host_congr (reserved s op p) (paid s op 5) op 7 (reserved_host s op p)
  simpa only [guarded,ValueReturnBorrow.paid_add] using h

theorem loaded_host (s : Store NearState) (op : Nat) (p : Layout) : (loaded s op p).host = (paid s op 15).host := by
  have h := paid_host_congr (guarded s op p) (paid s op 12) op 3 (guarded_host s op p)
  simpa only [loaded,ValueReturnBorrow.paid_add] using h

theorem high_host (s : Store NearState) (op : Nat) (p : Layout) : (high s op p).host = (paid s op 18).host := by
  have h := paid_host_congr (loaded s op p) (paid s op 15) op 3 (loaded_host s op p)
  simpa only [high,storeI32_host,ValueReturnBorrow.paid_add] using h

theorem low_host (s : Store NearState) (op : Nat) (p : Layout) : (low s op p).host = (paid s op 29).host := by
  have h := paid_host_congr (high s op p) (paid s op 18) op 11 (high_host s op p)
  simpa only [low,roundedStore,storeI32_host,ValueReturnBorrow.paid_add] using h

theorem after_host (s : Store NearState) (op : Nat) (p : Layout) : (after s op p).host = (paid s op 33).host := by
  have h := paid_host_congr (low s op p) (paid s op 29) op 4 (low_host s op p)
  simpa only [after,setGlobal,ValueReturnBorrow.paid_add] using h

theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (33 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 33 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧ (after s op p).host.gas.Credits rest := by
  rw [after_host]
  exact ⟨(paid_gas s op 33 rest hc).1,(paid_gas s op 33 rest hc).2,paid_credits s op 33 rest hc⟩

end WNear.Proofs.AllocateLayout
