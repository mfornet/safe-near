import Proofs.StateDispatchPrefix
import Proofs.ValueReturnOuterCodeFrame

/-! Exact resources and gas after the actual SDK lookup and borrow acquisition. -/
namespace WNear.Proofs.StateDispatchPrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

def acquiredMemory (p : Layout) := ValueReturnAcquire.recordMemory
  (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904)) (scratch p) 1074904

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some p.memory := by
  simpa only [arguments,looked,lookupBefore,reserved,ValueReturnThreadLocal.indirectAfter,
    ValueReturnThreadLocal.indirectEntered,ValueReturnThreadLocal.lookupAfter,
    ValueReturnThreadLocal.callAfter,ValueReturnThreadLocal.entered,paid,chargedStore,setGlobal] using hm

theorem acquired_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
  exact ValueReturnAcquire.calledAcquireStore_memory (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p) 1074904 p.memory (arguments_memory s op p hm)

theorem acquired_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (acquired s op p).globals = (reserved s op p).globals := by
  have hargs : (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    rw [arguments_globals]; exact reserved_global s op p hg
  have h := ValueReturnAcquire.calledAcquireStore_globals (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p) 1074904 p.memory {p.global with value := .i32 (scratch p)} hargs rfl
  exact h.trans (arguments_globals s op p)

theorem acquired_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (acquired s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [acquired_globals s op p hg]; exact reserved_global s op p hg

private def codeFields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : codeFields (paid s op n) = codeFields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : codeFields (chargedStore s cost) = codeFields s := rfl
private theorem fields_global (s : Store NearState) (index : Nat) (value : Value) : codeFields (setGlobal s index value) = codeFields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) : codeFields (storeI32 s index address memory value) = codeFields s := rfl
private theorem fields_acquire (s : Store NearState) (op gi mi : Nat) (sp out cell : UInt32) (memory : Memory) :
    codeFields (ValueReturnAcquire.calledAcquireStore s op gi mi sp out cell memory) = codeFields s := by
  simp only [ValueReturnAcquire.calledAcquireStore,ValueReturnAcquire.acquireStore,
    ValueReturnAcquire.acquireEntryStore,ValueReturnAcquire.recordStore,ValueReturnAcquire.guardStore,
    ValueReturnAcquire.calledIncrementStore,ValueReturnAcquire.incrementStore,
    ValueReturnAcquire.incrementEntryStore,ValueReturnAcquire.reserved,
    ValueReturnBorrowCounters.calledSwapStore,ValueReturnBorrowCounters.swapStore,
    ValueReturnBorrowCounters.swapEntryStore,fields_paid,fields_charge,fields_global,fields_store]
private theorem fields_lookup (s : Store NearState) (op : Nat) : codeFields (ValueReturnThreadLocal.indirectAfter s op) = codeFields s := by
  simp only [ValueReturnThreadLocal.indirectAfter,ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter,ValueReturnThreadLocal.callAfter,ValueReturnThreadLocal.entered,fields_paid,fields_charge]

private theorem fields_project (s t : Store NearState) (h : codeFields t = codeFields s) :
    t.funcs = s.funcs ∧ t.modules = s.modules ∧ t.tables = s.tables := by
  exact ⟨congrArg (fun x => x.1) h,congrArg (fun x => x.2.1) h,congrArg (fun x => x.2.2) h⟩

theorem acquired_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (acquired s op p).funcs = s.funcs ∧ (acquired s op p).modules = s.modules ∧ (acquired s op p).tables = s.tables := by
  have h : codeFields (acquired s op p) = codeFields s := by
    simp only [acquired,arguments,looked,lookupBefore,reserved,fields_acquire,fields_paid,fields_lookup,fields_global]
  exact fields_project s (acquired s op p) h

private def GasEffect (s t : Store NearState) (op n : Nat) : Prop := ∀ rest,
  s.host.gas.Credits (n * op + rest) →
    t.host.gas.burnt = s.host.gas.burnt + n * op ∧ t.host.gas.promises = s.host.gas.promises ∧ t.host.gas.Credits rest
private theorem gas_trans (s t u : Store NearState) (op a b : Nat)
    (h₁ : GasEffect s t op a) (h₂ : GasEffect t u op b) : GasEffect s u op (a + b) := by
  intro rest hc
  have c₁ := h₁ (b * op + rest) (hc.mono (by simp only [Nat.add_mul]; omega))
  have c₂ := h₂ rest c₁.2.2
  refine ⟨?_,c₂.2.1.trans c₁.2.1,c₂.2.2⟩
  rw [c₂.1,c₁.1,Nat.add_mul]; omega
private theorem gas_paid (s : Store NearState) (op n : Nat) : GasEffect s (paid s op n) op n := by
  intro rest hc
  have h := paid_gas s op n rest hc
  exact ⟨h.1,h.2,paid_credits s op n rest hc⟩
private theorem gas_charge (s : Store NearState) (op n : Nat) : GasEffect s (chargedStore s (n * op)) op n := by
  intro rest hc
  have h := GasCounter.burn_credits s.host.gas (n * op) rest hc
  exact ⟨h.2.1,h.2.2.1,h.2.2.2⟩
private theorem gas_lookup (s : Store NearState) (op : Nat) : GasEffect s (ValueReturnThreadLocal.indirectAfter s op) op 29 := by
  have a : GasEffect s (chargedStore s op) op 1 := by simpa only [Nat.one_mul] using gas_charge s op 1
  have b := gas_charge (chargedStore s op) op 8
  have c := gas_paid (ValueReturnThreadLocal.indirectEntered s op) op 2
  have d : GasEffect (paid (ValueReturnThreadLocal.indirectEntered s op) op 2)
      (chargedStore (paid (ValueReturnThreadLocal.indirectEntered s op) op 2) op) op 1 := by
    simpa only [Nat.one_mul] using gas_charge (paid (ValueReturnThreadLocal.indirectEntered s op) op 2) op 1
  have e := gas_charge (chargedStore (paid (ValueReturnThreadLocal.indirectEntered s op) op 2) op) op 9
  have f := gas_paid (ValueReturnThreadLocal.entered (paid (ValueReturnThreadLocal.indirectEntered s op) op 2) op) op 8
  -- The actual order is opcode, outer activation, two arguments, inner opcode/activation, body.
  have ab := gas_trans s _ _ op 1 8 a b
  have abc := gas_trans s _ _ op 9 2 ab c
  have abcd := gas_trans s _ _ op 11 1 abc d
  have abcde := gas_trans s _ _ op 12 9 abcd e
  have result := gas_trans s _ _ op 21 8 abcde f
  simpa only [ValueReturnThreadLocal.indirectAfter,ValueReturnThreadLocal.lookupAfter,
    ValueReturnThreadLocal.callAfter,ValueReturnThreadLocal.indirectEntered,ValueReturnThreadLocal.entered,Nat.one_mul] using result

private theorem gas_arguments (s : Store NearState) (op : Nat) (p : Layout) : GasEffect s (arguments s op p) op 42 := by
  have a : GasEffect s (reserved s op p) op 5 := gas_paid s op 5
  have b := gas_paid (reserved s op p) op 2
  have c := gas_lookup (lookupBefore s op p) op
  have d := gas_paid (looked s op p) op 3
  have e := gas_paid (paid (looked s op p) op 3) op 3
  have ab := gas_trans s _ _ op 5 2 a b
  have abc := gas_trans s _ _ op 7 29 ab c
  have abcd := gas_trans s _ _ op 36 3 abc d
  exact gas_trans s _ _ op 39 3 abcd e

theorem acquired_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (114 * op + rest)) :
    (acquired s op p).host.gas.burnt = s.host.gas.burnt + 114 * op ∧
    (acquired s op p).host.gas.promises = s.host.gas.promises ∧ (acquired s op p).host.gas.Credits rest := by
  have a := gas_arguments s op p (72 * op + rest) (hc.mono (by omega))
  have b := ValueReturnAcquire.calledAcquireStore_gas (arguments s op p) op p.globalIndex p.memoryIndex rest
    (scratch p) (scratch p) 1074904 p.memory a.2.2
  refine ⟨?_,b.2.1.trans a.2.1,b.2.2⟩
  change (ValueReturnAcquire.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex (scratch p) (scratch p) 1074904 p.memory).host.gas.burnt = _
  rw [b.1,a.1]; omega

end WNear.Proofs.StateDispatchPrefix
