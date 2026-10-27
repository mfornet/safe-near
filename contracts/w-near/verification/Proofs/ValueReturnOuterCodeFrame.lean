import Proofs.ValueReturnOuterState

/-! Small code projections prevent phase-frame proofs from reducing complete
computed memories or recursively expanded gas stores. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

private def codeFields (s : Store NearState) := (s.funcs, s.modules, s.tables)

private theorem fields_paid (s : Store NearState) (op n : Nat) :
    codeFields (paid s op n) = codeFields s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem fields_charge (s : Store NearState) (cost : Nat) :
    codeFields (chargedStore s cost) = codeFields s := rfl

private theorem fields_global (s : Store NearState) (index : Nat) (value : Value) :
    codeFields (setGlobal s index value) = codeFields s := rfl

private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    codeFields (storeI32 s index address memory value) = codeFields s := rfl

attribute [local irreducible] codeFields acquired high low reserved arguments looked lookupBefore status dispatchBefore

private theorem fields_acquire (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out cell : UInt32) (memory : Memory) :
    codeFields (ValueReturnAcquire.calledAcquireStore s op globalIndex memoryIndex sp out cell memory) = codeFields s := by
  simp only [ValueReturnAcquire.calledAcquireStore, ValueReturnAcquire.acquireStore,
    ValueReturnAcquire.acquireEntryStore, ValueReturnAcquire.recordStore, ValueReturnAcquire.guardStore,
    ValueReturnAcquire.calledIncrementStore, ValueReturnAcquire.incrementStore,
    ValueReturnAcquire.incrementEntryStore, ValueReturnAcquire.reserved,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore,
    ValueReturnBorrowCounters.swapEntryStore, fields_paid, fields_charge, fields_global, fields_store]

private theorem fields_lookup (s : Store NearState) (op : Nat) :
    codeFields (ValueReturnThreadLocal.indirectAfter s op) = codeFields s := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter,
    ValueReturnThreadLocal.entered, fields_paid, fields_charge]

private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) :
    codeFields (arguments s op p) = codeFields s := by
  simp only [arguments, looked, lookupBefore, reserved, fields_paid, fields_lookup, fields_global]

private theorem fields_acquired (s : Store NearState) (op : Nat) (p : Layout) :
    codeFields (acquired s op p) = codeFields s := by
  rw [acquired, fields_acquire, fields_arguments]

private theorem fields_high (s : Store NearState) (op : Nat) (p : Layout) :
    codeFields (high s op p) = codeFields s := by
  rw [high, fields_store, fields_paid, fields_acquired]

private theorem fields_status (s : Store NearState) (op : Nat) (p : Layout) :
    codeFields (status s op p) = codeFields s := by
  rw [status, fields_paid, low, fields_store, fields_paid, fields_high]

private theorem fields_dispatch (s : Store NearState) (op : Nat) (p : Layout) :
    codeFields (dispatchBefore s op p) = codeFields s := by
  rw [dispatchBefore, ValueReturnOuter.nonnullAfter, fields_paid, ValueReturnOuter.nonnullEntry,
    fields_charge, fields_charge, fields_paid, fields_status]

private theorem fields_reset (s : Store NearState) (memory : Array Memory) (host : NearState) :
    codeFields {s with mems := memory, host := host} = codeFields s := by
  unfold codeFields
  rfl


private theorem code_of_fields (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : codeFields t = codeFields s) : Code t p inst extra := by
  have hf' : t.funcs = s.funcs := by
    simpa only [codeFields] using congrArg (fun x => x.1) hf
  have hm' : t.modules = s.modules := by
    simpa only [codeFields] using congrArg (fun x => x.2.1) hf
  have ht' : t.tables = s.tables := by
    simpa only [codeFields] using congrArg (fun x => x.2.2) hf
  exact h.transport s t p inst extra hf' hm' ht' 

theorem Code.acquired (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (ValueReturnOuterBody.acquired s op p) p inst extra :=
  code_of_fields s _ p inst extra h (fields_acquired s op p)

theorem Code.high (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (ValueReturnOuterBody.high s op p) p inst extra :=
  code_of_fields s _ p inst extra h (fields_high s op p)

theorem Code.status (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (ValueReturnOuterBody.status s op p) p inst extra :=
  code_of_fields s _ p inst extra h (fields_status s op p)

theorem Code.selected (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (paid (ValueReturnOuterBody.status s op p) op 6) p inst extra := by
  apply code_of_fields s _ p inst extra h
  rw [fields_paid, fields_status]

theorem Code.dispatch (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (dispatchBefore s op p) p inst extra :=
  code_of_fields s _ p inst extra h (fields_dispatch s op p)

theorem Code.returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (ValueReturnOuterBody.returned cfg s p) p inst extra := by
  have hd := fields_dispatch s cfg.regularOpCost p
  have hr := ValueReturnDispatchGas.fragmentAfter_resources cfg (dispatchBefore s cfg.regularOpCost p) p.mi p.len p.ptr
  have hf := (fields_reset _ _ _).symm.trans (congrArg codeFields hr)
  have hf' : codeFields (ValueReturnOuterBody.returned cfg s p) =
      codeFields (dispatchBefore s cfg.regularOpCost p) := by
    simpa only [ValueReturnOuterBody.returned] using hf
  exact code_of_fields s _ p inst extra h (hf'.trans hd)

end WNear.Proofs.ValueReturnOuterBody
