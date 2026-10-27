import Proofs.InterfaceSetPhases
import Proofs.InterfaceBorrowFrame

/-! Code-field frames for the actual sequential setter states. -/
namespace WNear.Proofs.InterfaceSetPhases
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open InterfaceSetState
set_option maxRecDepth 16384

private def fields (s : Store NearState) := (s.funcs, s.modules, s.tables)
private theorem paid_fields (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem charge_fields (s : Store NearState) (cost : Nat) : fields (chargedStore s cost) = fields s := rfl
private theorem global_fields (s : Store NearState) (index : Nat) (value : Value) : fields (setGlobal s index value) = fields s := rfl
private theorem write_fields (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    fields (storeI32 s index address m v) = fields s := rfl
attribute [local irreducible] fields paid storeI32 setGlobal chargedStore
  InterfaceBorrow.calledAcquireStore InterfaceBorrow.acquireStore InterfaceBorrow.recordStore
  InterfaceBorrow.guardStore InterfaceBorrow.calledTakeStore InterfaceBorrow.takeStore InterfaceBorrow.reserved
  ValueReturnBorrowCounters.calledSwapStore ValueReturnBorrowCounters.swapStore
  reserved savedArguments lookupBefore looked arguments acquired installed released branched finalStore

private theorem acquire_fields (s : Store NearState) (op gi mi : Nat) (sp out cell : UInt32) (m : Memory) :
    fields (InterfaceBorrow.calledAcquireStore s op gi mi sp out cell m) = fields s := by
  rw [InterfaceBorrow.calledAcquireStore, InterfaceBorrow.acquireStore, global_fields, paid_fields,
    InterfaceBorrow.recordStore, write_fields, paid_fields, write_fields, paid_fields,
    InterfaceBorrow.guardStore, paid_fields, InterfaceBorrow.calledTakeStore, InterfaceBorrow.takeStore,
    paid_fields, ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore,
    write_fields, paid_fields, ValueReturnBorrowCounters.swapEntryStore, charge_fields, charge_fields,
    paid_fields, InterfaceBorrow.takeEntryStore, charge_fields, charge_fields, paid_fields,
    InterfaceBorrow.reserved, global_fields, paid_fields, InterfaceBorrow.acquireEntryStore, charge_fields, charge_fields]

private theorem lookup_fields (s : Store NearState) (op : Nat) :
    fields (ValueReturnThreadLocal.indirectAfter s op) = fields s := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    paid_fields, charge_fields]

private theorem install_fields (s : Store NearState) (op index : Nat) (scratch receiver vtable : UInt32)
    (m0 m1 m2 : Memory) :
    fields (InterfaceSetInstallTail.after s op index scratch receiver vtable m0 m1 m2) = fields s := by
  simp only [InterfaceSetInstallTail.after, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord,
    InterfaceSetInstallTail.guardedStore, InterfaceInstall.guardAfter, InterfaceInstall.guardEntry,
    InterfaceSetInstallTail.lowStore, InterfaceSetInstallTail.highStore,
    InterfaceSetBody.copiedWord, InterfaceSetBody.copiedTeeWord, paid_fields, charge_fields, write_fields]

private theorem release_fields (s : Store NearState) (op index : Nat) (counter : UInt32) (m : Memory) :
    fields (InterfaceBorrow.calledReleaseStore s op index counter m) = fields s := by
  simp only [InterfaceBorrow.calledReleaseStore, InterfaceBorrow.releaseEntryStore, InterfaceBorrow.releasedStore,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore,
    paid_fields, charge_fields, write_fields]

private theorem check_fields (s : Store NearState) (op index : Nat) (sp : UInt32) :
    fields (ValueReturnOuter.checkAfter s op index sp) = fields s := by
  simp only [ValueReturnOuter.checkAfter, ValueReturnOuter.nonnullEntry, ValueReturnBorrow.checkedStore,
    paid_fields, charge_fields, global_fields]

private theorem reserved_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (reserved s op p) = fields s := by
  rw [reserved, global_fields, paid_fields]
private theorem saved_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (savedArguments s op p) = fields s := by
  simp only [savedArguments, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, write_fields, paid_fields, reserved_fields]
private theorem before_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (lookupBefore s op p) = fields s := by
  rw [lookupBefore, paid_fields, saved_fields]
private theorem looked_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (looked s op p) = fields s := by
  rw [looked, lookup_fields, before_fields]
private theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p) = fields s := by
  rw [arguments, paid_fields, paid_fields, looked_fields]
private theorem acquired_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (acquired s op p) = fields s := by
  rw [acquired, acquire_fields, arguments_fields]
private theorem installed_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (installed s op p) = fields s := by
  rw [installed, install_fields, acquired_fields]
private theorem released_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (released s op p) = fields s := by
  rw [released, release_fields, paid_fields, installed_fields]
private theorem branched_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (branched s op p) = fields s := by
  rw [branched, charge_fields, paid_fields, released_fields]
private theorem final_fields (s : Store NearState) (op : Nat) (p : Layout) : fields (finalStore s op p) = fields s := by
  rw [finalStore, global_fields, paid_fields, check_fields, paid_fields, branched_fields]

private theorem code_of_fields (s t : Store NearState) (p : Layout) (inst : Nat)
    (h : Code s p inst) (hf : fields t = fields s) : Code t p inst := by
  have hfuncs : t.funcs = s.funcs := by simpa only [fields] using congrArg (fun x => x.1) hf
  have hmodules : t.modules = s.modules := by simpa only [fields] using congrArg (fun x => x.2.1) hf
  have htables : t.tables = s.tables := by simpa only [fields] using congrArg (fun x => x.2.2) hf
  exact h.transport s t p inst hfuncs hmodules htables

theorem reserved_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (reserved s op p) p inst := code_of_fields s _ p inst h (reserved_fields s op p)

theorem savedArguments_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (savedArguments s op p) p inst := code_of_fields s _ p inst h (saved_fields s op p)

theorem lookupBefore_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (lookupBefore s op p) p inst := code_of_fields s _ p inst h (before_fields s op p)

theorem looked_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (looked s op p) p inst := code_of_fields s _ p inst h (looked_fields s op p)

theorem arguments_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (arguments s op p) p inst := code_of_fields s _ p inst h (arguments_fields s op p)

theorem acquired_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (acquired s op p) p inst := code_of_fields s _ p inst h (acquired_fields s op p)

theorem installed_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (installed s op p) p inst := code_of_fields s _ p inst h (installed_fields s op p)

theorem released_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (released s op p) p inst := code_of_fields s _ p inst h (released_fields s op p)

theorem branched_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (branched s op p) p inst := code_of_fields s _ p inst h (branched_fields s op p)

theorem finalStore_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (finalStore s op p) p inst := code_of_fields s _ p inst h (final_fields s op p)

theorem acquire_code (s : Store NearState) (op gi mi : Nat) (sp out cell : UInt32) (memory : Memory)
    (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (InterfaceBorrow.calledAcquireStore s op gi mi sp out cell memory) p inst :=
  code_of_fields s _ p inst h (acquire_fields s op gi mi sp out cell memory)

theorem install_code (s : Store NearState) (op index : Nat) (scratch receiver vtable : UInt32)
    (m0 m1 m2 : Memory) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (InterfaceSetInstallTail.after s op index scratch receiver vtable m0 m1 m2) p inst :=
  code_of_fields s _ p inst h (install_fields s op index scratch receiver vtable m0 m1 m2)

end WNear.Proofs.InterfaceSetPhases
