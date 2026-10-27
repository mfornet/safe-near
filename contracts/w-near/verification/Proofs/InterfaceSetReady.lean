import Proofs.InterfaceSetPhases
import Proofs.InterfaceBorrowFrame

/-! Computed memory/global facts follow from original setter resources. -/
namespace WNear.Proofs.InterfaceSetPhases
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open InterfaceSetState
set_option maxRecDepth 16384

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem lookup_mems (s : Store NearState) (op : Nat) :
    (ValueReturnThreadLocal.indirectAfter s op).mems = s.mems := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    paid_mems, chargedStore]
private theorem lookup_globals (s : Store NearState) (op : Nat) :
    (ValueReturnThreadLocal.indirectAfter s op).globals = s.globals := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    paid_globals, chargedStore]

private theorem twoWords_memory (s : Store NearState) (op index firstOffset secondOffset : Nat)
    (address first second : UInt32) (memory : Memory) (hm : s.mems[index]? = some memory) :
    (InterfaceSetBody.twoWordsStore s op index firstOffset secondOffset address first second memory).mems[index]? =
      some (writeI32 (writeI32 memory (address.toNat + firstOffset) first) (address.toNat + secondOffset) second) := by
  have hpaid : (paid s op 3).mems[index]? = some memory := by rw [paid_mems]; exact hm
  have hfirst := storeI32_memory (paid s op 3) index (address.toNat + firstOffset) memory first hpaid
  have hsecondPaid : (paid (InterfaceSetBody.storeWord s op index firstOffset address first memory) op 3).mems[index]? =
      some (writeI32 memory (address.toNat + firstOffset) first) := by
    rw [paid_mems]
    simpa only [InterfaceSetBody.storeWord] using hfirst
  have hsecond := storeI32_memory (paid (InterfaceSetBody.storeWord s op index firstOffset address first memory) op 3)
    index (address.toNat + secondOffset) (writeI32 memory (address.toNat + firstOffset) first) second hsecondPaid
  simpa only [InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord] using hsecond

theorem savedArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (savedArguments s op p).mems[p.memoryIndex]? = some (savedMemory p) := by
  have hr : (reserved s op p).mems[p.memoryIndex]? = some p.memory := by
    simpa only [reserved, setGlobal, paid_mems] using hm
  have h := twoWords_memory (reserved s op p) op p.memoryIndex 20 16 (scratch p) p.vtable p.receiver p.memory hr
  simpa only [savedArguments, savedMemory] using h

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some (savedMemory p) := by
  rw [arguments, paid_mems, paid_mems, looked, lookup_mems, lookupBefore, paid_mems]
  exact savedArguments_memory s op p hm

private theorem arguments_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (reserved s op p).globals := by
  simp only [arguments, looked, lookupBefore, savedArguments, InterfaceSetBody.twoWordsStore,
    InterfaceSetBody.storeWord, storeI32_globals, paid_globals, lookup_globals]

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [arguments_globals]
  simp only [reserved, setGlobal, paid_globals]
  simp [Array.getElem?_modify, hg]

theorem acquired_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
  have h := InterfaceBorrow.calledAcquireStore_memory (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 (savedMemory p) (arguments_memory s op p hm)
  have hn : (1074904 : UInt32).toNat = (1074904 : Nat) := rfl
  simpa only [acquired, acquiredMemory, hn] using h

theorem high_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (InterfaceSetInstallTail.highStore (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p)).mems[p.memoryIndex]? =
      some (highMemory p) := by
  have hp : (paid (acquired s op p) op 4).mems[p.memoryIndex]? = some (acquiredMemory p) := by
    rw [paid_mems]; exact acquired_memory s op p hm
  have h := storeI32_memory (paid (acquired s op p) op 4) p.memoryIndex ((scratch p).toNat + 28)
    (acquiredMemory p) (readI32 (acquiredMemory p) ((scratch p).toNat + 12)) hp
  simpa only [InterfaceSetInstallTail.highStore, InterfaceSetBody.copiedWord, highMemory] using h

theorem low_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (InterfaceSetInstallTail.lowStore (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p)).mems[p.memoryIndex]? =
      some (lowMemory p) := by
  let high := InterfaceSetInstallTail.highStore (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p)
  have hp : (paid high op 5).mems[p.memoryIndex]? = some (highMemory p) := by
    rw [paid_mems]; exact high_memory s op p hm
  have h := storeI32_memory (paid high op 5) p.memoryIndex ((scratch p).toNat + 24)
    (highMemory p) (readI32 (highMemory p) ((scratch p).toNat + 8)) hp
  simpa only [InterfaceSetInstallTail.lowStore, InterfaceSetBody.copiedTeeWord, high, lowMemory, pointer] using h

theorem installed_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (installed s op p).mems[p.memoryIndex]? = some (installedMemory p) := by
  let before := InterfaceSetInstallTail.guardedStore (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p)
  have hp : before.mems[p.memoryIndex]? = some (lowMemory p) := by
    simpa only [before, InterfaceSetInstallTail.guardedStore, InterfaceInstall.guardAfter,
      InterfaceInstall.guardEntry, paid_mems, chargedStore] using low_memory s op p hm
  have h := twoWords_memory before op p.memoryIndex 4 0 (pointer p) p.vtable p.receiver (lowMemory p) hp
  simpa only [installed, InterfaceSetInstallTail.after, installedMemory, InterfaceInstall.installMemory,
    before, pointer, Nat.add_zero] using h

attribute [local irreducible] acquired installed arguments savedArguments lookupBefore looked
  InterfaceBorrow.calledAcquireStore InterfaceBorrow.acquireStore InterfaceBorrow.guardStore InterfaceBorrow.recordStore

private theorem global_projection (s : Store NearState) (index : Nat) (value : Value) :
    (setGlobal s index value).globals = s.globals.modify index (fun g => {g with value := value}) := rfl
private theorem charge_globals (s : Store NearState) (cost : Nat) : (chargedStore s cost).globals = s.globals := rfl
private theorem record_globals (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory) :
    (InterfaceBorrow.recordStore s op index out cell memory).globals = s.globals := by
  simp only [InterfaceBorrow.recordStore, storeI32_globals, paid_globals]

private theorem acquire_globals (s : Store NearState) (op gi mi : Nat) (sp out cell : UInt32)
    (memory : Memory) (global : GlobalInst) (hg : s.globals[gi]? = some global) (hv : global.value = .i32 sp) :
    (InterfaceBorrow.calledAcquireStore s op gi mi sp out cell memory).globals = s.globals := by
  rw [InterfaceBorrow.calledAcquireStore, InterfaceBorrow.acquireStore, global_projection, paid_globals,
    record_globals, InterfaceBorrow.guardStore_globals, InterfaceBorrow.reserved, global_projection,
    paid_globals, InterfaceBorrow.acquireEntryStore, charge_globals, charge_globals]
  have hrestore := StorePairCaller.setGlobal_restore s gi (.i32 (sp - 16)) global hg
  simpa only [setGlobal, hv] using hrestore

theorem acquired_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (acquired s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have harg := arguments_global s op p hg
  have he := acquire_globals (arguments s op p) op p.globalIndex p.memoryIndex (scratch p) (scratch p + 8)
    1074904 (savedMemory p) {p.global with value := .i32 (scratch p)} harg rfl
  rw [acquired, he]
  exact harg

private theorem install_globals (s : Store NearState) (op index : Nat) (scratch receiver vtable : UInt32)
    (m0 m1 m2 : Memory) :
    (InterfaceSetInstallTail.after s op index scratch receiver vtable m0 m1 m2).globals = s.globals := by
  simp only [InterfaceSetInstallTail.after, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord,
    InterfaceSetInstallTail.guardedStore, InterfaceInstall.guardAfter, InterfaceInstall.guardEntry,
    InterfaceSetInstallTail.lowStore, InterfaceSetInstallTail.highStore, InterfaceSetBody.copiedWord,
    InterfaceSetBody.copiedTeeWord, storeI32_globals, paid_globals, chargedStore]

theorem installed_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (installed s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [installed, install_globals]
  exact acquired_global s op p hg

end WNear.Proofs.InterfaceSetPhases
