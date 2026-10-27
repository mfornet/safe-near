import Proofs.InterfaceBorrowState

/-! Pure field projections of the exclusive-borrow state's sequential writes. -/
namespace WNear.Proofs.InterfaceBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem guardStore_memory (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (guardStore s op index cell memory).mems[index]? = some (writeI32 memory cell.toNat 4294967295) := by
  let before := paid (takeEntryStore (paid s op 1) op) op 7
  have hbefore : before.mems[index]? = some memory := by
    simpa only [before, paid_mems, takeEntryStore, chargedStore] using hm
  have swapping : (ValueReturnBorrowCounters.swapEntryStore before op).mems[index]? = some memory := by
    simpa only [ValueReturnBorrowCounters.swapEntryStore, chargedStore] using hbefore
  have rule := ValueReturnBorrowCounters.swapStore_memory (ValueReturnBorrowCounters.swapEntryStore before op) op index cell 4294967295 memory
  have result := rule swapping
  simpa only [guardStore, calledTakeStore, takeStore, ValueReturnBorrowCounters.calledSwapStore, paid_mems, before] using result

theorem acquireStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (hm : s.mems[memoryIndex]? = some memory) :
    (acquireStore s op globalIndex memoryIndex sp out cell memory).mems[memoryIndex]? =
      some (recordMemory (writeI32 memory cell.toNat 4294967295) out cell) := by
  have hr : (reserved s op globalIndex sp).mems[memoryIndex]? = some memory := by
    simpa only [reserved, ValueReturnAcquire.reserved, setGlobal, paid_mems] using hm
  have hg := guardStore_memory (reserved s op globalIndex sp) op memoryIndex cell memory hr
  have recRule := ValueReturnAcquire.recordStore_memory (guardStore (reserved s op globalIndex sp) op memoryIndex cell memory)
    op memoryIndex out cell (writeI32 memory cell.toNat 4294967295)
  have recorded := recRule hg
  simpa only [acquireStore, setGlobal, paid_mems, recordStore, recordMemory, ValueReturnAcquire.recordStore, ValueReturnAcquire.recordMemory] using recorded

theorem calledAcquireStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (hm : s.mems[memoryIndex]? = some memory) :
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).mems[memoryIndex]? =
      some (recordMemory (writeI32 memory cell.toNat 4294967295) out cell) := by
  exact acquireStore_memory (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory hm

theorem guardStore_globals (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :
    (guardStore s op index cell memory).globals = s.globals := by
  simp only [guardStore, calledTakeStore, takeStore, takeEntryStore,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore,
    ValueReturnBorrowCounters.swapEntryStore, storeI32_globals, paid_globals, chargedStore]


end WNear.Proofs.InterfaceBorrow
