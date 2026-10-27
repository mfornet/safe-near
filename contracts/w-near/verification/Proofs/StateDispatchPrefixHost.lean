import Proofs.StateDispatchPrefixFrame

/-! Functional host data is unchanged by the concrete lookup/acquisition prefix. -/
namespace WNear.Proofs.StateDispatchPrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] readI32 writeI32

private def hostView (seed host : NearState) :=
  {host with gas := seed.gas, gasProfile := seed.gasProfile}

private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    hostView seed (chargedStore s cost).host = hostView seed s.host := by
  simp only [hostView, chargedStore, chargeHost]

private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host = hostView seed s.host := by
  induction n with
  | zero => rfl
  | succ n ih => exact (view_charge seed (paid s op n) op).trans ih

private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (value : Value) :
    hostView seed (setGlobal s index value).host = hostView seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    hostView seed (storeI32 s index address memory value).host = hostView seed s.host := rfl

private theorem view_acquire (seed : NearState) (s : Store NearState) (op gi mi : Nat)
    (sp out cell : UInt32) (memory : Memory) :
    hostView seed (ValueReturnAcquire.calledAcquireStore s op gi mi sp out cell memory).host = hostView seed s.host := by
  simp only [ValueReturnAcquire.calledAcquireStore, ValueReturnAcquire.acquireStore,
    ValueReturnAcquire.acquireEntryStore, ValueReturnAcquire.recordStore, ValueReturnAcquire.guardStore,
    ValueReturnAcquire.calledIncrementStore, ValueReturnAcquire.incrementStore,
    ValueReturnAcquire.incrementEntryStore, ValueReturnAcquire.reserved,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore,
    ValueReturnBorrowCounters.swapEntryStore, view_paid, view_charge, view_global, view_store]

private theorem view_lookup (seed : NearState) (s : Store NearState) (op : Nat) :
    hostView seed (ValueReturnThreadLocal.indirectAfter s op).host = hostView seed s.host := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    view_paid, view_charge]

theorem acquired_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(acquired s op p).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  have h : hostView s.host (acquired s op p).host = hostView s.host s.host := by
    simp only [acquired, arguments, looked, lookupBefore, reserved, view_acquire, view_paid, view_lookup, view_global]
  exact h

end WNear.Proofs.StateDispatchPrefix
