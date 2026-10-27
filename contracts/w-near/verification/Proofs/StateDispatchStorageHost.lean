import Proofs.StateDispatchStorageState

/-! Functional host framing through the actual storage dispatch prefix. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] checked StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low

private def hostView (seed host : NearState) := {host with gas := seed.gas,gasProfile := seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host = hostView seed s.host := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (amount : Nat) :
    hostView seed (chargedStore s amount).host = hostView seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (index addr : Nat) (m : Memory) (v : UInt32) :
    hostView seed (storeI32 s index addr m v).host = hostView seed s.host := rfl

private theorem borrow_host (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) :
    hostView seed (StateDispatchStorageBorrow.after s op index memory scratch).host = hostView seed s.host := by
  simp only [StateDispatchStorageBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    view_paid,view_charge,StateDispatchStorageBorrow.low,StateDispatchStorageBorrow.high,view_store]

theorem borrow_after_eq (s : Store NearState) (op : Nat) (p : Layout) :
    StateDispatchStorageBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p) = checked s op p := by
  simp only [StateDispatchStorageBorrow.after,StateDispatchStorageBorrow.low,StateDispatchStorageBorrow.high,StateDispatchStorageBorrow.pointer,
    StateDispatchStorageBorrow.highMemory,checked,low,StateDispatchLength.low,StateDispatchLength.high,StateDispatchLength.highMemory,StateDispatchLength.borrowed,StateDispatchLength.scratch]

theorem checked_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(checked s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  rw [←borrow_after_eq]
  have h : hostView s.host (acquired s op p).host = s.host := by
    simpa only [hostView,acquired,StateDispatchLength.acquired] using StateDispatchPrefix.acquired_host s op p.toLayout
  exact (borrow_host s.host (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)).trans
    h
end WNear.Proofs.StateDispatchStorage
