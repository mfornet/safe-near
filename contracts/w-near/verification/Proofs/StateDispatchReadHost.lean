import Proofs.StateDispatchReadState

/-! Functional host framing through the actual storage dispatch prefix. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] checked acquired

private def hostView (seed host : NearState) := {host with gas := seed.gas,gasProfile := seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host = hostView seed s.host := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (amount : Nat) :
    hostView seed (chargedStore s amount).host = hostView seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (index addr : Nat) (m : Memory) (v : UInt32) :
    hostView seed (storeI32 s index addr m v).host = hostView seed s.host := rfl

private theorem borrow_host (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) :
    hostView seed (StateDispatchReadBorrow.after s op index memory scratch).host = hostView seed s.host := by
  simp only [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    view_paid,view_charge,StateDispatchReadBorrow.low,StateDispatchReadBorrow.high,view_store]

theorem checked_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(checked s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  unfold checked
  have h : hostView s.host (acquired s op p).host = s.host := by
    simpa only [hostView,acquired] using StateDispatchPrefix.acquired_host s op p.toLayout
  exact (borrow_host s.host (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)).trans
    h
end WNear.Proofs.StateDispatchRead
