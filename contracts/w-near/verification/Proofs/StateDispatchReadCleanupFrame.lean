import Proofs.StateDispatchReadCleanup

/-! Concrete resource frames of the register-read-dispatch release and accepted branch. -/
namespace WNear.Proofs.StateDispatchReadCleanup
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] readI32 writeI32

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : fields (chargedStore s cost) = fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    fields (storeI32 s index address memory value) = fields s := rfl
private theorem fields_release (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    fields (ValueReturnBorrowCounters.releasedStore s op index counter memory) = fields s := by
  simp only [ValueReturnBorrowCounters.releasedStore,ValueReturnBorrowCounters.calledSwapStore,
    ValueReturnBorrowCounters.swapStore,ValueReturnBorrowCounters.swapEntryStore,fields_paid,fields_charge,fields_store]
private theorem fields_project (s t : Store NearState) (h : fields t = fields s) :
    t.funcs = s.funcs ∧ t.modules = s.modules ∧ t.tables = s.tables ∧ t.globals = s.globals :=
  ⟨congrArg (fun x => x.1) h,congrArg (fun x => x.2.1) h,
    congrArg (fun x => x.2.2.1) h,congrArg (fun x => x.2.2.2) h⟩

theorem after_fields (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (after s op index counter memory).funcs = s.funcs ∧
    (after s op index counter memory).modules = s.modules ∧
    (after s op index counter memory).tables = s.tables ∧
    (after s op index counter memory).globals = s.globals := by
  have h : fields (after s op index counter memory) = fields s := by
    simp only [after,released,releaseBefore,ValueReturnOuter.releaseAfter,ValueReturnOuter.nonnullEntry,
      fields_paid,fields_release,fields_charge]
  exact fields_project s _ h

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).mems = s.mems := rfl

theorem after_memory (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (after s op index counter memory).mems[index]? =
      some (writeI32 memory counter.toNat (readI32 memory counter.toNat + 4294967295)) := by
  unfold after released ValueReturnOuter.releaseAfter
  rw [mems_paid]
  apply ValueReturnBorrowCounters.releasedStore_memory
  rw [ValueReturnOuter.nonnullEntry,mems_charge,mems_charge,releaseBefore,mems_paid]
  exact hm

private def hostView (seed host : NearState) := {host with gas := seed.gas,gasProfile := seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    hostView seed (chargedStore s cost).host = hostView seed s.host := by
  simp only [hostView,chargedStore,chargeHost]
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host = hostView seed s.host := by
  induction n with
  | zero => rfl
  | succ n ih => exact (view_charge seed (paid s op n) op).trans ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    hostView seed (storeI32 s index address memory value).host = hostView seed s.host := rfl
private theorem view_release (seed : NearState) (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    hostView seed (ValueReturnBorrowCounters.releasedStore s op index counter memory).host = hostView seed s.host := by
  simp only [ValueReturnBorrowCounters.releasedStore,ValueReturnBorrowCounters.calledSwapStore,
    ValueReturnBorrowCounters.swapStore,ValueReturnBorrowCounters.swapEntryStore,view_paid,view_charge,view_store]

theorem after_host (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    {(after s op index counter memory).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  have h : hostView s.host (after s op index counter memory).host = hostView s.host s.host := by
    simp only [after,released,releaseBefore,ValueReturnOuter.releaseAfter,ValueReturnOuter.nonnullEntry,
      view_paid,view_release,view_charge]
  exact h

end WNear.Proofs.StateDispatchReadCleanup
