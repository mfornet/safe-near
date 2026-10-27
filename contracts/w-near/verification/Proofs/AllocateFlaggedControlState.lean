import Proofs.AllocateFlaggedLinks
import Proofs.AllocateFlaggedTransfer
import Proofs.AllocateFlaggedGuard

/-! Deterministic gas/memory phases of the actual flags-two link control. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout taggedTeeStore maskStore)
open StorePairCaller (paid paid_credits)
attribute [local irreducible] readI32 writeI32

def afterBacklink (s : Store NearState) (op : Nat) := paid s op 17
def controlAfter (s : Store NearState) (op : Nat) (p : Layout) := transferred (paid (linkedStore (afterBacklink s op) op p) op 5) op p
def controlFrame (frame : CallFrame) (p : Layout) :=
  {backlinkFrame frame (readI32 p.memory (head p).toNat) (finish p) with
    locals:=(backlinkFrame frame (readI32 p.memory (head p).toNat) (finish p)).locals.set! 2 (.i32 (linkedWord p))}

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem linkedStore_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some (initializedMemory p)) :
    (linkedStore s op p).mems[p.memoryIndex]?=some (linkedMemory p) := by
  have first : (previousStore s op p).mems[p.memoryIndex]?=some (previousMemory p) := by
    unfold previousStore Allocate.taggedStore
    apply storeI32_memory
    rw [mems_paid]; exact hm
  have second : (unflaggedStore s op p).mems[p.memoryIndex]?=some (unflaggedMemory p) := by
    unfold unflaggedStore maskStore
    apply storeI32_memory
    rw [mems_paid]; exact first
  unfold linkedStore taggedTeeStore
  apply storeI32_memory
  rw [mems_paid]; exact second

theorem linkedStore_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (23*op+rest)) :
    (linkedStore s op p).host.gas.Credits rest := by
  have first : (previousStore s op p).host.gas.Credits (15*op+rest) := by
    unfold previousStore Allocate.taggedStore; rw [storeI32_host]
    exact paid_credits s op 8 _ (hc.mono (by omega))
  have second : (unflaggedStore s op p).host.gas.Credits (9*op+rest) := by
    unfold unflaggedStore maskStore; rw [storeI32_host]
    exact paid_credits _ op 6 _ (first.mono (by omega))
  unfold linkedStore taggedTeeStore
  rw [storeI32_host]
  exact paid_credits _ op 9 rest second

theorem transferred_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (12*op+rest)) :
    (transferred s op p).host.gas.Credits rest := by
  have first : (clearedStore s op p).host.gas.Credits (7*op+rest) := by
    unfold clearedStore clearStore; rw [storeI32_host]
    exact paid_credits s op 5 _ (hc.mono (by omega))
  have second : (flaggedStore s op p).host.gas.Credits (op+rest) := by
    unfold flaggedStore flagStore; rw [storeI32_host]
    exact paid_credits _ op 6 _ (first.mono (by omega))
  exact paid_credits _ op 1 rest (by simpa only [Nat.one_mul] using second)

theorem controlAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (57*op+rest)) :
    (controlAfter s op p).host.gas.Credits rest := by
  unfold controlAfter afterBacklink
  exact transferred_credits _ op rest p (paid_credits _ op 5 _ (linkedStore_credits _ op _ p
    (paid_credits s op 17 _ (hc.mono (by omega)))))

theorem controlAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some (initializedMemory p)) :
    (controlAfter s op p).mems[p.memoryIndex]?=some (flaggedMemory p) := by
  have linked := linkedStore_memory (afterBacklink s op) op p (by simpa only [afterBacklink,mems_paid] using hm)
  have clear : (clearedStore (paid (linkedStore (afterBacklink s op) op p) op 5) op p).mems[p.memoryIndex]?=some (clearedFlagMemory p) := by
    unfold clearedStore clearStore; apply storeI32_memory
    rw [mems_paid,mems_paid]; exact linked
  unfold controlAfter transferred
  rw [mems_paid]
  unfold flaggedStore flagStore
  apply storeI32_memory
  rw [mems_paid]; exact clear

theorem controlAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (controlAfter s op p).funcs=s.funcs ∧ (controlAfter s op p).modules=s.modules ∧
    (controlAfter s op p).tables=s.tables ∧ (controlAfter s op p).globals=s.globals := by
  simp only [controlAfter,transferred,flaggedStore,flagStore,clearedStore,clearStore,linkedStore,taggedTeeStore,unflaggedStore,
    maskStore,previousStore,Allocate.taggedStore,afterBacklink,paid,chargedStore,storeI32,and_self]
end WNear.Proofs.AllocateFlagged
