import Proofs.PanicHookSetSteps
import Proofs.ValueReturnOuterLayout

/-! Exact deployed first-install state, with the four writes kept sequential. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)

def lockedMemory (memory : Memory) := writeI32 memory 1074920 4294967295
def vtableMemory (memory : Memory) (vtable : UInt32) := writeI32 (lockedMemory memory) 1074928 vtable
def receiverMemory (memory : Memory) (receiver vtable : UInt32) := writeI32 (vtableMemory memory vtable) 1074924 receiver
def finalMemory (memory : Memory) (receiver vtable : UInt32) := writeI32 (receiverMemory memory receiver vtable) 1074920 0

def init (s : Store NearState) (op : Nat) := paid s op 4
def lockLoaded (s : Store NearState) (op : Nat) := paid (init s op) op 3
def locked (s : Store NearState) (op index : Nat) (memory : Memory) := stored (lockLoaded s op) op index 1074920 memory 4294967295
def lockPassed (s : Store NearState) (op index : Nat) (memory : Memory) := paid (locked s op index memory) op 2
def vtableLoaded (s : Store NearState) (op index : Nat) (memory : Memory) := paid (lockPassed s op index memory) op 3
def vtableStored (s : Store NearState) (op index : Nat) (memory : Memory) (vtable : UInt32) := stored (vtableLoaded s op index memory) op index 1074928 (lockedMemory memory) vtable
def receiverLoaded (s : Store NearState) (op index : Nat) (memory : Memory) (vtable : UInt32) := paid (vtableStored s op index memory vtable) op 3
def receiverStored (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) := stored (receiverLoaded s op index memory vtable) op index 1074924 (vtableMemory memory vtable) receiver
def unlocked (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) := stored (receiverStored s op index memory receiver vtable) op index 1074920 (receiverMemory memory receiver vtable) 0
def guarded (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) := paid (unlocked s op index memory receiver vtable) op 3
def after (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) := chargedStore (guarded s op index memory receiver vtable) op

/-- All four writes are in bounds under one original native span bound. -/
theorem memory_spec (memory : Memory) (receiver vtable : UInt32)
    (hwf : memory.wf) (hb : 1074936 ≤ memory.byteSize) :
    (lockedMemory memory).wf ∧ (lockedMemory memory).byteSize = memory.byteSize ∧
    readI32 (lockedMemory memory) 1074928 = readI32 memory 1074928 ∧
    (vtableMemory memory vtable).wf ∧ (vtableMemory memory vtable).byteSize = memory.byteSize ∧
    (receiverMemory memory receiver vtable).wf ∧ (receiverMemory memory receiver vtable).byteSize = memory.byteSize ∧
    (finalMemory memory receiver vtable).wf ∧ (finalMemory memory receiver vtable).byteSize = memory.byteSize := by
  have h1 := writeI32_spec memory 1074920 4294967295 hwf (by omega)
  change (lockedMemory memory).wf ∧ (lockedMemory memory).byteSize = memory.byteSize ∧
    (lockedMemory memory).max = memory.max ∧ _ at h1
  have hread : readI32 (lockedMemory memory) 1074928 = readI32 memory 1074928 := by
    apply LoadedValueReturnData.readI32_frame
    intro i hi
    unfold lockedMemory
    rw [h1.2.2.2]
    have hn : ¬ (1074920 ≤ 1074928 + i ∧ 1074928 + i < 1074920 + 4) := by omega
    exact ite_eq_right hn
  have b2 : 1074928 + 4 ≤ (lockedMemory memory).byteSize := by rw [h1.2.1]; omega
  have h2 := writeI32_spec (lockedMemory memory) 1074928 vtable h1.1 b2
  change (vtableMemory memory vtable).wf ∧ (vtableMemory memory vtable).byteSize = (lockedMemory memory).byteSize ∧ _ at h2
  have b3 : 1074924 + 4 ≤ (vtableMemory memory vtable).byteSize := by rw [h2.2.1,h1.2.1]; omega
  have h3 := writeI32_spec (vtableMemory memory vtable) 1074924 receiver h2.1 b3
  change (receiverMemory memory receiver vtable).wf ∧ (receiverMemory memory receiver vtable).byteSize = (vtableMemory memory vtable).byteSize ∧ _ at h3
  have b4 : 1074920 + 4 ≤ (receiverMemory memory receiver vtable).byteSize := by rw [h3.2.1,h2.2.1,h1.2.1]; omega
  have h4 := writeI32_spec (receiverMemory memory receiver vtable) 1074920 0 h3.1 b4
  exact ⟨h1.1,h1.2.1,hread,h2.1,h2.2.1.trans h1.2.1,h3.1,h3.2.1.trans (h2.2.1.trans h1.2.1),h4.1,h4.2.1.trans (h3.2.1.trans (h2.2.1.trans h1.2.1))⟩

/-- Every installed field is retained apart from the designated memory and gas. -/
theorem after_resources (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) :
    {after s op index memory receiver vtable with host := s.host, mems := s.mems} = s := by
  simp only [after, guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded,
    lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

/-- The functional host state is unchanged by the actual scalar sequence. -/
theorem after_functional_host (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) :
    {(after s op index memory receiver vtable).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after, guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded,
    lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore, chargeHost]

theorem init_host (s : Store NearState) (op : Nat) : (init s op).host = (paid s op 4).host := by
  simp only [init, paid, chargedStore]

theorem init_modules (s : Store NearState) (op : Nat) : (init s op).modules = s.modules := by
  simp only [init, paid, chargedStore]

theorem lockLoaded_host (s : Store NearState) (op : Nat) : (lockLoaded s op).host = (paid s op 7).host := by
  simp only [lockLoaded, init, paid, chargedStore]

theorem lockLoaded_modules (s : Store NearState) (op : Nat) : (lockLoaded s op).modules = s.modules := by
  simp only [lockLoaded, init, paid, chargedStore]

theorem locked_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (locked s op index memory).host = (paid s op 10).host := by
  simp only [locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem locked_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (locked s op index memory).modules = s.modules := by
  simp only [locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem lockPassed_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (lockPassed s op index memory).host = (paid s op 12).host := by
  simp only [lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem lockPassed_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (lockPassed s op index memory).modules = s.modules := by
  simp only [lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem vtableLoaded_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (vtableLoaded s op index memory).host = (paid s op 15).host := by
  simp only [vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem vtableLoaded_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) : (vtableLoaded s op index memory).modules = s.modules := by
  simp only [vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem vtableStored_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (vtable : UInt32) : (vtableStored s op index memory vtable).host = (paid s op 18).host := by
  simp only [vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem vtableStored_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (vtable : UInt32) : (vtableStored s op index memory vtable).modules = s.modules := by
  simp only [vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem receiverLoaded_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (vtable : UInt32) : (receiverLoaded s op index memory vtable).host = (paid s op 21).host := by
  simp only [receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem receiverLoaded_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (vtable : UInt32) : (receiverLoaded s op index memory vtable).modules = s.modules := by
  simp only [receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem receiverStored_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (receiverStored s op index memory receiver vtable).host = (paid s op 24).host := by
  simp only [receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem receiverStored_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (receiverStored s op index memory receiver vtable).modules = s.modules := by
  simp only [receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem unlocked_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (unlocked s op index memory receiver vtable).host = (paid s op 27).host := by
  simp only [unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem unlocked_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (unlocked s op index memory receiver vtable).modules = s.modules := by
  simp only [unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem guarded_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (guarded s op index memory receiver vtable).host = (paid s op 30).host := by
  simp only [guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem guarded_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (guarded s op index memory receiver vtable).modules = s.modules := by
  simp only [guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem after_host (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (after s op index memory receiver vtable).host = (paid s op 31).host := by
  simp only [after, guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem after_modules (s : Store NearState) (op : Nat) (index : Nat) (memory : Memory) (receiver : UInt32) (vtable : UInt32) : (after s op index memory receiver vtable).modules = s.modules := by
  simp only [after, guarded, unlocked, receiverStored, receiverLoaded, vtableStored, vtableLoaded, lockPassed, locked, lockLoaded, init, stored, storeI32, paid, chargedStore]

theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (receiver vtable : UInt32)
    (hc : s.host.gas.Credits (31 * op + rest)) : (after s op index memory receiver vtable).host.gas.Credits rest := by
  rw [after_host]
  exact paid_credits s op 31 rest hc

/-- The complete memory array differs only at the designated slot. -/
theorem after_mems (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) :
    (after s op index memory receiver vtable).mems = s.mems.set! index (finalMemory memory receiver vtable) := by
  simp only [after,guarded,unlocked,receiverStored,receiverLoaded,vtableStored,vtableLoaded,
    lockPassed,locked,lockLoaded,init,stored,storeI32,paid,chargedStore,
    Array.set!_eq_setIfInBounds,Array.setIfInBounds_setIfInBounds,finalMemory]

/-- The last store installs the complete sequential memory at the original index. -/
theorem after_memory (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32)
    (hm : s.mems[index]? = some memory) :
    (after s op index memory receiver vtable).mems[index]? = some (finalMemory memory receiver vtable) := by
  rw [after_mems,Array.set!_eq_setIfInBounds]
  exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hm).1

/-- Exact charged opcode cost and unchanged reserved gas. -/
theorem after_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (receiver vtable : UInt32)
    (hc : s.host.gas.Credits (31 * op + rest)) :
    (after s op index memory receiver vtable).host.gas.burnt = s.host.gas.burnt + 31 * op ∧
    (after s op index memory receiver vtable).host.gas.promises = s.host.gas.promises := by
  rw [after_host]
  exact paid_gas s op 31 rest hc

end WNear.Proofs.PanicHookSet
