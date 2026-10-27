import Proofs.DeallocateListState
import Proofs.DeallocateListClear

/-! Exact memory, code and gas frames of the actual two-link unlink path. -/
namespace WNear.Proofs.DeallocateListState
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] readI32 writeI32

def finalMemory (p : Layout) := DeallocateListClear.clearMemory (secondMemory p) p.pointer (finalRaw p)
def after (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateListClear.clearStore (secondAfter s op p) op p.memoryIndex (secondMemory p) p.pointer (finalRaw p)

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem write_memory (s : Store NearState) (op index destinationOffset sourceOffset : Nat)
    (destination source : UInt32) (memory : Memory) (hm : s.mems[index]? = some memory) :
    (DeallocateListWrite.writeStore s op index destinationOffset sourceOffset destination source memory).mems[index]? =
      some (writeI32 memory (destination.toNat + destinationOffset)
        (DeallocateListWrite.merged memory (destination.toNat + destinationOffset) (source.toNat + sourceOffset))) := by
  have initial : (paid s op 11).mems[index]? = some memory := by rw [paid_mems]; exact hm
  exact storeI32_memory (paid s op 11) index (destination.toNat + destinationOffset) memory
    (DeallocateListWrite.merged memory (destination.toNat + destinationOffset) (source.toNat + sourceOffset)) initial

theorem first_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (firstStore s op p).mems[p.memoryIndex]? = some (firstMemory p) := by
  have initial : (paid s op 17).mems[p.memoryIndex]? = some p.memory := by rw [paid_mems]; exact hm
  exact write_memory (paid s op 17) op p.memoryIndex 4 4 (firstLink p) p.pointer p.memory initial

theorem second_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (secondStore s op p).mems[p.memoryIndex]? = some (secondMemory p) := by
  have initial : (paid (firstStore s op p) op 8).mems[p.memoryIndex]? = some (firstMemory p) := by
    rw [paid_mems]; exact first_memory s op p hm
  simpa only [secondStore, secondMemory, Nat.add_zero] using
    write_memory (paid (firstStore s op p) op 8) op p.memoryIndex 0 0 (secondLink p) p.pointer (firstMemory p) initial

theorem secondAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (secondAfter s op p).mems[p.memoryIndex]? = some (secondMemory p) := by
  simpa only [secondAfter, paid_mems] using second_memory s op p hm

theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (after s op p).mems[p.memoryIndex]? = some (finalMemory p) :=
  DeallocateListClear.clearStore_memory (secondAfter s op p) op p.memoryIndex (secondMemory p) p.pointer (finalRaw p)
    (secondAfter_memory s op p hm)

theorem first_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (firstStore s op p).funcs = s.funcs ∧ (firstStore s op p).modules = s.modules ∧
    (firstStore s op p).tables = s.tables ∧ (firstStore s op p).globals = s.globals := by
  simp only [firstStore, DeallocateListWrite.writeStore, storeI32_funcs, storeI32_modules, storeI32_tables,
    storeI32_globals, paid, chargedStore, and_self]

theorem second_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (secondStore s op p).funcs = s.funcs ∧ (secondStore s op p).modules = s.modules ∧
    (secondStore s op p).tables = s.tables ∧ (secondStore s op p).globals = s.globals := by
  simpa only [secondStore, DeallocateListWrite.writeStore, storeI32_funcs, storeI32_modules, storeI32_tables,
    storeI32_globals, paid, chargedStore] using first_fields s op p

theorem secondAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (secondAfter s op p).funcs = s.funcs ∧ (secondAfter s op p).modules = s.modules ∧
    (secondAfter s op p).tables = s.tables ∧ (secondAfter s op p).globals = s.globals := by
  simpa only [secondAfter, paid, chargedStore] using second_fields s op p

theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧
    (after s op p).tables = s.tables ∧ (after s op p).globals = s.globals := by
  have c := DeallocateListClear.clearStore_fields (secondAfter s op p) op p.memoryIndex (secondMemory p) p.pointer (finalRaw p)
  have b := secondAfter_fields s op p
  exact ⟨c.1.trans b.1, c.2.1.trans b.2.1, c.2.2.1.trans b.2.2.1, c.2.2.2.trans b.2.2.2⟩

theorem after_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after, DeallocateListClear.clearStore, DeallocateListClear.highStore,
    secondAfter, secondStore, firstStore, DeallocateListWrite.writeStore,
    storeI32_host, paid, chargedStore, chargeHost]

/-- Original native bounds imply well-formedness and unchanged size of both
computed intermediate memories. -/
theorem memory_specs (p : Layout) (hw : p.memory.wf)
    (hb1 : (firstLink p).toNat + 8 ≤ p.memory.byteSize)
    (hb2 : (secondLink p).toNat + 4 ≤ (firstMemory p).byteSize) :
    (firstMemory p).wf ∧ (firstMemory p).byteSize = p.memory.byteSize ∧
    (secondMemory p).wf ∧ (secondMemory p).byteSize = p.memory.byteSize := by
  have first := writeI32_spec p.memory ((firstLink p).toNat + 4)
    (DeallocateListWrite.merged p.memory ((firstLink p).toNat + 4) (p.pointer.toNat + 4)) hw (by omega)
  have second := writeI32_spec (firstMemory p) (secondLink p).toNat
    (DeallocateListWrite.merged (firstMemory p) (secondLink p).toNat p.pointer.toNat) first.1 hb2
  exact ⟨first.1, first.2.1, second.1, second.2.1.trans first.2.1⟩

private theorem write_gas (s : Store NearState) (op index destinationOffset sourceOffset rest : Nat)
    (destination source : UInt32) (memory : Memory) (hc : s.host.gas.Credits (11 * op + rest)) :
    (DeallocateListWrite.writeStore s op index destinationOffset sourceOffset destination source memory).host.gas.burnt = s.host.gas.burnt + 11 * op ∧
    (DeallocateListWrite.writeStore s op index destinationOffset sourceOffset destination source memory).host.gas.promises = s.host.gas.promises ∧
    (DeallocateListWrite.writeStore s op index destinationOffset sourceOffset destination source memory).host.gas.Credits rest := by
  have h := paid_gas s op 11 rest hc
  have c := paid_credits s op 11 rest hc
  exact ⟨h.1, h.2, c⟩

theorem first_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (28 * op + rest)) :
    (firstStore s op p).host.gas.burnt = s.host.gas.burnt + 28 * op ∧
    (firstStore s op p).host.gas.promises = s.host.gas.promises ∧
    (firstStore s op p).host.gas.Credits rest := by
  have charge := paid_gas s op 17 (11 * op + rest) (hc.mono (by omega))
  have credits := paid_credits s op 17 (11 * op + rest) (hc.mono (by omega))
  have write := write_gas (paid s op 17) op p.memoryIndex 4 4 rest (firstLink p) p.pointer p.memory credits
  refine ⟨?_, write.2.1.trans charge.2, write.2.2⟩
  change (DeallocateListWrite.writeStore (paid s op 17) op p.memoryIndex 4 4 (firstLink p) p.pointer p.memory).host.gas.burnt = _
  rw [write.1, charge.1]; omega

theorem second_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (47 * op + rest)) :
    (secondStore s op p).host.gas.burnt = s.host.gas.burnt + 47 * op ∧
    (secondStore s op p).host.gas.promises = s.host.gas.promises ∧
    (secondStore s op p).host.gas.Credits rest := by
  have first := first_gas s op (19 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (firstStore s op p) op 8 (11 * op + rest) (first.2.2.mono (by omega))
  have credits := paid_credits (firstStore s op p) op 8 (11 * op + rest) (first.2.2.mono (by omega))
  have write := write_gas (paid (firstStore s op p) op 8) op p.memoryIndex 0 0 rest (secondLink p) p.pointer (firstMemory p) credits
  refine ⟨?_, write.2.1.trans (charge.2.trans first.2.1), write.2.2⟩
  change (DeallocateListWrite.writeStore (paid (firstStore s op p) op 8) op p.memoryIndex 0 0 (secondLink p) p.pointer (firstMemory p)).host.gas.burnt = _
  rw [write.1, charge.1, first.1]; omega

theorem secondAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (50 * op + rest)) :
    (secondAfter s op p).host.gas.burnt = s.host.gas.burnt + 50 * op ∧
    (secondAfter s op p).host.gas.promises = s.host.gas.promises ∧
    (secondAfter s op p).host.gas.Credits rest := by
  have second := second_gas s op (3 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (secondStore s op p) op 3 rest second.2.2
  have credits := paid_credits (secondStore s op p) op 3 rest second.2.2
  refine ⟨?_, charge.2.trans second.2.1, credits⟩
  change (paid (secondStore s op p) op 3).host.gas.burnt = _
  rw [charge.1, second.1]; omega

theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (61 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 61 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧
    (after s op p).host.gas.Credits rest := by
  have second := secondAfter_gas s op (11 * op + rest) p (hc.mono (by omega))
  have clear := DeallocateListClear.clearStore_gas (secondAfter s op p) op p.memoryIndex rest (secondMemory p) p.pointer (finalRaw p) second.2.2
  refine ⟨?_, clear.2.1.trans second.2.1, clear.2.2⟩
  change (DeallocateListClear.clearStore (secondAfter s op p) op p.memoryIndex (secondMemory p) p.pointer (finalRaw p)).host.gas.burnt = _
  rw [clear.1, second.1]; omega

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (61 * op + rest)) : (after s op p).host.gas.Credits rest :=
  (after_gas s op rest p hc).2.2

end WNear.Proofs.DeallocateListState
