import Proofs.PanicAllocateState

/-! Derived state fields and credits for the actual zero-size f508 path. -/
namespace WNear.Proofs.PanicAllocateState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (arguments s op p).mems[p.memoryIndex]? = some p.memory := by
  simpa only [arguments, reserved, paid_mems, setGlobal] using hm

theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs = s.funcs ∧ (arguments s op p).modules = s.modules ∧ (arguments s op p).tables = s.tables := by
  simp only [arguments, reserved, paid, chargedStore, setGlobal, and_self]

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [arguments, paid_globals, reserved, setGlobal, paid_globals]
  simp [Array.getElem?_modify, hg]

theorem allocated_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (allocated s op p).mems[p.memoryIndex]? = some (allocatedMemory p) :=
  PanicAllocateZero.calledStore_memory (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory (arguments_memory s op p hm)

theorem allocated_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (allocated s op p).funcs = s.funcs ∧ (allocated s op p).modules = s.modules ∧ (allocated s op p).tables = s.tables := by
  have resource := PanicAllocateZero.calledStore_resources (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory
  have funcs := congrArg (fun t => t.funcs) resource
  have modules := congrArg (fun t => t.modules) resource
  have tables := congrArg (fun t => t.tables) resource
  simp only at funcs modules tables
  have initial := arguments_fields s op p
  exact ⟨funcs.trans initial.1, modules.trans initial.2.1, tables.trans initial.2.2⟩

theorem allocated_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (allocated s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have resource := PanicAllocateZero.calledStore_resources (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory
  have globals := congrArg (fun t => t.globals) resource
  simp only at globals
  change (PanicAllocateZero.calledStore (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory).globals[p.globalIndex]? = _
  rw [globals]
  exact arguments_global s op p hg

theorem low_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (low s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  have before : (paid (allocated s op p) op 4).mems[p.memoryIndex]? = some (allocatedMemory p) := by
    rw [paid_mems]; exact allocated_memory s op p hm
  have result := storeI32_memory (paid (allocated s op p) op 4) p.memoryIndex p.out.toNat (allocatedMemory p)
    (readI32 (allocatedMemory p) ((scratch p).toNat + 8)) before
  simpa only [low, PanicAllocateCopy.copyStore, lowMemory, Nat.add_zero] using result

theorem high_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (high s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have before : (paid (low s op p) op 4).mems[p.memoryIndex]? = some (lowMemory p) := by
    rw [paid_mems]; exact low_memory s op p hm
  exact storeI32_memory (paid (low s op p) op 4) p.memoryIndex (p.out.toNat + 4) (lowMemory p)
    (readI32 (lowMemory p) ((scratch p).toNat + 12)) before

theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  simpa only [after, setGlobal, paid_mems] using high_memory s op p hm

theorem low_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (low s op p).funcs = s.funcs ∧ (low s op p).modules = s.modules ∧ (low s op p).tables = s.tables := by
  simpa only [low, PanicAllocateCopy.copyStore, paid, chargedStore, storeI32_funcs, storeI32_modules, storeI32_tables] using allocated_fields s op p

theorem high_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (high s op p).funcs = s.funcs ∧ (high s op p).modules = s.modules ∧ (high s op p).tables = s.tables := by
  simpa only [high, PanicAllocateCopy.copyStore, paid, chargedStore, storeI32_funcs, storeI32_modules, storeI32_tables] using low_fields s op p

theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧ (after s op p).tables = s.tables := by
  simpa only [after, paid, chargedStore, setGlobal] using high_fields s op p

theorem low_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (low s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simpa only [low, PanicAllocateCopy.copyStore, storeI32_globals, paid_globals] using allocated_global s op p hg

theorem high_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (high s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simpa only [high, PanicAllocateCopy.copyStore, storeI32_globals, paid_globals] using low_global s op p hg

theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (after s op p).globals = s.globals := by
  have resource := PanicAllocateZero.calledStore_resources (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory
  have globals := congrArg (fun t => t.globals) resource
  simp only at globals
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  simp only [after, setGlobal, high, low, PanicAllocateCopy.copyStore, storeI32_globals, paid_globals, allocated]
  rw [globals]
  simpa only [arguments, reserved, paid_globals, setGlobal, scratch, UInt32.sub_add_cancel, hsp] using restore

theorem after_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after, high, low, PanicAllocateCopy.copyStore, allocated, PanicAllocateZero.calledStore,
    PanicAllocateZero.bodyStore, PanicAllocateZero.entered, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord,
    arguments, reserved, setGlobal, storeI32_host, paid, chargedStore, chargeHost]

theorem arguments_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (11 * op + rest)) :
    (arguments s op p).host.gas.burnt = s.host.gas.burnt + 11 * op ∧
    (arguments s op p).host.gas.promises = s.host.gas.promises ∧
    (arguments s op p).host.gas.Credits rest := by
  have h5 := paid_gas s op 5 (6 * op + rest) (hc.mono (by omega))
  have c5 : (reserved s op p).host.gas.Credits (6 * op + rest) := by
    simpa only [reserved, setGlobal] using paid_credits s op 5 (6 * op + rest) (hc.mono (show 5 * op + (6 * op + rest) ≤ 11 * op + rest by omega))
  have h6 := paid_gas (reserved s op p) op 6 rest c5
  have c6 := paid_credits (reserved s op p) op 6 rest c5
  have promises : (reserved s op p).host.gas.promises = s.host.gas.promises := by simpa only [reserved, setGlobal] using h5.2
  refine ⟨?_, h6.2.trans promises, c6⟩
  change (paid (reserved s op p) op 6).host.gas.burnt = _
  rw [h6.1]
  change (paid s op 5).host.gas.burnt + 6 * op = _
  rw [h5.1]; omega

theorem allocated_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (33 * op + rest)) :
    (allocated s op p).host.gas.burnt = s.host.gas.burnt + 33 * op ∧
    (allocated s op p).host.gas.promises = s.host.gas.promises ∧
    (allocated s op p).host.gas.Credits rest := by
  have args := arguments_gas s op (22 * op + rest) p (hc.mono (by omega))
  have call := PanicAllocateZero.calledStore_gas (arguments s op p) op p.memoryIndex rest (scratch p + 8) p.alignment p.memory args.2.2
  have credits := PanicAllocateZero.calledStore_credits (arguments s op p) op p.memoryIndex rest (scratch p + 8) p.alignment p.memory args.2.2
  refine ⟨?_, call.2.trans args.2.1, credits⟩
  change (PanicAllocateZero.calledStore (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory).host.gas.burnt = _
  rw [call.1, args.1]; omega

theorem low_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (37 * op + rest)) :
    (low s op p).host.gas.burnt = s.host.gas.burnt + 37 * op ∧
    (low s op p).host.gas.promises = s.host.gas.promises ∧
    (low s op p).host.gas.Credits rest := by
  have allocation := allocated_gas s op (4 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (allocated s op p) op 4 rest allocation.2.2
  have credits := paid_credits (allocated s op p) op 4 rest allocation.2.2
  refine ⟨?_, charge.2.trans allocation.2.1, credits⟩
  change (paid (allocated s op p) op 4).host.gas.burnt = _
  rw [charge.1, allocation.1]; omega

theorem high_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (41 * op + rest)) :
    (high s op p).host.gas.burnt = s.host.gas.burnt + 41 * op ∧
    (high s op p).host.gas.promises = s.host.gas.promises ∧
    (high s op p).host.gas.Credits rest := by
  have copied := low_gas s op (4 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (low s op p) op 4 rest copied.2.2
  have credits := paid_credits (low s op p) op 4 rest copied.2.2
  refine ⟨?_, charge.2.trans copied.2.1, credits⟩
  change (paid (low s op p) op 4).host.gas.burnt = _
  rw [charge.1, copied.1]; omega

theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (45 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 45 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧
    (after s op p).host.gas.Credits rest := by
  have copied := high_gas s op (4 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (high s op p) op 4 rest copied.2.2
  have credits := paid_credits (high s op p) op 4 rest copied.2.2
  refine ⟨?_, charge.2.trans copied.2.1, credits⟩
  change (paid (high s op p) op 4).host.gas.burnt = _
  rw [charge.1, copied.1]; omega

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (45 * op + rest)) : (after s op p).host.gas.Credits rest := (after_gas s op rest p hc).2.2

end WNear.Proofs.PanicAllocateState
