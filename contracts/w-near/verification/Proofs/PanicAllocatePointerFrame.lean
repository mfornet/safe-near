import Proofs.PanicAllocatePointerState

/-! Derived frames and exact credits for f503's actual zero-size wrapper. -/
namespace WNear.Proofs.PanicAllocatePointerState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] PanicAllocateState.after

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs = s.funcs ∧ (arguments s op p).modules = s.modules ∧ (arguments s op p).tables = s.tables := by
  simp only [arguments, reserved, paid, chargedStore, setGlobal, and_self]

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some p.memory := by
  simpa only [arguments, reserved, paid_mems, setGlobal] using hm

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [arguments, paid_globals, reserved, setGlobal, paid_globals]
  simp [Array.getElem?_modify, hg]

theorem allocated_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (allocated s op p).funcs = s.funcs ∧ (allocated s op p).modules = s.modules ∧ (allocated s op p).tables = s.tables := by
  have h := PanicAllocateState.after_fields (PanicAllocateCall.entered (arguments s op p) op) op (inner p)
  have args := arguments_fields s op p
  simp only [PanicAllocateCall.entered, chargedStore] at h
  simpa only [allocated, PanicAllocateCall.callAfter, PanicAllocateCall.entered, chargedStore] using
    And.intro (h.1.trans args.1) (And.intro (h.2.1.trans args.2.1) (h.2.2.trans args.2.2))

theorem allocated_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (allocated s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have args := arguments_memory s op p hm
  have enteredMemory : (PanicAllocateCall.entered (arguments s op p) op).mems[(inner p).memoryIndex]? = some (inner p).memory := by
    simpa only [PanicAllocateCall.entered, chargedStore, inner] using args
  have index : (inner p).memoryIndex = p.memoryIndex := rfl
  simpa only [allocated, PanicAllocateCall.callAfter, finalMemory, index] using
    PanicAllocateState.after_memory (PanicAllocateCall.entered (arguments s op p) op) op (inner p) enteredMemory

theorem allocated_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (allocated s op p).globals = (arguments s op p).globals := by
  have enteredGlobal : (PanicAllocateCall.entered (arguments s op p) op).globals[(inner p).globalIndex]? = some (inner p).global := by
    simpa only [PanicAllocateCall.entered, chargedStore, inner] using arguments_global s op p hg
  have h := PanicAllocateState.after_globals (PanicAllocateCall.entered (arguments s op p) op) op (inner p) enteredGlobal rfl
  simpa only [allocated, PanicAllocateCall.callAfter, PanicAllocateCall.entered, chargedStore] using h

theorem allocated_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (allocated s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [allocated_globals s op p hg]
  exact arguments_global s op p hg

theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧ (after s op p).tables = s.tables := by
  simpa only [after, restored, checked, setGlobal, paid, chargedStore] using allocated_fields s op p

theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  simpa only [after, restored, checked, paid_mems, setGlobal] using allocated_memory s op p hm

theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (after s op p).globals = s.globals := by
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  simp only [after, restored, checked, paid_globals, setGlobal]
  rw [allocated_globals s op p hg]
  simpa only [arguments, reserved, paid_globals, setGlobal, scratch, UInt32.sub_add_cancel, hsp] using restore

theorem after_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  have h := PanicAllocateState.after_host (PanicAllocateCall.entered (arguments s op p) op) op (inner p)
  have masked := congrArg (fun host : NearState => {host with gas := s.host.gas, gasProfile := s.host.gasProfile}) h
  simp only at masked
  simpa only [after, restored, checked, allocated, PanicAllocateCall.callAfter,
    setGlobal, paid, PanicAllocateCall.entered, arguments, reserved, chargedStore, chargeHost] using masked

theorem arguments_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (10 * op + rest)) :
    (arguments s op p).host.gas.burnt = s.host.gas.burnt + 10 * op ∧
    (arguments s op p).host.gas.promises = s.host.gas.promises ∧
    (arguments s op p).host.gas.Credits rest := by
  have h5 := paid_gas s op 5 (5 * op + rest) (hc.mono (by omega))
  have c5 : (reserved s op p).host.gas.Credits (5 * op + rest) := by
    simpa only [reserved, setGlobal] using paid_credits s op 5 (5 * op + rest) (hc.mono (by omega))
  have h10 := paid_gas (reserved s op p) op 5 rest c5
  refine ⟨?_, h10.2.trans h5.2, paid_credits (reserved s op p) op 5 rest c5⟩
  change (paid (reserved s op p) op 5).host.gas.burnt = _
  rw [h10.1]
  change (paid s op 5).host.gas.burnt + 5 * op = _
  rw [h5.1]; omega

private theorem call508_gas (s : Store NearState) (op rest : Nat) (p : PanicAllocateState.Layout)
    (hc : s.host.gas.Credits (56 * op + rest)) :
    (PanicAllocateCall.callAfter s op p).host.gas.burnt = s.host.gas.burnt + 56 * op ∧
    (PanicAllocateCall.callAfter s op p).host.gas.promises = s.host.gas.promises ∧
    (PanicAllocateCall.callAfter s op p).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (55 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (45 * op + rest) (hop.2.2.2.mono (by omega))
  have h := PanicAllocateState.after_gas (PanicAllocateCall.entered s op) op rest p ha.2.2.2
  refine ⟨?_, h.2.1.trans (ha.2.2.1.trans hop.2.2.1), h.2.2⟩
  change (PanicAllocateState.after (PanicAllocateCall.entered s op) op p).host.gas.burnt = _
  rw [h.1]
  change (chargedStore (chargedStore s op) (10 * op)).host.gas.burnt + 45 * op = _
  have ba := ha.2.1
  change (chargedStore (chargedStore s op) (10 * op)).host.gas.burnt = (chargedStore s op).host.gas.burnt + 10 * op at ba
  have bo := hop.2.1
  change (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op at bo
  rw [ba, bo]; omega

theorem allocated_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (66 * op + rest)) :
    (allocated s op p).host.gas.burnt = s.host.gas.burnt + 66 * op ∧
    (allocated s op p).host.gas.promises = s.host.gas.promises ∧
    (allocated s op p).host.gas.Credits rest := by
  have args := arguments_gas s op (56 * op + rest) p (hc.mono (by omega))
  have call := call508_gas (arguments s op p) op rest (inner p) args.2.2
  refine ⟨?_, call.2.1.trans args.2.1, call.2.2⟩
  change (PanicAllocateCall.callAfter (arguments s op p) op (inner p)).host.gas.burnt = _
  rw [call.1, args.1]; omega

theorem checked_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (70 * op + rest)) :
    (checked s op p).host.gas.burnt = s.host.gas.burnt + 70 * op ∧
    (checked s op p).host.gas.promises = s.host.gas.promises ∧
    (checked s op p).host.gas.Credits rest := by
  have prev := allocated_gas s op (4 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (allocated s op p) op 4 rest prev.2.2
  refine ⟨?_, charge.2.trans prev.2.1, paid_credits (allocated s op p) op 4 rest prev.2.2⟩
  change (paid (allocated s op p) op 4).host.gas.burnt = _
  rw [charge.1, prev.1]; omega

theorem restored_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (74 * op + rest)) :
    (restored s op p).host.gas.burnt = s.host.gas.burnt + 74 * op ∧
    (restored s op p).host.gas.promises = s.host.gas.promises ∧
    (restored s op p).host.gas.Credits rest := by
  have prev := checked_gas s op (4 * op + rest) p (hc.mono (by omega))
  have charge := paid_gas (checked s op p) op 4 rest prev.2.2
  refine ⟨?_, charge.2.trans prev.2.1, paid_credits (checked s op p) op 4 rest prev.2.2⟩
  change (paid (checked s op p) op 4).host.gas.burnt = _
  rw [charge.1, prev.1]; omega

theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (75 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 75 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧
    (after s op p).host.gas.Credits rest := by
  have prev := restored_gas s op (op + rest) p (hc.mono (by omega))
  have charge := paid_gas (restored s op p) op 1 rest (prev.2.2.mono (by omega))
  have credits := paid_credits (restored s op p) op 1 rest (prev.2.2.mono (by omega))
  refine ⟨?_, charge.2.trans prev.2.1, credits⟩
  change (paid (restored s op p) op 1).host.gas.burnt = _
  rw [charge.1, prev.1]; omega

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (75 * op + rest)) : (after s op p).host.gas.Credits rest :=
  (after_gas s op rest p hc).2.2

end WNear.Proofs.PanicAllocatePointerState
