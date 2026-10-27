import Proofs.StorePair
import Binary.StorePairCaller
import NearVM.MeteredScalarRules
import NearVM.MeteredWasmCall
import Proofs.StorePairReadback
import Proofs.StorePairAddresses

/-! Alias-aware memory and actual-body composition for deployed f414. -/
namespace WNear.Proofs.StorePairCaller
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePair
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

abbrev body := WNear.Binary.StorePairCaller.body

/-- Source words are captured before the scratch write, then copied to the
output after both scratch words have been read. The two regions may overlap. -/
def sequentialMemory (memory : Memory) (scratch out : Nat) (lo hi : UInt64) : Memory :=
  pairMemory (pairMemory memory scratch lo hi) out lo hi

/-- Sequential scratch/output writes retain all bytes outside their union,
without any source/output/scratch disjointness condition. -/
theorem sequentialMemory_frame (memory : Memory) (scratch out : Nat) (lo hi : UInt64)
    (hwf : memory.wf) (hscratch : scratch + 16 ≤ memory.byteSize) (hout : out + 16 ≤ memory.byteSize) :
    (sequentialMemory memory scratch out lo hi).wf ∧
    (sequentialMemory memory scratch out lo hi).byteSize = memory.byteSize ∧
    (sequentialMemory memory scratch out lo hi).max = memory.max ∧
    ∀ j, (j < scratch ∨ scratch + 16 ≤ j) → (j < out ∨ out + 16 ≤ j) →
      (sequentialMemory memory scratch out lo hi).read8 j = memory.read8 j := by
  have hs := pairMemory_spec memory scratch lo hi hwf hscratch
  have ho := pairMemory_spec (pairMemory memory scratch lo hi) out lo hi hs.1 (by rw [hs.2.1]; exact hout)
  refine ⟨ho.1, ho.2.1.trans hs.2.1, ho.2.2.1.trans hs.2.2.1, ?_⟩
  intro j hsj hoj
  rw [show (sequentialMemory memory scratch out lo hi).read8 j = _ from ho.2.2.2 j]
  rw [hs.2.2.2 j]
  simp only [show ¬(out ≤ j ∧ j < out + 8) by omega,
    show ¬(out + 8 ≤ j ∧ j < out + 16) by omega,
    show ¬(scratch ≤ j ∧ j < scratch + 8) by omega,
    show ¬(scratch + 8 ≤ j ∧ j < scratch + 16) by omega, ↓reduceIte]

/-- Repeated real opcode charges, with no functional store changes. -/
def paid (s : Store NearState) (op : Nat) : Nat → Store NearState
  | 0 => s
  | n + 1 => chargedStore (paid s op n) op

theorem paid_credits (s : Store NearState) (op count rest : Nat)
    (hc : s.host.gas.Credits (count * op + rest)) :
    (paid s op count).host.gas.Credits rest := by
  induction count generalizing rest with
  | zero => simpa only [paid, Nat.zero_mul, Nat.zero_add] using hc
  | succ n ih =>
    have h : s.host.gas.Credits (n * op + (op + rest)) := by simpa only [Nat.succ_mul, Nat.add_assoc] using hc
    exact charged_credits _ op rest (ih (op + rest) h)

/-- Real prologue store after five ordinary instruction charges. -/
def reserved (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid s op 5) globalIndex (.i32 (sp - 16))

/-- Both source words are loaded before the actual nested call. -/
def nestedEntry (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  chargedStore (chargedStore (paid (reserved s op globalIndex sp) op 7) op) (11 * op)

/-- Actual scratch write after the nested helper's six instructions. -/
def scratchStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp : UInt32) (memory : Memory) (lo hi : UInt64) : Store NearState :=
  pairStore (nestedEntry s op globalIndex sp) op memoryIndex (sp - 16).toNat memory lo hi

/-- f414 reloads both scratch words before either output write. -/
def outputHighStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) : Store NearState :=
  storeI64 (paid (scratchStore s op globalIndex memoryIndex sp memory lo hi) op 9)
    memoryIndex (out.toNat + 8) (pairMemory memory (sp - 16).toNat lo hi) hi

def outputStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) : Store NearState :=
  storeWord (outputHighStore s op globalIndex memoryIndex sp out memory lo hi) op memoryIndex out.toNat
    (writeI64 (pairMemory memory (sp - 16).toNat lo hi) (out.toNat + 8) hi) lo

/-- The active-body terminal store includes all 46 opcode units, both writes,
and restoration of the original stack pointer. Entry activation is separate. -/
def finalStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) : Store NearState :=
  setGlobal (paid (outputStore s op globalIndex memoryIndex sp out memory lo hi) op 4)
    globalIndex (.i32 sp)

/-- Repeated charges frame all resources except the host state. -/
theorem paid_resources (s : Store NearState) (op count : Nat) :
    { paid s op count with host := s.host } = s := by
  induction count with
  | zero => rfl
  | succ n ih => simpa only [paid, chargedStore] using ih

/-- Exact gas for a sequence of successful opcode charges. -/
theorem paid_gas (s : Store NearState) (op count rest : Nat)
    (hc : s.host.gas.Credits (count * op + rest)) :
    (paid s op count).host.gas.burnt = s.host.gas.burnt + count * op ∧
    (paid s op count).host.gas.promises = s.host.gas.promises := by
  induction count generalizing rest with
  | zero => simp [paid]
  | succ n ih =>
    have h : s.host.gas.Credits (n * op + (op + rest)) := by
      simpa only [Nat.succ_mul, Nat.add_assoc] using hc
    have hp := ih (op + rest) h
    have hr := paid_credits s op n (op + rest) h
    have hb := GasCounter.burn_credits (paid s op n).host.gas op rest hr
    change ((chargedStore (paid s op n) op).host.gas.burnt = _ ∧
      (chargedStore (paid s op n) op).host.gas.promises = _)
    have hb' : (chargedStore (paid s op n) op).host.gas.burnt =
        (paid s op n).host.gas.burnt + op := hb.2.1
    have hp' : (chargedStore (paid s op n) op).host.gas.promises =
        (paid s op n).host.gas.promises := hb.2.2.1
    simp only [Nat.succ_mul]
    constructor <;> omega

/-- The terminal store's installed memory is exactly the alias-aware sequential
scratch/output write; all source values were captured before these writes. -/
theorem finalStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).mems[memoryIndex]? =
      some (sequentialMemory memory (sp - 16).toNat out.toNat lo hi) := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [finalStore, outputStore, outputHighStore, scratchStore, nestedEntry, reserved,
    storeWord, pairStore, storeI64, charge3, paid, chargedStore, setGlobal,
    pairMemory, sequentialMemory, hi]

/-- Every other memory is unchanged. -/
theorem finalStore_other_memory (s : Store NearState) (op globalIndex memoryIndex other : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) (hne : other ≠ memoryIndex) :
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).mems[other]? = s.mems[other]? := by
  simp [finalStore, outputStore, outputHighStore, scratchStore, nestedEntry, reserved,
    storeWord, pairStore, storeI64, charge3, paid, chargedStore, setGlobal, Ne.symm hne]

/-- Host functional state is untouched by this helper, including its guest context. -/
theorem finalStore_host_frame (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) :
    { (finalStore s op globalIndex memoryIndex sp out memory lo hi).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [finalStore, outputStore, outputHighStore, scratchStore, nestedEntry, reserved,
    storeWord, pairStore, storeI64, charge3, paid, chargedStore, setGlobal, chargeHost]

/-- Modules, functions and tables, as well as every other store field outside
memory/global/host updates, retain their original values. -/
theorem finalStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) :
    { finalStore s op globalIndex memoryIndex sp out memory lo hi with
      mems := s.mems, globals := s.globals, host := s.host } = s := by
  simp only [finalStore, outputStore, outputHighStore, scratchStore, nestedEntry, reserved,
    storeWord, pairStore, storeI64, charge3, paid, chargedStore, setGlobal]

/-- Restoring an existing global value restores its entire instance, including
its type and mutability; no other global is touched. -/
theorem setGlobal_restore (s : Store NearState) (index : Nat) (temporary : Value)
    (global : GlobalInst) (hglobal : s.globals[index]? = some global) :
    (setGlobal (setGlobal s index temporary) index global.value).globals = s.globals := by
  apply Array.ext
  · simp [setGlobal]
  · intro j hj hk
    by_cases he : index = j
    · subst j
      have hi := (Array.getElem?_eq_some_iff.mp hglobal).1
      have hg := (Array.getElem?_eq_some_iff.mp hglobal).2
      simp [setGlobal, Array.getElem_modify, hg]
    · simp [setGlobal, Array.getElem_modify, he]

/-- Both stack-pointer updates restore the original global array exactly. -/
theorem finalStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64) (global : GlobalInst)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).globals = s.globals := by
  have hr := setGlobal_restore s globalIndex (.i32 (sp - 16)) global hglobal
  rw [hsp] at hr
  simpa only [finalStore, outputStore, outputHighStore, scratchStore, nestedEntry, reserved,
    storeWord, pairStore, storeI64, charge3, paid, chargedStore, setGlobal] using hr

/-- Full active-body accounting: 29 caller opcodes, eleven nested activation
units, and six nested body opcodes, with no lost promise reservation. -/
theorem finalStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out : UInt32) (memory : Memory) (lo hi : UInt64)
    (hgas : s.host.gas.Credits (46 * op + rest)) :
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).host.gas.burnt =
      s.host.gas.burnt + 46 * op ∧
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).host.gas.promises =
      s.host.gas.promises ∧
    (finalStore s op globalIndex memoryIndex sp out memory lo hi).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (5 * op + (41 * op + rest)) := by
    convert hgas using 1; omega
  have b5 := paid_gas s op 5 (41 * op + rest) h0
  have c5 : (reserved s op globalIndex sp).host.gas.Credits (7 * op + (34 * op + rest)) := by
    have hc := paid_credits s op 5 (41 * op + rest) h0
    simpa only [reserved, setGlobal, show 7 * op + (34 * op + rest) = 41 * op + rest by omega] using hc
  have b12 := paid_gas (reserved s op globalIndex sp) op 7 (34 * op + rest) c5
  have c12 : (paid (reserved s op globalIndex sp) op 7).host.gas.Credits
      (op + (33 * op + rest)) := by
    have hc := paid_credits (reserved s op globalIndex sp) op 7 (34 * op + rest) c5
    convert hc using 1; omega
  have b13 := GasCounter.burn_credits (paid (reserved s op globalIndex sp) op 7).host.gas
    op (33 * op + rest) c12
  have c13 : (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas.Credits
      (11 * op + (22 * op + rest)) := by
    simpa only [chargedStore, chargeHost, show 11 * op + (22 * op + rest) = 33 * op + rest by omega] using b13.2.2.2
  have b24 := GasCounter.burn_credits
    (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas
    (11 * op) (22 * op + rest) c13
  have c24 : (nestedEntry s op globalIndex sp).host.gas.Credits
      (6 * op + (16 * op + rest)) := by
    simpa only [nestedEntry, chargedStore, chargeHost, show 6 * op + (16 * op + rest) = 22 * op + rest by omega] using b24.2.2.2
  have b30 := pairStore_gas (nestedEntry s op globalIndex sp) op memoryIndex
    (sp - 16).toNat (16 * op + rest) memory lo hi c24
  have c27 : (nestedEntry s op globalIndex sp).host.gas.Credits
      (3 * op + (3 * op + (16 * op + rest))) := by
    convert c24 using 1; omega
  have c30 := storeWord_credits
    (storeWord (nestedEntry s op globalIndex sp) op memoryIndex ((sp - 16).toNat + 8) memory hi)
    op memoryIndex (sp - 16).toNat (16 * op + rest)
    (writeI64 memory ((sp - 16).toNat + 8) hi) lo
    (storeWord_credits (nestedEntry s op globalIndex sp) op memoryIndex
      ((sp - 16).toNat + 8) (3 * op + (16 * op + rest)) memory hi c27)
  have c30' : (scratchStore s op globalIndex memoryIndex sp memory lo hi).host.gas.Credits
      (9 * op + (7 * op + rest)) := by
    simpa only [scratchStore, pairStore, show 9 * op + (7 * op + rest) = 16 * op + rest by omega] using c30
  have b39 := paid_gas (scratchStore s op globalIndex memoryIndex sp memory lo hi)
    op 9 (7 * op + rest) c30'
  have c39 : (outputHighStore s op globalIndex memoryIndex sp out memory lo hi).host.gas.Credits
      (3 * op + (4 * op + rest)) := by
    have hc := paid_credits (scratchStore s op globalIndex memoryIndex sp memory lo hi)
      op 9 (7 * op + rest) c30'
    simpa only [outputHighStore, storeI64, show 3 * op + (4 * op + rest) = 7 * op + rest by omega] using hc
  have b42 := storeWord_gas (outputHighStore s op globalIndex memoryIndex sp out memory lo hi)
    op memoryIndex out.toNat (4 * op + rest)
    (writeI64 (pairMemory memory (sp - 16).toNat lo hi) (out.toNat + 8) hi) lo c39
  have c42 := storeWord_credits (outputHighStore s op globalIndex memoryIndex sp out memory lo hi)
    op memoryIndex out.toNat (4 * op + rest)
    (writeI64 (pairMemory memory (sp - 16).toNat lo hi) (out.toNat + 8) hi) lo c39
  have b46 := paid_gas (outputStore s op globalIndex memoryIndex sp out memory lo hi) op 4 rest c42
  have c46 := paid_credits (outputStore s op globalIndex memoryIndex sp out memory lo hi) op 4 rest c42
  have bb13 : (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas.burnt =
      (paid (reserved s op globalIndex sp) op 7).host.gas.burnt + op := b13.2.1
  have bp13 : (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas.promises =
      (paid (reserved s op globalIndex sp) op 7).host.gas.promises := b13.2.2.1
  have bb24 : (nestedEntry s op globalIndex sp).host.gas.burnt =
      (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas.burnt + 11 * op := b24.2.1
  have bp24 : (nestedEntry s op globalIndex sp).host.gas.promises =
      (chargedStore (paid (reserved s op globalIndex sp) op 7) op).host.gas.promises := b24.2.2.1
  refine ⟨?_, ?_, c46⟩
  · change (paid (outputStore s op globalIndex memoryIndex sp out memory lo hi) op 4).host.gas.burnt = _
    dsimp only [outputStore, outputHighStore, scratchStore, reserved, setGlobal, storeI64] at *
    omega
  · change (paid (outputStore s op globalIndex memoryIndex sp out memory lo hi) op 4).host.gas.promises = _
    dsimp only [outputStore, outputHighStore, scratchStore, reserved, setGlobal, storeI64] at *
    omega

end WNear.Proofs.StorePairCaller
