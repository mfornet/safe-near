import Binary.ExpectResult
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules

/-! Exact accepted-branch effects of deployed f158, with sequential aliases.
The reserved stack slot is never accessed, so its UInt32 pointer may wrap. -/
namespace WNear.Proofs.ExpectResultState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas setGlobal_restore)

/-- Payload low word is read before any output write. -/
def lowWord (memory : Memory) (source : Nat) : UInt64 := readI64 memory (source + 4)

def lowMemory (memory : Memory) (out source : Nat) : Memory :=
  writeI64 memory out (lowWord memory source)

/-- Payload high word is read after writing the low output word. -/
def highWord (memory : Memory) (out source : Nat) : UInt32 :=
  readI32 (lowMemory memory out source) (source + 12)

def resultMemory (memory : Memory) (out source : Nat) : Memory :=
  writeI32 (lowMemory memory out source) (out + 8) (highWord memory out source)

def reserved (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid s op 5) globalIndex (.i32 (sp - 16))

def checked (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  paid (reserved s op globalIndex sp) op 5

def lowStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  storeI64 (paid (checked s op globalIndex sp) op 4) memoryIndex out.toNat memory
    (lowWord memory source.toNat)

def highStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  storeI32 (paid (lowStore s op globalIndex memoryIndex sp out source memory) op 8)
    memoryIndex (out.toNat + 8) (lowMemory memory out.toNat source.toNat)
    (highWord memory out.toNat source.toNat)

def finalStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  setGlobal (paid (highStore s op globalIndex memoryIndex sp out source memory) op 4)
    globalIndex (.i32 sp)

/-- Exact bytes and frame, even when output overwrites the source of the
second load. Only the twelve output bytes can change. -/
theorem resultMemory_spec (memory : Memory) (out source : Nat)
    (hwf : memory.wf) (hout : out + 12 ≤ memory.byteSize) :
    (resultMemory memory out source).wf ∧
    (resultMemory memory out source).byteSize = memory.byteSize ∧
    (resultMemory memory out source).max = memory.max ∧
    ∀ j, (resultMemory memory out source).read8 j =
      if out + 8 ≤ j ∧ j < out + 12 then
        UInt8.ofNat ((highWord memory out source).toNat >>> (8 * (j - (out + 8))))
      else if out ≤ j ∧ j < out + 8 then
        UInt8.ofNat ((lowWord memory source).toNat >>> (8 * (j - out)))
      else memory.read8 j := by
  have hb0 : out + 8 ≤ memory.byteSize := by omega
  have hl := writeI64_spec memory out (lowWord memory source) hwf hb0
  have hb1 : out + 8 + 4 ≤ (lowMemory memory out source).byteSize := by
    rw [show (lowMemory memory out source).byteSize = memory.byteSize from hl.2.1]
    omega
  have hh := writeI32_spec (lowMemory memory out source) (out + 8)
    (highWord memory out source) hl.1 hb1
  refine ⟨hh.1, hh.2.1.trans hl.2.1, hh.2.2.1.trans hl.2.2.1, ?_⟩
  intro j
  rw [show (resultMemory memory out source).read8 j = _ from hh.2.2.2 j]
  rw [show (lowMemory memory out source).read8 j = _ from hl.2.2.2 j]

theorem finalStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[memoryIndex]? =
      some (resultMemory memory out.toNat source.toNat) := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [finalStore, highStore, lowStore, checked, reserved, storeI64, storeI32,
    paid, chargedStore, setGlobal, resultMemory, hi]

theorem finalStore_other_memory (s : Store NearState) (op globalIndex memoryIndex other : Nat)
    (sp out source : UInt32) (memory : Memory) (hne : other ≠ memoryIndex) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[other]? = s.mems[other]? := by
  simp [finalStore, highStore, lowStore, checked, reserved, storeI64, storeI32,
    paid, chargedStore, setGlobal, Ne.symm hne]

/-- Stack-pointer restoration retains the entire original global array. -/
theorem finalStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) (global : GlobalInst)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (finalStore s op globalIndex memoryIndex sp out source memory).globals = s.globals := by
  have hr := setGlobal_restore s globalIndex (.i32 (sp - 16)) global hglobal
  rw [hsp] at hr
  simpa only [finalStore, highStore, lowStore, checked, reserved, storeI64, storeI32,
    paid, chargedStore, setGlobal] using hr

theorem finalStore_host_frame (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { (finalStore s op globalIndex memoryIndex sp out source memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [finalStore, highStore, lowStore, checked, reserved, storeI64, storeI32,
    paid, chargedStore, setGlobal, chargeHost]

theorem finalStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { finalStore s op globalIndex memoryIndex sp out source memory with
      mems := s.mems, globals := s.globals, host := s.host } = s := by
  simp only [finalStore, highStore, lowStore, checked, reserved, storeI64, storeI32,
    paid, chargedStore, setGlobal]

/-- All twenty-six paid accepted-branch instructions are accounted for,
without affecting promise reservations or the caller's remaining credits. -/
theorem finalStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out source : UInt32) (memory : Memory)
    (hgas : s.host.gas.Credits (26 * op + rest)) :
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.burnt =
      s.host.gas.burnt + 26 * op ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.promises =
      s.host.gas.promises ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (5 * op + (21 * op + rest)) := by
    convert hgas using 1; omega
  have b5 := paid_gas s op 5 (21 * op + rest) h0
  have c5 : (reserved s op globalIndex sp).host.gas.Credits (5 * op + (16 * op + rest)) := by
    have hc := paid_credits s op 5 (21 * op + rest) h0
    simpa only [reserved, setGlobal, show 5 * op + (16 * op + rest) = 21 * op + rest by omega] using hc
  have b10 := paid_gas (reserved s op globalIndex sp) op 5 (16 * op + rest) c5
  have c10 : (checked s op globalIndex sp).host.gas.Credits (4 * op + (12 * op + rest)) := by
    have hc := paid_credits (reserved s op globalIndex sp) op 5 (16 * op + rest) c5
    simpa only [checked, show 4 * op + (12 * op + rest) = 16 * op + rest by omega] using hc
  have b14 := paid_gas (checked s op globalIndex sp) op 4 (12 * op + rest) c10
  have c14 : (lowStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits
      (8 * op + (4 * op + rest)) := by
    have hc := paid_credits (checked s op globalIndex sp) op 4 (12 * op + rest) c10
    simpa only [lowStore, storeI64, show 8 * op + (4 * op + rest) = 12 * op + rest by omega] using hc
  have b22 := paid_gas (lowStore s op globalIndex memoryIndex sp out source memory)
    op 8 (4 * op + rest) c14
  have c22 : (highStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits
      (4 * op + rest) := by
    have hc := paid_credits (lowStore s op globalIndex memoryIndex sp out source memory)
      op 8 (4 * op + rest) c14
    simpa only [highStore, storeI32] using hc
  have b26 := paid_gas (highStore s op globalIndex memoryIndex sp out source memory) op 4 rest c22
  have c26 := paid_credits (highStore s op globalIndex memoryIndex sp out source memory) op 4 rest c22
  refine ⟨?_, ?_, c26⟩
  · change (paid (highStore s op globalIndex memoryIndex sp out source memory) op 4).host.gas.burnt = _
    dsimp only [checked, lowStore, highStore, reserved, setGlobal, storeI64, storeI32] at *
    omega
  · change (paid (highStore s op globalIndex memoryIndex sp out source memory) op 4).host.gas.promises = _
    dsimp only [checked, lowStore, highStore, reserved, setGlobal, storeI64, storeI32] at *
    omega

end WNear.Proofs.ExpectResultState
