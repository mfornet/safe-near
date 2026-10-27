import WasmLogic.MemoryLemmas

/-!
# What instantiation leaves in memory

Facts about the memory a module is instantiated with, from lemmas rather
than evaluation: the prepared memory has as many pages as the protocol's
`initial_memory_pages` (1024 for wNEAR), and a data segment is written into
it byte by byte, which the kernel cannot evaluate at that size.
-/

namespace NearLogic

open Wasm

theorem Memory.new_wf (min : Nat) (max : Option Nat) : (Memory.new min max).wf := by
  rw [Memory.wf_iff]
  intro i h
  left
  simp [Memory.new]

theorem Memory.new_byteSize (min : Nat) (max : Option Nat) :
    (Memory.new min max).byteSize = min * pageSize := by
  simp [Memory.byteSize, Memory.new]

theorem Memory.new_read8 (min : Nat) (max : Option Nat) (a : Nat) : (Memory.new min max).read8 a = 0 := by
  unfold Memory.read8 Memory.new
  simp only [Array.getElem?_replicate]
  split <;> simp_all

/-- A data segment written within bounds: what each byte reads. -/
theorem writeBytes_spec {m : Memory} (hwf : m.wf) {addr : Nat} {bytes : ByteArray}
    (hb : addr + bytes.size ≤ m.byteSize) :
    ∃ m', m.writeBytes addr bytes = some m' ∧ m'.wf ∧ m'.byteSize = m.byteSize ∧ m'.max = m.max ∧
      ∀ j, m'.read8 j = if addr ≤ j ∧ j < addr + bytes.size then bytes[j - addr]! else m.read8 j := by
  refine ⟨Memory.writeRun m addr bytes.size (fun i => bytes[i]!), ?_, ?_⟩
  · unfold Memory.writeBytes Memory.inBounds
    rw [if_pos (by simpa using hb)]
    rfl
  · exact Memory.writeRun_spec hwf hb _

end NearLogic
