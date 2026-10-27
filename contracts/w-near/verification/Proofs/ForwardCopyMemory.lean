import NearVM.MeteredByteMemoryRules
import NearVM.MeteredScalarRules

/-! Functional semantics of deployed f951's forward byte-copy loop.
The recursion reads each byte after previous writes, retaining overlap behavior. -/
namespace WNear.Proofs.ForwardCopyMemory
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- One read/write at the current pointers, followed by the remaining bytes. -/
def forward (memory : Memory) (out source : Nat) : Nat → Memory
  | 0 => memory
  | n + 1 => forward (writeByte memory out (readByteWord memory source)) (out + 1) (source + 1) n

theorem spec (memory : Memory) (out source count : Nat)
    (hwf : memory.wf) (hbound : out + count ≤ memory.byteSize) :
    (forward memory out source count).wf ∧
    (forward memory out source count).byteSize = memory.byteSize ∧
    (forward memory out source count).max = memory.max ∧
    ∀ j, (j < out ∨ out + count ≤ j) → (forward memory out source count).read8 j = memory.read8 j := by
  induction count generalizing memory out source with
  | zero => exact ⟨hwf, rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    have hb : out + 1 ≤ memory.byteSize := by omega
    have hs := writeByte_spec memory out (readByteWord memory source) hwf hb
    have hn : out + 1 + n ≤ (writeByte memory out (readByteWord memory source)).byteSize := by
      rw [hs.2.1]; omega
    have ht := ih _ (out + 1) (source + 1) hs.1 hn
    refine ⟨ht.1, ht.2.1.trans hs.2.1, ht.2.2.1.trans hs.2.2.1, ?_⟩
    intro j hj
    have htail : j < out + 1 ∨ out + 1 + n ≤ j := by omega
    rw [forward, ht.2.2.2 j htail, hs.2.2.2 j]
    have hout : ¬(out ≤ j ∧ j < out + 1) := by omega
    simp only [hout, ↓reduceIte]

/-- Reading a byte into an i32 and storing its low byte retains that byte. -/
theorem byte_roundtrip (memory : Memory) (source : Nat) :
    UInt8.ofNat (readByteWord memory source).toNat = memory.read8 source := by
  have hb := (memory.read8 source).toNat_lt
  rw [readByteWord_eq, UInt32.toNat_ofNat']
  have hl : (memory.read8 source).toNat < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hl, UInt8.ofNat_toNat]

/-- The first write copies the current source byte exactly. -/
theorem first_byte (memory : Memory) (out source : Nat)
    (hwf : memory.wf) (hbound : out + 1 ≤ memory.byteSize) :
    (writeByte memory out (readByteWord memory source)).read8 out = memory.read8 source := by
  have hs := writeByte_spec memory out (readByteWord memory source) hwf hbound
  rw [hs.2.2.2 out]
  simp only [Nat.le_refl, Nat.lt_add_one, and_self, ↓reduceIte, Nat.sub_self,
    Nat.mul_zero, Nat.shiftRight_zero]
  exact byte_roundtrip memory source

/-- Disjoint copies read precisely the original source bytes. Overlapping
copies still use forward; no disjointness is imposed on its semantics. -/
theorem copied_bytes (memory : Memory) (out source count : Nat)
    (hwf : memory.wf) (hbound : out + count ≤ memory.byteSize)
    (hdisjoint : out + count ≤ source ∨ source + count ≤ out) :
    ∀ i, i < count → (forward memory out source count).read8 (out + i) = memory.read8 (source + i) := by
  induction count generalizing memory out source with
  | zero => intro i hi; omega
  | succ n ih =>
    have hb : out + 1 ≤ memory.byteSize := by omega
    have hs := writeByte_spec memory out (readByteWord memory source) hwf hb
    have hn : out + 1 + n ≤ (writeByte memory out (readByteWord memory source)).byteSize := by
      rw [hs.2.1]; omega
    have ht := spec (writeByte memory out (readByteWord memory source)) (out + 1) (source + 1) n hs.1 hn
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero]
      rw [forward, ht.2.2.2 out (Or.inl (by omega))]
      exact first_byte memory out source hwf hb
    | succ i =>
      have hd : out + 1 + n ≤ source + 1 ∨ source + 1 + n ≤ out + 1 := by omega
      have hr := ih _ (out + 1) (source + 1) hs.1 hn hd i (by omega)
      have ho : ¬(out ≤ source + 1 + i ∧ source + 1 + i < out + 1) := by omega
      simp only [hs.2.2.2, ho, ↓reduceIte] at hr
      simpa only [forward, Nat.add_assoc, Nat.add_comm 1 i] using hr

/-- Any complete word within a disjoint copy is the corresponding original
source word. This links byte-loop effects to the decoded-object fields. -/
theorem copied_word (memory : Memory) (out source count offset : Nat)
    (hwf : memory.wf) (hbound : out + count ≤ memory.byteSize)
    (hdisjoint : out + count ≤ source ∨ source + count ≤ out)
    (hoffset : offset + 8 ≤ count) :
    readI64 (forward memory out source count) (out + offset) = readI64 memory (source + offset) := by
  have hc := copied_bytes memory out source count hwf hbound hdisjoint
  have hm : (List.range 8).map (fun i => (forward memory out source count).read8 (out + offset + i)) =
      (List.range 8).map (fun i => memory.read8 (source + offset + i)) := by
    apply List.map_congr_left
    intro i hi
    have h := hc (offset + i) (by have := List.mem_range.mp hi; omega)
    simpa only [Nat.add_assoc] using h
  have hd := congrArg (fun bytes => UInt64.ofNat (Memory.decodeLE bytes)) hm
  simpa only [Memory.decodeLE, List.foldr_map, readI64] using hd

end WNear.Proofs.ForwardCopyMemory
