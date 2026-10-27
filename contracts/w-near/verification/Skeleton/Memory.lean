import Skeleton.Instantiation
import Wasm.MemoryLemmas

/-!
# The initialized data bytes, without materializing memory pages

All facts hold for any positive memory page count, including the runtime's
prepared memory, and any declared maximum. The proof uses the shared byte
API rather than reducing the 64 KiB page created by the first write.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near

private theorem new_wf (pages : Nat) (max : Option Nat) : (Memory.new pages max).wf := by
  rw [Memory.wf_iff]
  intro i hi
  left
  simp [Memory.new]

/-- Memory initialization is a six-byte run at offset zero. -/
theorem dataMemory_eq_writeRun (pages : Nat) (max : Option Nat) :
    dataMemory pages max = (Memory.new pages max).writeRun 0 6
      (fun i => module.datas[0]!.init[i]!) := by
  simp only [dataMemory, Memory.writeRun, Nat.zero_add]

/-- Initialization preserves memory size and maximum and writes only the six
specified bytes. The page representation remains well formed. -/
theorem dataMemory_spec (pages : Nat) (max : Option Nat) (hpages : 0 < pages) :
    (dataMemory pages max).wf ∧
    (dataMemory pages max).byteSize = pages * pageSize ∧
    (dataMemory pages max).max = max ∧
    ∀ i, (dataMemory pages max).read8 i =
      if i < 6 then module.datas[0]!.init[i]! else (Memory.new pages max).read8 i := by
  rw [dataMemory_eq_writeRun]
  have hbound : 0 + 6 ≤ (Memory.new pages max).byteSize := by
    simp only [Memory.byteSize, Memory.new, Array.size_replicate, pageSize]
    omega
  have hs := Memory.writeRun_spec (new_wf pages max) hbound
    (fun i => module.datas[0]!.init[i]!)
  simpa only [Memory.byteSize, Memory.new, Array.size_replicate, Nat.zero_add,
    Nat.zero_le, true_and, Nat.sub_zero] using hs

/-- The fixed key read by `storage_write`. -/
theorem dataMemory_key (pages : Nat) (max : Option Nat) (hpages : 0 < pages) :
    (dataMemory pages max).readList 0 1 = "k".toUTF8.toList := by
  unfold Memory.readList
  have hread := (dataMemory_spec pages max hpages).2.2.2
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    Nat.zero_add, hread, show (0 : Nat) < 6 by decide, ↓reduceIte]
  decide +kernel

/-- The fixed UTF-8 message read by `log_utf8`. -/
theorem dataMemory_saved (pages : Nat) (max : Option Nat) (hpages : 0 < pages) :
    (dataMemory pages max).readList 1 5 = "saved".toUTF8.toList := by
  unfold Memory.readList
  have hread := (dataMemory_spec pages max hpages).2.2.2
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, hread]
  simp only [Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  decide +kernel

end WNear.Skeleton
