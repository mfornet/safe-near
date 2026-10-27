import Proofs.InterfaceLazyComplete

/-! Exact sequential memory of lazy initialization, without separation premises. -/
namespace WNear.Proofs.InterfaceLazyLayout
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceLazyState
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def savedMemory (p : InterfaceLazyState.Layout) :=
  writeI64 (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p))
    (p.scratch.toNat + 20) (oldLow p)

theorem saved_memory (s : Store NearState) (op : Nat) (p : InterfaceLazyState.Layout)
    (hm : s.mems[p.memoryIndex]? = some (statusMemory p)) :
    (saved s op p).mems[p.memoryIndex]? = some (savedMemory p) := by
  let high := InterfaceLazySaved.savedHigh s op p.memoryIndex p.scratch (oldHigh p) (statusMemory p)
  let middle := InterfaceSetBody.storeWord high op p.memoryIndex 16 p.scratch (oldStatus p)
    (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p))
  have hp : (paid s op 7).mems[p.memoryIndex]? = some (statusMemory p) := by rw [paid_mems]; exact hm
  have hh : high.mems[p.memoryIndex]? = some (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p)) :=
    storeI32_memory (paid s op 7) p.memoryIndex ((p.scratch + 16) + 12).toNat (statusMemory p) (oldHigh p) hp
  have hhp : (paid high op 3).mems[p.memoryIndex]? = some (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p)) := by
    rw [paid_mems]; exact hh
  have hs : middle.mems[p.memoryIndex]? = some (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p)) :=
    storeI32_memory (paid high op 3) p.memoryIndex (p.scratch.toNat + 16)
      (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p)) (oldStatus p) hhp
  have hsp : (paid middle op 3).mems[p.memoryIndex]? = some (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p)) := by
    rw [paid_mems]; exact hs
  have result := storeI64_memory (paid middle op 3) p.memoryIndex (p.scratch.toNat + 20)
    (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p)) (oldLow p) hsp
  simpa only [saved, InterfaceLazySaved.savedStore, InterfaceLazySaved.savedLow, high, middle, savedMemory] using result

theorem tail_memory (s : Store NearState) (op : Nat) (p : InterfaceLazyState.Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (InterfaceLazyTail.after s op p).mems[p.memoryIndex]? = some (savedMemory p) := by
  have h1 := high_memory s op p hm
  have h2 := word_memory (high s op p) op p h1
  have h3 := status_memory (word (high s op p) op p) op p h2
  have h4 := saved_memory (status (word (high s op p) op p) op p) op p h3
  simpa only [InterfaceLazyTail.after, InterfaceLazyTail.wordAfter, InterfaceLazyTail.statusAfter,
    InterfaceLazySavedTail.after, finalStore, InterfaceLazyFinish.finalStore, paid_mems, setGlobal] using h4

def finalMemory (p : InterfaceLazyComplete.Layout) := savedMemory (InterfaceLazyComplete.tailLayout p)

/-- Complete lazy-body post-memory, with no post-call lookup assumed. -/
theorem after_memory (s : Store NearState) (op : Nat) (p : InterfaceLazyComplete.Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (InterfaceLazyComplete.after s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  have hr : (InterfaceLazyComplete.reserved s op p).mems[p.memoryIndex]? = some p.memory := by
    simpa only [InterfaceLazyComplete.reserved, setGlobal, paid_mems] using hm
  have hinit := InterfaceLazyPrefix.after_memory (InterfaceLazyComplete.reserved s op p) op p.memoryIndex
    (InterfaceLazyComplete.scratch p) p.memory hr
  have initialMemory : (InterfaceLazyComplete.initialized s op p).mems[(InterfaceLazyComplete.tailLayout p).memoryIndex]? =
      some (InterfaceLazyComplete.tailLayout p).memory := by
    simpa only [InterfaceLazyComplete.initialized, InterfaceLazyComplete.tailLayout] using hinit
  have result := tail_memory (InterfaceLazyComplete.initialized s op p) op (InterfaceLazyComplete.tailLayout p) initialMemory
  simpa only [InterfaceLazyComplete.after, InterfaceLazyComplete.tailLayout, finalMemory] using result

end WNear.Proofs.InterfaceLazyLayout
