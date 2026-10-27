import Proofs.ValueReturnOuterState

/-! Computed memory lookups for the real outer path. Naming the generic paid
frame keeps phase stores opaque while proving these projection equalities. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
open WNear.Proofs.StorePairCaller (paid)
attribute [local irreducible] writeI32 storeI32 acquired high low acquiredMemory highMemory lowMemory

theorem paid_mems (s : Store NearState) (op count : Nat) : (paid s op count).mems = s.mems := by
  induction count with
  | zero => rfl
  | succ n ih => exact ih

theorem high_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (high s op p).mems[p.memoryIndex]? = some (highMemory p) := by
  have hpaid : (paid (acquired s op p) op 4).mems[p.memoryIndex]? = some (acquiredMemory p) := by
    rw [paid_mems]
    exact acquired_memory s op p hm
  have rule := storeI32_memory (paid (acquired s op p) op 4) p.memoryIndex ((scratch p).toNat + 12)
    (acquiredMemory p) (readI32 (acquiredMemory p) ((scratch p).toNat + 4))
  have result := rule hpaid
  simpa only [high, highMemory] using result

theorem low_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (low s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  have hpaid : (paid (high s op p) op 5).mems[p.memoryIndex]? = some (highMemory p) := by
    rw [paid_mems]
    exact high_memory s op p hm
  have rule := storeI32_memory (paid (high s op p) op 5) p.memoryIndex ((scratch p).toNat + 8)
    (highMemory p) (borrowed p)
  have result := rule hpaid
  simpa only [low, lowMemory] using result

theorem nonnullAfter_mems (s : Store NearState) (op : Nat) :
    (ValueReturnOuter.nonnullAfter s op).mems = s.mems := by
  unfold ValueReturnOuter.nonnullAfter
  rw [paid_mems]
  rfl

theorem dispatch_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (dispatchBefore s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  rw [dispatchBefore, nonnullAfter_mems, paid_mems, status, paid_mems]
  exact low_memory s op p hm

end WNear.Proofs.ValueReturnOuterBody
