import Bridge.Functions.SerdeIgnProgress

/-! # A closing-byte reserve for complete ignored-reader phase accounting

The reserve charges future closes for the current active depth. These are
arithmetic composition lemmas for the proved code segments; they do not yet
assemble the complete reader's control-flow and ownership invariant.
-/

namespace WNear.Binary.SerdeIgnBudget

open Wasm Wasm.Near WNear.IgnoreModel

/-- Every container phase has a current frame in addition to its saved frames. -/
def active (mode : Mode) (frames : List UInt8) : Nat :=
  match mode with
  | .val => frames.length
  | .opened _ | .cont _ => frames.length + 1

/-- Successful complete execution has a future byte available for every active frame. -/
theorem active_le_consumed (n : Nat) (mode : Mode) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody n mode frames bs = some (r, ops)) :
    active mode frames ≤ bs.length - r.length := by
  have hp := SerdeIgnProgress.run_consumed n mode frames bs r ops h
  cases mode <;> simp only [active] <;> omega

/-- The same reserve bound at the concrete reader's cursor. -/
theorem active_le_remaining (n : Nat) (mode : Mode) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i : Nat)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody n mode frames (bs.drop i) = some (r, ops)) :
    active mode frames ≤ bs.length - r.length - i := by
  have hp := SerdeIgnProgress.run_consumed n mode frames (bs.drop i) r ops h
  simp only [List.length_drop] at hp
  cases mode <;> simp only [active] <;> omega

/-- Retain 110 of the 470 operations per future byte for each active container. -/
def regular (cfg : WasmConfig) (fixed remaining depth : Nat) : Nat :=
  (fixed + 470 * remaining - 110 * depth) * cfg.regularOpCost

/-- Full-machine progress prevents truncation of the depth reserve. -/
theorem reserve_le (remaining depth fixed : Nat) (hd : depth ≤ remaining) :
    110 * depth ≤ fixed + 470 * remaining := by omega

/-- Adding the closing reserve recovers the original unchanged per-byte allowance. -/
theorem regular_reserve (cfg : WasmConfig) (fixed remaining depth : Nat) (hd : depth ≤ remaining) :
    regular cfg fixed remaining depth + 110 * depth * cfg.regularOpCost =
      (fixed + 470 * remaining) * cfg.regularOpCost := by
  have hh := reserve_le remaining depth fixed hd
  unfold regular
  rw [← Nat.add_mul, Nat.sub_add_cancel hh]

/-- Existing opened-phase allowances distinguish the array fast path from object keys. -/
def openedAllowance (f : UInt8) : Nat := if f = 0x5B then 250 else 200

/-- The existing member adapter reserves value entry on arrays; object keys pay it by consumed bytes. -/
def memberAllowance (f : UInt8) : Nat := if f = 0x5B then 75 else 0

/-- The concrete peek/guard/open block and six additional control operations fit a nested opening.
The traced growth charge is split separately using the actual returned capacity and allocator bound. -/
theorem opening_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth : Nat) (hd : depth + 1 ≤ remaining) :
    (390 + 96 * w) * cfg.regularOpCost + regular cfg (openedAllowance f) remaining (depth + 1) ≤
      regular cfg (if depth = 0 then 109 else 60) (w + 1 + remaining) depth := by
  have h : 390 + 96 * w + (openedAllowance f + 470 * remaining - 110 * (depth + 1)) ≤
      (if depth = 0 then 109 else 60) + 470 * (w + 1 + remaining) - 110 * depth := by
    unfold openedAllowance
    split <;> split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- A close restores the outer frame and its reserve without increasing the 470-per-byte charge.
The 355-operation allowance contains the proved peek/dispatch/pop costs and additional control work. -/
theorem closing_cost (cfg : WasmConfig) (w remaining depth : Nat) (hd : depth ≤ remaining) :
    (355 + 96 * w) * cfg.regularOpCost + regular cfg 0 remaining depth ≤
      regular cfg 0 (w + 1 + remaining) (depth + 1) := by
  have h : 355 + 96 * w + (0 + 470 * remaining - 110 * depth) ≤
      0 + 470 * (w + 1 + remaining) - 110 * (depth + 1) := by omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- First-member dispatch retains the reserve through either complete member adapter. -/
theorem first_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth : Nat) (hd : depth ≤ remaining) :
    (175 + 96 * w + memberAllowance f) * cfg.regularOpCost + regular cfg 0 remaining depth ≤
      regular cfg (openedAllowance f) (w + remaining) depth := by
  have h : 175 + 96 * w + memberAllowance f + (0 + 470 * remaining - 110 * depth) ≤
      openedAllowance f + 470 * (w + remaining) - 110 * depth := by
    unfold memberAllowance openedAllowance
    split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- An accepted comma pays the next-member adapter and retains the active-depth reserve. -/
theorem comma_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth : Nat) (hd : depth ≤ remaining) :
    (200 + 96 * w + memberAllowance f) * cfg.regularOpCost + regular cfg 0 remaining depth ≤
      regular cfg 0 (w + 1 + remaining) depth := by
  have h : 200 + 96 * w + memberAllowance f + (0 + 470 * remaining - 110 * depth) ≤
      0 + 470 * (w + 1 + remaining) - 110 * depth := by
    unfold memberAllowance
    split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- A scalar preserves the active-depth reserve while fitting its existing value-entry charge. -/
theorem scalar_cost (cfg : WasmConfig) (w consumed remaining depth : Nat)
    (hc : 0 < consumed) (hd : depth ≤ remaining) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 72) * cfg.regularOpCost + regular cfg 0 remaining depth ≤
      regular cfg 60 (w + consumed + remaining) depth := by
  have h : 125 + 96 * w + 7 + (470 * consumed - 72) + (0 + 470 * remaining - 110 * depth) ≤
      60 + 470 * (w + consumed + remaining) - 110 * depth := by omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

end WNear.Binary.SerdeIgnBudget
