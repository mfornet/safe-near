import Bridge.Functions.ScratchAmortized
import Bridge.Functions.ScratchFast

/-!
# The remaining scratch-growth charge, along a concrete append sequence

Fitting push/append costs are already in the linear string budget. `extraStep`
reserves the additional control work and the existing growth contract only when
an append does not fit. The free-list bound increases by two at each such event.
-/

namespace WNear.Binary.ScratchGrow

open Wasm Wasm.Near
open WNear.Binary.VecGrow (growCap_toNat)

/-- The extra charge sufficient for every non-fitting push or slice append. -/
def extraStep (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  if fits cap len k then 0 else 220 * cfg.regularOpCost + costRes cfg F cap len k

/-- The growth-only reserve along the append sequence, with actual capacity/free-list updates. -/
def extraCost (cfg : WasmConfig) (F : Nat) (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => extraStep cfg F cap len k + extraCost cfg (fAfter F cap len k) (capAfter cap len k) (len + k) ks

/-- The number of appends that trigger allocation or growth. -/
def growthCount (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => (if fits cap len k then 0 else 1) + growthCount (capAfter cap len k) (len + k) ks

/-- The free-list bound after every reserve. -/
def endFreeBound (F : Nat) (cap len : UInt32) : List UInt32 → Nat
  | [] => F
  | k :: ks => endFreeBound (fAfter F cap len k) (capAfter cap len k) (len + k) ks

/-- The sum of the free-list bounds used by allocating reserve calls. -/
def walkBounds (F : Nat) (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => (if fits cap len k then 0 else F) +
      walkBounds (fAfter F cap len k) (capAfter cap len k) (len + k) ks

/-- Sum of new capacities allocated by reserve calls. -/
def allocatedBytes (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => (if fits cap len k then 0 else (capAfter cap len k).toNat) +
      allocatedBytes (capAfter cap len k) (len + k) ks

/-- Every fitting or growing slice append is paid by its fitting charge and the extra reserve. -/
theorem extCost_extra (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) :
    ScratchFast.extCost cfg F cap len k ≤
      180 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost + extraStep cfg F cap len k := by
  unfold ScratchFast.extCost extraStep costExt costApp
  split <;> omega

/-- The same extra reserve pays for a direct push or for its allocating branch. -/
theorem pushCost_extra (cfg : WasmConfig) (F : Nat) (cap len : UInt32) :
    ScratchFast.pushCost cfg F cap len ≤ 40 * cfg.regularOpCost + extraStep cfg F cap len 1 := by
  unfold ScratchFast.pushCost extraStep costApp
  split <;> omega

/-- Unicode's existing append contract is covered too. -/
theorem costExt_extra (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) :
    costExt cfg F cap len k ≤
      260 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost + extraStep cfg F cap len k := by
  unfold costExt costApp extraStep costRes
  split <;> omega

/-- The evolving allocator bound is determined exactly by the growth count. -/
theorem endFreeBound_eq (F : Nat) (cap len : UInt32) (ks : List UInt32) :
    endFreeBound F cap len ks = F + 2 * growthCount cap len ks := by
  induction ks generalizing F cap len with
  | nil => simp [endFreeBound, growthCount]
  | cons k ks ih =>
    simp only [endFreeBound, growthCount, ih, fAfter]
    split <;> omega

/-- Summed allocator walks retain their initial-bound term and the growth-count square.
This identity does not assert a gas bound independent of the initial heap. -/
theorem walkBounds_eq (F : Nat) (cap len : UInt32) (ks : List UInt32) :
    walkBounds F cap len ks + growthCount cap len ks =
      F * growthCount cap len ks + growthCount cap len ks * growthCount cap len ks := by
  induction ks generalizing F cap len with
  | nil => simp [walkBounds, growthCount]
  | cons k ks ih =>
    have hrec := ih (fAfter F cap len k) (capAfter cap len k) (len + k)
    by_cases hf : fits cap len k
    · simpa only [walkBounds, growthCount, fAfter, if_pos hf, Nat.zero_add] using hrec
    · simp only [walkBounds, growthCount, fAfter, if_neg hf] at hrec ⊢
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hrec ⊢
      omega

/-- Doubling capacity pays for the entire new allocation, by twice the capacity increase. -/
theorem allocated_step (cap len k : UInt32) (hc : cap.toNat < 2 ^ 30) :
    (if fits cap len k then 0 else (capAfter cap len k).toNat) + 2 * cap.toNat ≤
      2 * (capAfter cap len k).toNat := by
  by_cases hf : fits cap len k
  · simp [hf, capAfter]
  · simp only [if_neg hf, capAfter]
    rw [growCap_toNat _ _ hc]
    omega

/-- The sum of all new capacities telescopes, even when one append is much larger than the old buffer. -/
theorem allocatedBytes_capacity (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    allocatedBytes cap len ks + 2 * cap.toNat ≤ 2 * (endState cap len ks).1.toNat := by
  induction ks generalizing cap len with
  | nil => simp [allocatedBytes, endState]
  | cons k ks ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have hs := allocated_step cap len k hc
    have hr := ih (capAfter cap len k) (len + k) hv
    simp only [allocatedBytes, endState]
    omega

/-- Total requested capacity is linear in the final used length, with no dependence on append count. -/
theorem allocatedBytes_linear (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    allocatedBytes cap len ks ≤ 4 * (endState cap len ks).2.toNat + 16 := by
  have hs := allocatedBytes_capacity cap len ks hv
  have hc := endState_capacity cap len ks hv
  omega

/-- Pages charged by the allocator's growth contracts, counting only non-fitting reserves. -/
def growthPages (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => (if fits cap len k then 0 else
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (capAfter cap len k)) 1).toNat) +
      growthPages (capAfter cap len k) (len + k) ks

/-- One growth reserve, retaining the allocator walk and memory-growth fee explicitly. -/
theorem extraStep_le (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) (hf : ¬ fits cap len k) :
    extraStep cfg F cap len k ≤ (1790 + F * 320 + 18 * cap.toNat) * cfg.regularOpCost +
      cfg.linearOpBaseCost + cfg.linearOpUnitCost *
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (capAfter cap len k)) 1).toNat := by
  have hm : MemCpy.cost cap.toNat ≤ 18 * cap.toNat + 6 := by unfold MemCpy.cost; split <;> omega
  have hmc := Nat.mul_le_mul_right cfg.regularOpCost hm
  unfold extraStep costRes costGrow SerdeString.costA VecGrow.cost154 AllocWalk.cost310W
    AllocWalk.cost581W AllocWalk.walkCost AllocWalk.wc capAfter
  simp only [if_neg hf]
  split
  · simp only [Nat.add_mul, ← Nat.mul_assoc]
    omega
  · simp only [Nat.add_mul, ← Nat.mul_assoc] at hmc ⊢
    omega

/-- The complete remaining growth reserve, with every source of gas separated.
The allocator-walk term is not discarded or replaced by a constant heap bound. -/
theorem extraCost_le (cfg : WasmConfig) (F : Nat) (cap len : UInt32) (ks : List UInt32) :
    extraCost cfg F cap len ks ≤
      (1790 * growthCount cap len ks + walkBounds F cap len ks * 320 + 18 * movedBytes cap len ks) * cfg.regularOpCost +
      growthCount cap len ks * cfg.linearOpBaseCost + cfg.linearOpUnitCost * growthPages cap len ks := by
  induction ks generalizing F cap len with
  | nil => simp [extraCost, growthCount, walkBounds, movedBytes, growthPages]
  | cons k ks ih =>
    have hr := ih (fAfter F cap len k) (capAfter cap len k) (len + k)
    by_cases hf : fits cap len k
    · simpa only [extraCost, extraStep, growthCount, walkBounds, movedBytes, growthPages,
        fAfter, if_pos hf, Nat.zero_add] using hr
    · have hs := extraStep_le cfg F cap len k hf
      simp only [extraCost, growthCount, walkBounds, movedBytes, growthPages, fAfter, if_neg hf] at hr ⊢
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, ← Nat.mul_assoc] at hr hs ⊢
      omega

/-- The allocator's page request, including its minimum cell and rounding overhead. -/
theorem allocation_pages (size : UInt32) (hs : size.toNat < 2 ^ 28) :
    65536 * (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ size.toNat + 66066 := by
  have hw : (AllocAlloc.wordsOf size).toNat = (size.toNat + 3) / 4 := by
    unfold AllocAlloc.wordsOf
    simp; omega
  have hsmall : (AllocAlloc.wordsOf size).toNat < 2 ^ 29 := by rw [hw]; omega
  rw [AllocNewCell.cellPages_toNat _ _ hsmall (by decide),
    AllocNewCell.cellBytes_toNat _ _ hsmall (by decide), hw]
  simp only [UInt32.toNat_one]
  omega

/-- The sum of page requests is controlled by requested capacity and the number of growths. -/
theorem growthPages_scaled (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks)
    (hc : (endState cap len ks).1.toNat < 2 ^ 28) :
    65536 * growthPages cap len ks ≤ allocatedBytes cap len ks + 66066 * growthCount cap len ks := by
  induction ks generalizing cap len with
  | nil => simp [growthPages, allocatedBytes, growthCount]
  | cons k ks ih =>
    obtain ⟨_, _, _, hv⟩ := hv
    have hr := ih (capAfter cap len k) (len + k) hv (by simpa only [endState] using hc)
    have hnext := movedBytes_capacity (capAfter cap len k) (len + k) ks hv
    have hn : (capAfter cap len k).toNat < 2 ^ 28 := by
      simp only [endState] at hc
      omega
    by_cases hf : fits cap len k
    · simpa only [growthPages, allocatedBytes, growthCount, if_pos hf, Nat.zero_add] using hr
    · have hs := allocation_pages (capAfter cap len k) hn
      simp only [growthPages, allocatedBytes, growthCount, if_neg hf, Nat.mul_add] at hr ⊢
      omega

/-- Each growth doubles capacity, so the final capacity controls a power of the growth count. -/
theorem end_capacity_pow (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    cap.toNat * 2 ^ growthCount cap len ks ≤ (endState cap len ks).1.toNat := by
  induction ks generalizing cap len with
  | nil => simp [growthCount, endState]
  | cons k ks ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have hr := ih (capAfter cap len k) (len + k) hv
    by_cases hf : fits cap len k
    · simpa only [growthCount, if_pos hf, Nat.zero_add, endState, capAfter] using hr
    · have hs : 2 * cap.toNat ≤ (capAfter cap len k).toNat := by
        simp only [capAfter, if_neg hf]
        rw [growCap_toNat _ _ hc]
        omega
      have hm := Nat.mul_le_mul_right (2 ^ growthCount (capAfter cap len k) (len + k) ks) hs
      simp only [growthCount, if_neg hf, endState]
      calc
        cap.toNat * 2 ^ (1 + growthCount (capAfter cap len k) (len + k) ks) =
            (2 * cap.toNat) * 2 ^ growthCount (capAfter cap len k) (len + k) ks := by rw [Nat.pow_add]; simp; ac_rfl
        _ ≤ _ := hm
        _ ≤ _ := hr

/-- Any non-fitting reserve strictly increases capacity along an admissible trace. -/
theorem end_capacity_strict (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks)
    (hg : 0 < growthCount cap len ks) : cap.toNat < (endState cap len ks).1.toNat := by
  induction ks generalizing cap len with
  | nil => simp [growthCount] at hg
  | cons k ks ih =>
    obtain ⟨hu, hc, hadd, hv⟩ := hv
    by_cases hf : fits cap len k
    · have hr := ih (capAfter cap len k) (len + k) hv (by simpa only [growthCount, if_pos hf, Nat.zero_add] using hg)
      simpa only [endState, capAfter, if_pos hf] using hr
    · have hs : cap.toNat < (capAfter cap len k).toNat := by
        have hsum : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
        simp only [capAfter, if_neg hf]
        rw [growCap_toNat _ _ hc, hsum]
        simp only [fits] at hf
        omega
      have hr := movedBytes_capacity (capAfter cap len k) (len + k) ks hv
      simp only [endState]
      omega

/-- The first allocation has capacity at least eight; subsequent growths at least double it. -/
theorem growthCount_power (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks)
    (hg : 0 < growthCount cap len ks) :
    8 * 2 ^ (growthCount cap len ks - 1) ≤ (endState cap len ks).1.toNat := by
  induction ks generalizing cap len with
  | nil => simp [growthCount] at hg
  | cons k ks ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    by_cases hf : fits cap len k
    · have hr := ih (capAfter cap len k) (len + k) hv (by simpa only [growthCount, if_pos hf, Nat.zero_add] using hg)
      simpa only [growthCount, if_pos hf, Nat.zero_add, endState] using hr
    · have hs : 8 ≤ (capAfter cap len k).toNat := by
        simp only [capAfter, if_neg hf]
        rw [growCap_toNat _ _ hc]
        omega
      have hm := Nat.mul_le_mul_right (2 ^ growthCount (capAfter cap len k) (len + k) ks) hs
      have hr := end_capacity_pow (capAfter cap len k) (len + k) ks hv
      simpa only [growthCount, if_neg hf, Nat.add_sub_cancel_left, endState] using hm.trans hr

end WNear.Binary.ScratchGrow
