import Bridge.Functions.SerdeIgnPush
import Bridge.Functions.ScratchGrowthTrace

/-!
# Growth accounting for scratch frame stacks with pops

A frame pop decreases used length but keeps capacity. The append-only string
trace therefore cannot bound frame copying by final used length. This trace
uses the maximum reached length and charges every actual reserve growth,
including its changing free-list bound and requested pages.
-/

namespace WNear.Binary.SerdeIgnTrace

open Wasm Wasm.Near
open WNear.Binary.ScratchGrow (fits capAfter fAfter)

/-- `true` pushes one frame byte; `false` pops one present frame byte. -/
abbrev Op := Bool

/-- Pops preserve capacity; pushes use the actual reserve's capacity transition. -/
def nextCap (cap : UInt32) (len : Nat) (op : Op) : UInt32 :=
  if op then capAfter cap (UInt32.ofNat len) 1 else cap

def nextLen (len : Nat) (op : Op) : Nat := if op then len + 1 else len - 1

/-- Only a push without spare capacity allocates or copies. -/
def grows (cap : UInt32) (len : Nat) (op : Op) : Bool :=
  op && decide (¬ fits cap (UInt32.ofNat len) 1)

/-- Every state, including the final state, meets the general push's arithmetic bounds. -/
def Valid (cap : UInt32) (len : Nat) : List Op → Prop
  | [] => len ≤ cap.toNat ∧ cap.toNat < 2 ^ 27
  | op :: ops => len ≤ cap.toNat ∧ cap.toNat < 2 ^ 27 ∧
      (if op then len + 1 < 2 ^ 27 else 0 < len) ∧
      Valid (nextCap cap len op) (nextLen len op) ops

/-- Exact capacity and length at the end of the operation sequence. -/
def endState (cap : UInt32) (len : Nat) : List Op → UInt32 × Nat
  | [] => (cap, len)
  | op :: ops => endState (nextCap cap len op) (nextLen len op) ops

/-- High-water used length, including the initial state. -/
def peak (len : Nat) : List Op → Nat
  | [] => len
  | op :: ops => max len (peak (nextLen len op) ops)

def pushCount : List Op → Nat
  | [] => 0
  | op :: ops => (if op then 1 else 0) + pushCount ops

def growthCount (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if grows cap len op then 1 else 0) + growthCount (nextCap cap len op) (nextLen len op) ops

def movedBytes (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if grows cap len op then cap.toNat else 0) + movedBytes (nextCap cap len op) (nextLen len op) ops

def allocatedBytes (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if grows cap len op then (nextCap cap len op).toNat else 0) +
      allocatedBytes (nextCap cap len op) (nextLen len op) ops

/-- Requested allocator pages, rather than an assumption that every growth extends memory. -/
def pages (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if grows cap len op then
      (AllocNewCell.cellPages (AllocAlloc.wordsOf (nextCap cap len op)) 1).toNat else 0) +
      pages (nextCap cap len op) (nextLen len op) ops

/-- Free-list walk bounds evolve only at growing pushes. -/
def walks (F : Nat) (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if grows cap len op then F else 0) +
      walks (if grows cap len op then F + 2 else F) (nextCap cap len op) (nextLen len op) ops

/-- Exact remaining reserve charges from the proved push contracts. -/
def extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => 0
  | op :: ops => (if op then SerdeIgnReserve.growthCost cfg F cap (UInt32.ofNat len) 1 else 0) +
      extraCost cfg (if grows cap len op then F + 2 else F) (nextCap cap len op) (nextLen len op) ops

theorem nextCap_mono (cap : UInt32) (len : Nat) (op : Op) (hc : cap.toNat < 2 ^ 27) :
    cap.toNat ≤ (nextCap cap len op).toNat := by
  cases op
  · simp [nextCap]
  · have h := ScratchGrow.moved_step cap (UInt32.ofNat len) 1 (by omega)
    simpa only [nextCap, ite_true] using (show cap.toNat ≤ (capAfter cap (UInt32.ofNat len) 1).toNat by omega)

/-- Capacity increases cover every old byte copied, even across intervening pops. -/
theorem moved_step (cap : UInt32) (len : Nat) (op : Op) (hc : cap.toNat < 2 ^ 27) :
    (if grows cap len op then cap.toNat else 0) + cap.toNat ≤ (nextCap cap len op).toNat := by
  cases op
  · simp [nextCap, grows]
  · have h := ScratchGrow.moved_step cap (UInt32.ofNat len) 1 (by omega)
    by_cases hf : fits cap (UInt32.ofNat len) 1 <;>
      simpa only [nextCap, grows, Bool.true_and, hf, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] using h

/-- A growth's new allocation is at most twice the capacity increase. -/
theorem allocated_step (cap : UInt32) (len : Nat) (op : Op) (hc : cap.toNat < 2 ^ 27) :
    (if grows cap len op then (nextCap cap len op).toNat else 0) + 2 * cap.toNat ≤
      2 * (nextCap cap len op).toNat := by
  cases op
  · simp [nextCap, grows]
  · have h := ScratchGrow.allocated_step cap (UInt32.ofNat len) 1 (by omega)
    by_cases hf : fits cap (UInt32.ofNat len) 1 <;>
      simpa only [nextCap, grows, Bool.true_and, hf, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] using h

/-- The high-water length is bounded by the initial length plus the number of pushes. -/
theorem peak_le (len : Nat) (ops : List Op) : peak len ops ≤ len + pushCount ops := by
  induction ops generalizing len with
  | nil => simp [peak, pushCount]
  | cons op ops ih =>
    have h := ih (nextLen len op)
    cases op <;> simp only [peak, pushCount, nextLen, ite_true, Bool.false_eq_true, ite_false] at h ⊢ <;> omega

/-- Total copying is bounded by retained capacity, regardless of final used length. -/
theorem movedBytes_capacity (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    movedBytes cap len ops + cap.toNat ≤ (endState cap len ops).1.toNat := by
  induction ops generalizing cap len with
  | nil => simp [movedBytes, endState]
  | cons op ops ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have h := moved_step cap len op hc
    have hr := ih (nextCap cap len op) (nextLen len op) hv
    simp only [movedBytes, endState]
    omega

/-- Every requested allocation is paid by capacity increases; pops never reset this potential. -/
theorem allocatedBytes_capacity (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    allocatedBytes cap len ops + 2 * cap.toNat ≤ 2 * (endState cap len ops).1.toNat := by
  induction ops generalizing cap len with
  | nil => simp [allocatedBytes, endState]
  | cons op ops ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have h := allocated_step cap len op hc
    have hr := ih (nextCap cap len op) (nextLen len op) hv
    simp only [allocatedBytes, endState]
    omega

/-- Retained capacity depends on peak length, not on the number of later pops. -/
theorem endState_capacity (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    (endState cap len ops).1.toNat ≤ max cap.toNat (2 * peak len ops + 8) := by
  induction ops generalizing cap len with
  | nil => simp [endState, peak]
  | cons op ops ih =>
    obtain ⟨hl, hc, hop, hv⟩ := hv
    have hr := ih (nextCap cap len op) (nextLen len op) hv
    have hp : nextLen len op ≤ peak (nextLen len op) ops := by
      cases ops <;> simp [peak]
    cases op
    · simp only [nextCap, nextLen, Bool.false_eq_true, ite_false, endState, peak] at hr hp ⊢
      omega
    · have hlen : (UInt32.ofNat len).toNat = len := by simp; omega
      have hsum : (UInt32.ofNat len + 1).toNat = len + 1 := by rw [UInt32.toNat_add, hlen]; simp; omega
      have hs := ScratchGrow.capAfter_used cap (UInt32.ofNat len) 1 (by omega) (by rw [hlen]; simp; omega)
      rw [hsum] at hs
      simp only [nextCap, nextLen, ite_true, endState, peak] at hr hp ⊢
      omega

/-- A linear high-water copying bound also covers an initially grown scratch allocation. -/
theorem movedBytes_peak (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    movedBytes cap len ops ≤ 2 * peak len ops + 8 := by
  have hm := movedBytes_capacity cap len ops hv
  have hc := endState_capacity cap len ops hv
  omega

/-- Initial capacity cancels out of the total requested-capacity bound. -/
theorem allocatedBytes_peak (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    allocatedBytes cap len ops ≤ 4 * peak len ops + 16 := by
  have ha := allocatedBytes_capacity cap len ops hv
  have hc := endState_capacity cap len ops hv
  omega

/-- The same allocator-walk identity as append traces holds with arbitrary intervening pops. -/
theorem walks_eq (F : Nat) (cap : UInt32) (len : Nat) (ops : List Op) :
    walks F cap len ops + growthCount cap len ops =
      F * growthCount cap len ops + growthCount cap len ops * growthCount cap len ops := by
  induction ops generalizing F cap len with
  | nil => simp [walks, growthCount]
  | cons op ops ih =>
    have hr := ih (if grows cap len op then F + 2 else F) (nextCap cap len op) (nextLen len op)
    cases hg : grows cap len op <;> simp only [walks, growthCount, hg, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hr ⊢ <;> omega

/-- Page rounding and allocator headers are charged at each actual growth event. -/
theorem pages_scaled (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    65536 * pages cap len ops ≤ allocatedBytes cap len ops + 66066 * growthCount cap len ops := by
  induction ops generalizing cap len with
  | nil => simp [pages, allocatedBytes, growthCount]
  | cons op ops ih =>
    obtain ⟨_, _, _, hv⟩ := hv
    have hr := ih (nextCap cap len op) (nextLen len op) hv
    have hc : (nextCap cap len op).toNat < 2 ^ 27 := by
      cases ops with
      | nil => exact hv.2
      | cons => exact hv.2.1
    have hs := ScratchGrow.allocation_pages (nextCap cap len op) (by omega)
    cases hg : grows cap len op <;> simp only [pages, allocatedBytes, growthCount, hg,
      Bool.false_eq_true, ite_false, ite_true, Nat.mul_add, Nat.mul_one] at hr ⊢ <;> omega

/-- Every growing push at least doubles capacity and allocates at least eight bytes. -/
theorem growth_step (cap : UInt32) (len : Nat) (op : Op) (hc : cap.toNat < 2 ^ 27)
    (hg : grows cap len op = true) :
    8 ≤ (nextCap cap len op).toNat ∧ 2 * cap.toNat ≤ (nextCap cap len op).toNat := by
  cases op
  · simp [grows] at hg
  · have hf : ¬ fits cap (UInt32.ofNat len) 1 := by
      simpa only [grows, Bool.true_and, decide_eq_true_eq] using hg
    simp only [nextCap, ite_true, capAfter, if_neg hf]
    rw [VecGrow.growCap_toNat _ _ (by omega)]
    omega

/-- Pops do not interfere with the multiplicative capacity potential. -/
theorem growthCount_doubles (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops) :
    cap.toNat * 2 ^ growthCount cap len ops ≤ (endState cap len ops).1.toNat := by
  induction ops generalizing cap len with
  | nil => simp [growthCount, endState]
  | cons op ops ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have hr := ih (nextCap cap len op) (nextLen len op) hv
    cases hg : grows cap len op
    · have hs := nextCap_mono cap len op hc
      have hm := Nat.mul_le_mul_right (2 ^ growthCount (nextCap cap len op) (nextLen len op) ops) hs
      simp only [growthCount, hg, Bool.false_eq_true, ite_false, Nat.zero_add, endState]
      exact hm.trans hr
    · have hs := (growth_step cap len op hc hg).2
      have hm := Nat.mul_le_mul_right (2 ^ growthCount (nextCap cap len op) (nextLen len op) ops) hs
      simp only [growthCount, hg, ite_true, endState]
      calc
        cap.toNat * 2 ^ (1 + growthCount (nextCap cap len op) (nextLen len op) ops) =
            (2 * cap.toNat) * 2 ^ growthCount (nextCap cap len op) (nextLen len op) ops := by
              rw [Nat.pow_add]; simp; ac_rfl
        _ ≤ _ := hm.trans hr

/-- After the first growth, the event count is logarithmic in retained capacity. -/
theorem growthCount_power (cap : UInt32) (len : Nat) (ops : List Op) (hv : Valid cap len ops)
    (hg : 0 < growthCount cap len ops) :
    8 * 2 ^ (growthCount cap len ops - 1) ≤ (endState cap len ops).1.toNat := by
  induction ops generalizing cap len with
  | nil => simp [growthCount] at hg
  | cons op ops ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    cases hs : grows cap len op
    · have hr := ih (nextCap cap len op) (nextLen len op) hv
        (by simpa only [growthCount, hs, Bool.false_eq_true, ite_false, Nat.zero_add] using hg)
      simpa only [growthCount, hs, Bool.false_eq_true, ite_false, Nat.zero_add, endState] using hr
    · have hm := Nat.mul_le_mul_right (2 ^ growthCount (nextCap cap len op) (nextLen len op) ops)
        (growth_step cap len op hc hs).1
      have hr := growthCount_doubles (nextCap cap len op) (nextLen len op) ops hv
      simpa only [growthCount, hs, ite_true, Nat.add_sub_cancel_left, endState] using hm.trans hr

/-- Only pushes can grow; a pop contributes no event. -/
theorem growthCount_le_pushCount (cap : UInt32) (len : Nat) (ops : List Op) :
    growthCount cap len ops ≤ pushCount ops := by
  induction ops generalizing cap len with
  | nil => simp [growthCount, pushCount]
  | cons op ops ih =>
    have hr := ih (nextCap cap len op) (nextLen len op)
    cases op
    · simpa only [growthCount, pushCount, grows, Bool.false_and, Bool.false_eq_true, ite_false, Nat.zero_add] using hr
    · simp only [growthCount, pushCount, ite_true]
      split <;> omega

/-- The final free-list bound after exactly these reserve events. -/
def endFreeBound (F : Nat) (cap : UInt32) (len : Nat) : List Op → Nat
  | [] => F
  | op :: ops => endFreeBound (if grows cap len op then F + 2 else F)
      (nextCap cap len op) (nextLen len op) ops

theorem endFreeBound_eq (F : Nat) (cap : UInt32) (len : Nat) (ops : List Op) :
    endFreeBound F cap len ops = F + 2 * growthCount cap len ops := by
  induction ops generalizing F cap len with
  | nil => simp [endFreeBound, growthCount]
  | cons op ops ih =>
    simp only [endFreeBound, growthCount, ih]
    split <;> omega

/-- The real frame reserve's extra charge is smaller than the existing scratch extra-step charge. -/
theorem growthCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (len : Nat) :
    SerdeIgnReserve.growthCost cfg F cap (UInt32.ofNat len) 1 ≤
      ScratchGrow.extraStep cfg F cap (UInt32.ofNat len) 1 := by
  unfold SerdeIgnReserve.growthCost ScratchGrow.extraStep
  split <;> omega

/-- All reserve charges retain their allocator-walk, old-copy and requested-page contributions. -/
theorem extraCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (len : Nat) (ops : List Op) :
    extraCost cfg F cap len ops ≤
      (1790 * growthCount cap len ops + walks F cap len ops * 320 + 18 * movedBytes cap len ops) * cfg.regularOpCost +
      growthCount cap len ops * cfg.linearOpBaseCost + cfg.linearOpUnitCost * pages cap len ops := by
  induction ops generalizing F cap len with
  | nil => simp [extraCost, growthCount, walks, movedBytes, pages]
  | cons op ops ih =>
    have hr := ih (if grows cap len op then F + 2 else F) (nextCap cap len op) (nextLen len op)
    cases op
    · simpa only [extraCost, grows, Bool.false_and, Bool.false_eq_true, ite_false, growthCount, walks, movedBytes, pages, Nat.zero_add, Nat.zero_mul] using hr
    · by_cases hf : fits cap (UInt32.ofNat len) 1
      · simpa only [extraCost, grows, Bool.true_and, growthCount, walks, movedBytes, pages,
          SerdeIgnReserve.growthCost, hf, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true,
          Nat.zero_add, Nat.zero_mul] using hr
      · have hs := (growthCost_le cfg F cap len).trans (ScratchGrow.extraStep_le cfg F cap (UInt32.ofNat len) 1 hf)
        simp only [extraCost, grows, Bool.true_and, hf, not_false_eq_true, decide_true, ite_true,
          growthCount, walks, movedBytes, pages, nextCap] at hr hs ⊢
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, ← Nat.mul_assoc] at hr hs ⊢
        omega

/-- Closed reserve budget in the actual growth count and high-water frame count. -/
def budget (cfg : WasmConfig) (F G N : Nat) : Nat :=
  (1790 * G + (F * G + G * G) * 320 + 18 * (2 * N + 8)) * cfg.regularOpCost +
    G * cfg.linearOpBaseCost + cfg.linearOpUnitCost * ((4 * N + 16 + 66066 * G) / 65536)

/-- The complete traced charge fits the closed budget, with no gas-ceiling-dependent reserve. -/
theorem extraCost_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (len : Nat) (ops : List Op)
    (hv : Valid cap len ops) :
    extraCost cfg F cap len ops ≤ budget cfg F (growthCount cap len ops) (peak len ops) := by
  have he := extraCost_le cfg F cap len ops
  have hw := walks_eq F cap len ops
  have hm := movedBytes_peak cap len ops hv
  have ha := allocatedBytes_peak cap len ops hv
  have hp := pages_scaled cap len ops hv
  have hw' : walks F cap len ops ≤ F * growthCount cap len ops + growthCount cap len ops * growthCount cap len ops := by omega
  have hp' : pages cap len ops ≤ (4 * peak len ops + 16 + 66066 * growthCount cap len ops) / 65536 := by omega
  have hwork := Nat.mul_le_mul_right cfg.regularOpCost (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_right 320 hw') (1790 * growthCount cap len ops))
    (Nat.mul_le_mul_left 18 hm))
  have hpages := Nat.mul_le_mul_left cfg.linearOpUnitCost hp'
  exact he.trans (Nat.add_le_add (Nat.add_le_add_right hwork _) hpages)

end WNear.Binary.SerdeIgnTrace
