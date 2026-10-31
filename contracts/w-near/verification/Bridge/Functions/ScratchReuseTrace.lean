import Bridge.Functions.ScratchMixedTrace
import Bridge.Functions.ScratchGrowthTrace

/-! Reusable parser growth charges and checked accepted-input domain bounds.
General parser instances and the pinned protocol ceiling remain separate obligations. -/

namespace WNear.Binary.ScratchReuseTrace
open Wasm Wasm.Near
open WNear.Binary

abbrev Batches := List (List UInt32)

def next (cap : UInt32) (ks : List UInt32) : UInt32 := (ScratchGrow.endState cap 0 ks).1

def Valid (cap : UInt32) : Batches → Prop
  | [] => cap.toNat < 2 ^ 28
  | ks :: batches => cap.toNat < 2 ^ 28 ∧ ScratchGrow.validTrace cap 0 ks ∧ Valid (next cap ks) batches

def endCap (cap : UInt32) : Batches → UInt32
  | [] => cap
  | ks :: batches => endCap (next cap ks) batches

def peak (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => max (ScratchGrow.endState cap 0 ks).2.toNat (peak (next cap ks) batches)

def growthCount (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.growthCount cap 0 ks + growthCount (next cap ks) batches

def endFreeBound (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => F
  | ks :: batches => endFreeBound (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks) batches

def walks (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.walkBounds F cap 0 ks +
      walks (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks) batches

def movedBytes (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.movedBytes cap 0 ks + movedBytes (next cap ks) batches

def allocatedBytes (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.allocatedBytes cap 0 ks + allocatedBytes (next cap ks) batches

def pages (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.growthPages cap 0 ks + pages (next cap ks) batches

def extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => ScratchGrow.extraCost cfg F cap 0 ks +
      extraCost cfg (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks) batches

theorem valid_cap (cap : UInt32) (batches : Batches) (hv : Valid cap batches) : cap.toNat < 2 ^ 28 := by
  cases batches with
  | nil => exact hv
  | cons ks batches => exact hv.1

theorem endFreeBound_eq (F : Nat) (cap : UInt32) (batches : Batches) :
    endFreeBound F cap batches = F + 2 * growthCount cap batches := by
  induction batches generalizing F cap with
  | nil => simp [endFreeBound, growthCount]
  | cons ks batches ih =>
    simp only [endFreeBound, ih, growthCount, ScratchGrow.endFreeBound_eq]
    omega

theorem walks_eq (F : Nat) (cap : UInt32) (batches : Batches) :
    walks F cap batches + growthCount cap batches =
      F * growthCount cap batches + growthCount cap batches * growthCount cap batches := by
  induction batches generalizing F cap with
  | nil => simp [walks, growthCount]
  | cons ks batches ih =>
    have h1 := ScratchGrow.walkBounds_eq F cap 0 ks
    have h2 := ih (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks)
    rw [ScratchGrow.endFreeBound_eq] at h2
    simp only [walks, growthCount, ScratchGrow.endFreeBound_eq]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at h2 ⊢
    rw [Nat.mul_comm (growthCount (next cap ks) batches) (ScratchGrow.growthCount cap 0 ks)]
    omega

theorem movedBytes_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    movedBytes cap batches + cap.toNat ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [movedBytes, endCap]
  | cons ks batches ih =>
    have h1 := ScratchGrow.movedBytes_capacity cap 0 ks hv.2.1
    have h2 := ih (next cap ks) hv.2.2
    simp only [movedBytes, endCap, next] at *
    omega

theorem allocatedBytes_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    allocatedBytes cap batches + 2 * cap.toNat ≤ 2 * (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [allocatedBytes, endCap]
  | cons ks batches ih =>
    have h1 := ScratchGrow.allocatedBytes_capacity cap 0 ks hv.2.1
    have h2 := ih (next cap ks) hv.2.2
    simp only [allocatedBytes, endCap, next] at *
    omega

theorem endCap_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    (endCap cap batches).toNat ≤ max cap.toNat (2 * peak cap batches + 8) := by
  induction batches generalizing cap with
  | nil => simp [endCap]
  | cons ks batches ih =>
    have h1 := ScratchGrow.endState_capacity cap 0 ks hv.2.1
    have h2 := ih (next cap ks) hv.2.2
    simp only [UInt32.toNat_zero, endCap, peak, next] at *
    omega

theorem movedBytes_peak (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    movedBytes cap batches ≤ 2 * peak cap batches + 8 := by
  have := movedBytes_capacity cap batches hv
  have := endCap_capacity cap batches hv
  omega

theorem allocatedBytes_peak (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    allocatedBytes cap batches ≤ 4 * peak cap batches + 16 := by
  have := allocatedBytes_capacity cap batches hv
  have := endCap_capacity cap batches hv
  omega

theorem pages_scaled (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    65536 * pages cap batches ≤ allocatedBytes cap batches + 66066 * growthCount cap batches := by
  induction batches generalizing cap with
  | nil => simp [pages, allocatedBytes, growthCount]
  | cons ks batches ih =>
    have h1 := ScratchGrow.growthPages_scaled cap 0 ks hv.2.1 (valid_cap (next cap ks) batches hv.2.2)
    have h2 := ih (next cap ks) hv.2.2
    simp only [pages, allocatedBytes, growthCount]
    omega

theorem extraCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (batches : Batches) :
    extraCost cfg F cap batches ≤
      (1790 * growthCount cap batches + walks F cap batches * 320 + 18 * movedBytes cap batches) * cfg.regularOpCost +
      growthCount cap batches * cfg.linearOpBaseCost + cfg.linearOpUnitCost * pages cap batches := by
  induction batches generalizing F cap with
  | nil => simp [extraCost, growthCount, walks, movedBytes, pages]
  | cons ks batches ih =>
    have h1 := ScratchGrow.extraCost_le cfg F cap 0 ks
    have h2 := ih (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks)
    simp only [extraCost, growthCount, walks, movedBytes, pages]
    simp only [Nat.add_mul, Nat.mul_add] at h1 h2 ⊢
    omega

def budget (cfg : WasmConfig) (F G P : Nat) : Nat :=
  (1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * P + 8)) * cfg.regularOpCost +
    G * cfg.linearOpBaseCost + cfg.linearOpUnitCost * ((4 * P + 16 + 66066 * G) / 65536)

def mixed (batches : Batches) : ScratchMixedTrace.Batches := batches.map .append

theorem mixed_valid (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    ScratchMixedTrace.Valid cap (mixed batches) := by
  induction batches generalizing cap with
  | nil => exact hv
  | cons ks batches ih => exact ⟨hv.1, hv.2.1, ih (next cap ks) hv.2.2⟩

theorem mixed_growthCount (cap : UInt32) (batches : Batches) :
    ScratchMixedTrace.growthCount cap (mixed batches) = growthCount cap batches := by
  induction batches generalizing cap with
  | nil => rfl
  | cons ks batches ih =>
    simpa only [mixed, List.map_cons, ScratchMixedTrace.growthCount,
      ScratchMixedTrace.Segment.growthCount, ScratchMixedTrace.Segment.next, growthCount, next] using
      congrArg (ScratchGrow.growthCount cap 0 ks + ·) (ih (next cap ks))

theorem mixed_peak (cap : UInt32) (batches : Batches) :
    ScratchMixedTrace.peak cap (mixed batches) = peak cap batches := by
  induction batches generalizing cap with
  | nil => rfl
  | cons ks batches ih =>
    simpa only [mixed, List.map_cons, ScratchMixedTrace.peak,
      ScratchMixedTrace.Segment.peak, ScratchMixedTrace.Segment.next, peak, next] using
      congrArg (max (ScratchGrow.endState cap 0 ks).2.toNat) (ih (next cap ks))

theorem mixed_extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (batches : Batches) :
    ScratchMixedTrace.extraCost cfg F cap (mixed batches) = extraCost cfg F cap batches := by
  induction batches generalizing F cap with
  | nil => rfl
  | cons ks batches ih =>
    simpa only [mixed, List.map_cons, ScratchMixedTrace.extraCost,
      ScratchMixedTrace.Segment.extraCost, ScratchMixedTrace.Segment.endFreeBound,
      ScratchMixedTrace.Segment.next, extraCost, next] using
      congrArg (ScratchGrow.extraCost cfg F cap 0 ks + ·)
        (ih (ScratchGrow.endFreeBound F cap 0 ks) (next cap ks))

theorem extraCost_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    extraCost cfg F cap batches ≤ budget cfg F (growthCount cap batches) (peak cap batches) := by
  have h := ScratchMixedTrace.extraCost_budget cfg F cap (mixed batches) (mixed_valid cap batches hv)
  rw [mixed_extraCost, mixed_growthCount, mixed_peak] at h
  exact h

end WNear.Binary.ScratchReuseTrace

namespace WNear.Binary.ScratchReuseTrace
open Wasm Wasm.Near
open WNear.Binary

theorem growthCount_doubles (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    cap.toNat * 2 ^ growthCount cap batches ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [growthCount, endCap]
  | cons ks batches ih =>
    have h1 := ScratchGrow.end_capacity_pow cap 0 ks hv.2.1
    have h2 := ih (next cap ks) hv.2.2
    simp only [growthCount, endCap]
    calc
      cap.toNat * 2 ^ (ScratchGrow.growthCount cap 0 ks + growthCount (next cap ks) batches) =
          (cap.toNat * 2 ^ ScratchGrow.growthCount cap 0 ks) * 2 ^ growthCount (next cap ks) batches := by
            rw [Nat.pow_add]; simp only [Nat.mul_assoc]
      _ ≤ (next cap ks).toNat * 2 ^ growthCount (next cap ks) batches :=
        Nat.mul_le_mul_right _ h1
      _ ≤ _ := h2

theorem growthCount_power (cap : UInt32) (batches : Batches) (hv : Valid cap batches)
    (hg : 0 < growthCount cap batches) : 8 * 2 ^ (growthCount cap batches - 1) ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [growthCount] at hg
  | cons ks batches ih =>
    by_cases hz : ScratchGrow.growthCount cap 0 ks = 0
    · have h2 := ih (next cap ks) hv.2.2 (by simpa only [growthCount, hz, Nat.zero_add] using hg)
      simpa only [growthCount, endCap, hz, Nat.zero_add] using h2
    · have h1 := ScratchGrow.growthCount_power cap 0 ks hv.2.1 (by omega)
      have h2 := growthCount_doubles (next cap ks) batches hv.2.2
      simp only [growthCount, endCap]
      have he : ScratchGrow.growthCount cap 0 ks + growthCount (next cap ks) batches - 1 =
          (ScratchGrow.growthCount cap 0 ks - 1) + growthCount (next cap ks) batches := by omega
      rw [he, Nat.pow_add, ← Nat.mul_assoc]
      exact (Nat.mul_le_mul_right _ h1).trans h2

theorem endCap_strict (cap : UInt32) (batches : Batches) (hv : Valid cap batches)
    (hg : 0 < growthCount cap batches) : cap.toNat < (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [growthCount] at hg
  | cons ks batches ih =>
    by_cases hz : ScratchGrow.growthCount cap 0 ks = 0
    · have h2 := ih (next cap ks) hv.2.2 (by simpa only [growthCount, hz, Nat.zero_add] using hg)
      have h1 := ScratchGrow.movedBytes_capacity cap 0 ks hv.2.1
      simp only [endCap, next] at *
      omega
    · have h1 := ScratchGrow.end_capacity_strict cap 0 ks hv.2.1 (by omega)
      have h2 := movedBytes_capacity (next cap ks) batches hv.2.2
      simp only [endCap, next] at *
      omega

/-- Clears cannot restart the geometric allocation series. -/
theorem growthCount_peak (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    growthCount cap batches = 0 ∨ 8 * 2 ^ (growthCount cap batches - 1) ≤ 2 * peak cap batches + 8 := by
  by_cases hz : growthCount cap batches = 0
  · exact Or.inl hz
  · have hp := growthCount_power cap batches hv (by omega)
    have hs := endCap_strict cap batches hv (by omega)
    have hc := endCap_capacity cap batches hv
    right
    omega

theorem budget_mono_peak (cfg : WasmConfig) (F G P Q : Nat) (hp : P ≤ Q) : budget cfg F G P ≤ budget cfg F G Q := by
  have hw := Nat.mul_le_mul_right cfg.regularOpCost
    (show 1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * P + 8) ≤
      1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * Q + 8) by omega)
  have hd : (4 * P + 16 + 66066 * G) / 65536 ≤ (4 * Q + 16 + 66066 * G) / 65536 := by omega
  have hh := Nat.mul_le_mul_left cfg.linearOpUnitCost hd
  unfold budget
  omega

end WNear.Binary.ScratchReuseTrace
