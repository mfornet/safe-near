import Bridge.Functions.ScratchGrow

/-!
# Amortized copying in the actual scratch reserve sequence

The charge counts the old capacity on every growth, matching the `memcpy` length
in `VecGrow.cost154`. Each growth at least doubles capacity. Telescoping capacity
increases bounds the total copied bytes by twice the final used length plus 8.
-/

namespace WNear.Binary.ScratchGrow

open Wasm Wasm.Near
open WNear.Binary.VecGrow (growCap_toNat)

/-- The final capacity and used length after a list of actual reserves/appends. -/
def endState (cap len : UInt32) : List UInt32 → UInt32 × UInt32
  | [] => (cap, len)
  | k :: ks => endState (capAfter cap len k) (len + k) ks

/-- Old capacities copied during growth; fitting appends copy no old allocation. -/
def movedBytes (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks => (if fits cap len k then 0 else cap.toNat) + movedBytes (capAfter cap len k) (len + k) ks

/-- Arithmetic side conditions required by the existing reserve contracts, at each append. -/
def validTrace (cap len : UInt32) : List UInt32 → Prop
  | [] => True
  | k :: ks => len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 30 ∧ len.toNat + k.toNat < 2 ^ 32 ∧
      validTrace (capAfter cap len k) (len + k) ks

/-- One reserve increases capacity by at least the number of old bytes it copies. -/
theorem moved_step (cap len k : UInt32) (hc : cap.toNat < 2 ^ 30) :
    (if fits cap len k then 0 else cap.toNat) + cap.toNat ≤ (capAfter cap len k).toNat := by
  unfold capAfter
  split
  · omega
  · rename_i hfit
    rw [growCap_toNat _ _ hc]
    omega

/-- A reserve's final capacity is bounded by the old capacity or twice its new used length plus 8. -/
theorem capAfter_used (cap len k : UInt32) (hc : cap.toNat < 2 ^ 30)
    (hadd : len.toNat + k.toNat < 2 ^ 32) :
    (capAfter cap len k).toNat ≤ max cap.toNat (2 * (len + k).toNat + 8) := by
  unfold capAfter
  split
  · omega
  · rename_i hfit
    have hsum : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
    rw [growCap_toNat _ _ hc, hsum]
    simp only [fits] at hfit
    omega

/-- The used length never decreases along a valid trace. -/
theorem endState_len (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    len.toNat ≤ (endState cap len ks).2.toNat := by
  induction ks generalizing cap len with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨_, _, hadd, hv⟩ := hv
    have hrec := ih (capAfter cap len k) (len + k) hv
    have hsum : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
    simp only [endState]
    omega

/-- Capacity increases pay for every byte of old allocation copied by reallocations. -/
theorem movedBytes_capacity (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    movedBytes cap len ks + cap.toNat ≤ (endState cap len ks).1.toNat := by
  induction ks generalizing cap len with
  | nil => simp [movedBytes, endState]
  | cons k ks ih =>
    obtain ⟨_, hc, _, hv⟩ := hv
    have hstep := moved_step cap len k hc
    have hrec := ih (capAfter cap len k) (len + k) hv
    simp only [movedBytes, endState]
    omega

/-- The capacity bound is stable across every append, even when appends have different lengths. -/
theorem endState_capacity (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    (endState cap len ks).1.toNat ≤ max cap.toNat (2 * (endState cap len ks).2.toNat + 8) := by
  induction ks generalizing cap len with
  | nil => simp [endState]
  | cons k ks ih =>
    obtain ⟨_, hc, hadd, hv⟩ := hv
    have hstep := capAfter_used cap len k hc hadd
    have hrec := ih (capAfter cap len k) (len + k) hv
    have hlen := endState_len (capAfter cap len k) (len + k) ks hv
    simp only [endState]
    omega

/-- **Amortized scratch copying:** all reallocation copies together are linear in final used bytes. -/
theorem movedBytes_linear (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    movedBytes cap len ks ≤ 2 * (endState cap len ks).2.toNat + 8 := by
  have hm := movedBytes_capacity cap len ks hv
  have hc := endState_capacity cap len ks hv
  omega

/-- The `memcpy` instruction charge of reallocations; first allocation has no old buffer. -/
def copyOps (cap len : UInt32) : List UInt32 → Nat
  | [] => 0
  | k :: ks =>
    (if fits cap len k then 0 else if cap = 0 then 0 else MemCpy.cost cap.toNat) +
      copyOps (capAfter cap len k) (len + k) ks

/-- Each nonempty old allocation pays for its copy's fixed overhead as well as its bytes. -/
theorem copyOps_moved (cap len : UInt32) (ks : List UInt32) :
    copyOps cap len ks ≤ 24 * movedBytes cap len ks := by
  induction ks generalizing cap len with
  | nil => simp [copyOps, movedBytes]
  | cons k ks ih =>
    have hstep : (if fits cap len k then 0 else if cap = 0 then 0 else MemCpy.cost cap.toNat) ≤
        24 * (if fits cap len k then 0 else cap.toNat) := by
      by_cases hf : fits cap len k
      · simp [hf]
      · simp only [if_neg hf]
        by_cases hc : cap = 0
        · simp [hc]
        · have hn : cap.toNat ≠ 0 := fun h => hc (UInt32.toNat_inj.mp (by simpa using h))
          simp only [if_neg hc, MemCpy.cost, if_neg hn]
          omega
    have hrec := ih (capAfter cap len k) (len + k)
    simp only [copyOps, movedBytes, Nat.mul_add]
    omega

/-- The entire reallocation-copy instruction charge is linear in final used bytes. -/
theorem copyOps_linear (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    copyOps cap len ks ≤ 48 * (endState cap len ks).2.toNat + 192 := by
  have hc := copyOps_moved cap len ks
  have hm := Nat.mul_le_mul_left 24 (movedBytes_linear cap len ks hv)
  omega

end WNear.Binary.ScratchGrow
