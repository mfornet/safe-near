import Bridge.Functions.ScratchMixedTrace
import Bridge.Functions.ScratchReuseTrace

namespace WNear.Binary.ScratchMixedTrace
open Wasm Wasm.Near
open WNear.Binary

namespace Segment

theorem growth_doubles (cap : UInt32) (seg : Segment) (hv : Valid cap seg) :
    cap.toNat * 2 ^ growthCount cap seg ≤ (next cap seg).toNat := by
  cases seg with
  | append chunks => exact ScratchGrow.end_capacity_pow cap 0 chunks hv
  | frames ops => simpa only [growthCount, next, Nat.mul_comm] using SerdeIgnTrace.growthCount_doubles cap 0 ops hv

theorem growth_power (cap : UInt32) (seg : Segment) (hv : Valid cap seg) (hg : 0 < growthCount cap seg) :
    8 * 2 ^ (growthCount cap seg - 1) ≤ (next cap seg).toNat := by
  cases seg with
  | append chunks => exact ScratchGrow.growthCount_power cap 0 chunks hv hg
  | frames ops => exact SerdeIgnTrace.growthCount_power cap 0 ops hv hg

end Segment

theorem growth_doubles (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    cap.toNat * 2 ^ growthCount cap batches ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [growthCount, endCap]
  | cons seg batches ih =>
    have h1 := Segment.growth_doubles cap seg hv.2.1
    have h2 := ih (Segment.next cap seg) hv.2.2
    simp only [growthCount, endCap]
    calc
      cap.toNat * 2 ^ (Segment.growthCount cap seg + growthCount (Segment.next cap seg) batches) =
          (cap.toNat * 2 ^ Segment.growthCount cap seg) * 2 ^ growthCount (Segment.next cap seg) batches := by
            rw [Nat.pow_add]; simp only [Nat.mul_assoc]
      _ ≤ (Segment.next cap seg).toNat * 2 ^ growthCount (Segment.next cap seg) batches :=
        Nat.mul_le_mul_right _ h1
      _ ≤ _ := h2

theorem growth_power (cap : UInt32) (batches : Batches) (hv : Valid cap batches)
    (hg : 0 < growthCount cap batches) : 8 * 2 ^ (growthCount cap batches - 1) ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [growthCount] at hg
  | cons seg batches ih =>
    by_cases hz : Segment.growthCount cap seg = 0
    · have h2 := ih (Segment.next cap seg) hv.2.2 (by simpa only [growthCount, hz, Nat.zero_add] using hg)
      simpa only [growthCount, endCap, hz, Nat.zero_add] using h2
    · have h1 := Segment.growth_power cap seg hv.2.1 (by omega)
      have h2 := growth_doubles (Segment.next cap seg) batches hv.2.2
      simp only [growthCount, endCap]
      have he : Segment.growthCount cap seg + growthCount (Segment.next cap seg) batches - 1 =
          (Segment.growthCount cap seg - 1) + growthCount (Segment.next cap seg) batches := by omega
      rw [he, Nat.pow_add, ← Nat.mul_assoc]
      exact (Nat.mul_le_mul_right _ h1).trans h2

/-- One global growth bound across all retained key, frame and account-string segments. -/
theorem growth_v86 (batches : Batches) (hv : Valid 0 batches) (hp : peak 0 batches ≤ 4194304) :
    growthCount 0 batches ≤ 21 := by
  by_contra hn
  have hpower := growth_power 0 batches hv (by omega)
  have hcap := endCap_capacity 0 batches hv
  have he : 21 ≤ growthCount 0 batches - 1 := by omega
  have hpow := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right (n := 2) (by decide) he)
  change 16777216 ≤ 8 * 2 ^ (growthCount 0 batches - 1) at hpow
  simp only [UInt32.toNat_zero] at hcap
  omega

/-- Exact requested-page bound across the complete retained mixed scratch trace. -/
theorem pages_v86 (batches : Batches) (hv : Valid 0 batches) (hp : peak 0 batches ≤ 4194304) :
    65536 * pages 0 batches ≤ 18164618 := by
  have hg := growth_v86 batches hv hp
  have ha := allocatedBytes_peak 0 batches hv
  have hs := pages_scaled 0 batches hv
  omega

/-- A valid account-id allocation requests at most one page. -/
theorem account_page (size : UInt32) (hs : size.toNat ≤ 64) :
    (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ 1 := by
  have hp := ScratchGrow.allocation_pages size (by omega)
  omega

end WNear.Binary.ScratchMixedTrace
