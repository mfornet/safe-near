import Bridge.Functions.SerdeIgnTrace

/-! One retained scratch allocation across string and ignored-frame segments.
This accounts for reserve growth; it does not discharge the full parser contract. -/

namespace WNear.Binary.ScratchMixedTrace
open Wasm Wasm.Near
open WNear.Binary

/-- Each completed segment clears used length, retaining capacity and allocator state. -/
inductive Segment where
  | append (chunks : List UInt32)
  | frames (ops : List Bool)

namespace Segment

def next (cap : UInt32) : Segment → UInt32
  | .append ks => (ScratchGrow.endState cap 0 ks).1
  | .frames ops => (SerdeIgnTrace.endState cap 0 ops).1

def peak (cap : UInt32) : Segment → Nat
  | .append ks => (ScratchGrow.endState cap 0 ks).2.toNat
  | .frames ops => SerdeIgnTrace.peak 0 ops

def growthCount (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.growthCount cap 0 ks
  | .frames ops => SerdeIgnTrace.growthCount cap 0 ops

def movedBytes (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.movedBytes cap 0 ks
  | .frames ops => SerdeIgnTrace.movedBytes cap 0 ops

def allocatedBytes (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.allocatedBytes cap 0 ks
  | .frames ops => SerdeIgnTrace.allocatedBytes cap 0 ops

def pages (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.growthPages cap 0 ks
  | .frames ops => SerdeIgnTrace.pages cap 0 ops

def endFreeBound (F : Nat) (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.endFreeBound F cap 0 ks
  | .frames ops => SerdeIgnTrace.endFreeBound F cap 0 ops

def walks (F : Nat) (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.walkBounds F cap 0 ks
  | .frames ops => SerdeIgnTrace.walks F cap 0 ops

def extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) : Segment → Nat
  | .append ks => ScratchGrow.extraCost cfg F cap 0 ks
  | .frames ops => SerdeIgnTrace.extraCost cfg F cap 0 ops

def Valid (cap : UInt32) : Segment → Prop
  | .append ks => ScratchGrow.validTrace cap 0 ks
  | .frames ops => SerdeIgnTrace.Valid cap 0 ops

theorem free_eq (F : Nat) (cap : UInt32) (seg : Segment) :
    endFreeBound F cap seg = F + 2 * growthCount cap seg := by
  cases seg with
  | append ks => exact ScratchGrow.endFreeBound_eq F cap 0 ks
  | frames ops => exact SerdeIgnTrace.endFreeBound_eq F cap 0 ops

theorem walks_eq (F : Nat) (cap : UInt32) (seg : Segment) :
    walks F cap seg + growthCount cap seg = F * growthCount cap seg + growthCount cap seg * growthCount cap seg := by
  cases seg with
  | append ks => exact ScratchGrow.walkBounds_eq F cap 0 ks
  | frames ops => exact SerdeIgnTrace.walks_eq F cap 0 ops

theorem moved_capacity (cap : UInt32) (seg : Segment) (hv : Valid cap seg) :
    movedBytes cap seg + cap.toNat ≤ (next cap seg).toNat := by
  cases seg with
  | append ks => exact ScratchGrow.movedBytes_capacity cap 0 ks hv
  | frames ops => exact SerdeIgnTrace.movedBytes_capacity cap 0 ops hv

theorem allocated_capacity (cap : UInt32) (seg : Segment) (hv : Valid cap seg) :
    allocatedBytes cap seg + 2 * cap.toNat ≤ 2 * (next cap seg).toNat := by
  cases seg with
  | append ks => exact ScratchGrow.allocatedBytes_capacity cap 0 ks hv
  | frames ops => exact SerdeIgnTrace.allocatedBytes_capacity cap 0 ops hv

theorem capacity (cap : UInt32) (seg : Segment) (hv : Valid cap seg) :
    (next cap seg).toNat ≤ max cap.toNat (2 * peak cap seg + 8) := by
  cases seg with
  | append ks => simpa only [next, peak, UInt32.toNat_zero] using ScratchGrow.endState_capacity cap 0 ks hv
  | frames ops => exact SerdeIgnTrace.endState_capacity cap 0 ops hv

theorem pages_scaled (cap : UInt32) (seg : Segment) (hv : Valid cap seg)
    (hc : (next cap seg).toNat < 2 ^ 28) :
    65536 * pages cap seg ≤ allocatedBytes cap seg + 66066 * growthCount cap seg := by
  cases seg with
  | append ks => exact ScratchGrow.growthPages_scaled cap 0 ks hv hc
  | frames ops => exact SerdeIgnTrace.pages_scaled cap 0 ops hv

theorem extraCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (seg : Segment) :
    extraCost cfg F cap seg ≤
      (1790 * growthCount cap seg + walks F cap seg * 320 + 18 * movedBytes cap seg) * cfg.regularOpCost +
      growthCount cap seg * cfg.linearOpBaseCost + cfg.linearOpUnitCost * pages cap seg := by
  cases seg with
  | append ks => exact ScratchGrow.extraCost_le cfg F cap 0 ks
  | frames ops => exact SerdeIgnTrace.extraCost_le cfg F cap 0 ops

end Segment

abbrev Batches := List Segment
def Valid (cap : UInt32) : Batches → Prop
  | [] => cap.toNat < 2 ^ 28
  | ks :: batches => cap.toNat < 2 ^ 28 ∧ Segment.Valid cap ks ∧ Valid (Segment.next cap ks) batches

def endCap (cap : UInt32) : Batches → UInt32
  | [] => cap
  | ks :: batches => endCap (Segment.next cap ks) batches

def peak (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => max (Segment.peak cap ks) (peak (Segment.next cap ks) batches)

def growthCount (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.growthCount cap ks + growthCount (Segment.next cap ks) batches

def endFreeBound (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => F
  | ks :: batches => endFreeBound (Segment.endFreeBound F cap ks) (Segment.next cap ks) batches

def walks (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.walks F cap ks +
      walks (Segment.endFreeBound F cap ks) (Segment.next cap ks) batches

def movedBytes (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.movedBytes cap ks + movedBytes (Segment.next cap ks) batches

def allocatedBytes (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.allocatedBytes cap ks + allocatedBytes (Segment.next cap ks) batches

def pages (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.pages cap ks + pages (Segment.next cap ks) batches

def extraCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) : Batches → Nat
  | [] => 0
  | ks :: batches => Segment.extraCost cfg F cap ks +
      extraCost cfg (Segment.endFreeBound F cap ks) (Segment.next cap ks) batches

theorem valid_cap (cap : UInt32) (batches : Batches) (hv : Valid cap batches) : cap.toNat < 2 ^ 28 := by
  cases batches with
  | nil => exact hv
  | cons ks batches => exact hv.1

theorem endFreeBound_eq (F : Nat) (cap : UInt32) (batches : Batches) :
    endFreeBound F cap batches = F + 2 * growthCount cap batches := by
  induction batches generalizing F cap with
  | nil => simp [endFreeBound, growthCount]
  | cons ks batches ih =>
    simp only [endFreeBound, ih, growthCount, Segment.free_eq]
    omega

theorem walks_eq (F : Nat) (cap : UInt32) (batches : Batches) :
    walks F cap batches + growthCount cap batches =
      F * growthCount cap batches + growthCount cap batches * growthCount cap batches := by
  induction batches generalizing F cap with
  | nil => simp [walks, growthCount]
  | cons ks batches ih =>
    have h1 := Segment.walks_eq F cap ks
    have h2 := ih (Segment.endFreeBound F cap ks) (Segment.next cap ks)
    rw [Segment.free_eq] at h2
    simp only [walks, growthCount, Segment.free_eq]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at h2 ⊢
    rw [Nat.mul_comm (growthCount (Segment.next cap ks) batches) (Segment.growthCount cap ks)]
    omega

theorem movedBytes_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    movedBytes cap batches + cap.toNat ≤ (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [movedBytes, endCap]
  | cons ks batches ih =>
    have h1 := Segment.moved_capacity cap ks hv.2.1
    have h2 := ih (Segment.next cap ks) hv.2.2
    simp only [movedBytes, endCap, Segment.next] at *
    omega

theorem allocatedBytes_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    allocatedBytes cap batches + 2 * cap.toNat ≤ 2 * (endCap cap batches).toNat := by
  induction batches generalizing cap with
  | nil => simp [allocatedBytes, endCap]
  | cons ks batches ih =>
    have h1 := Segment.allocated_capacity cap ks hv.2.1
    have h2 := ih (Segment.next cap ks) hv.2.2
    simp only [allocatedBytes, endCap, Segment.next] at *
    omega

theorem endCap_capacity (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    (endCap cap batches).toNat ≤ max cap.toNat (2 * peak cap batches + 8) := by
  induction batches generalizing cap with
  | nil => simp [endCap]
  | cons ks batches ih =>
    have h1 := Segment.capacity cap ks hv.2.1
    have h2 := ih (Segment.next cap ks) hv.2.2
    simp only [UInt32.toNat_zero, endCap, peak, Segment.next] at *
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
    have h1 := Segment.pages_scaled cap ks hv.2.1 (valid_cap (Segment.next cap ks) batches hv.2.2)
    have h2 := ih (Segment.next cap ks) hv.2.2
    simp only [pages, allocatedBytes, growthCount]
    omega

theorem extraCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (batches : Batches) :
    extraCost cfg F cap batches ≤
      (1790 * growthCount cap batches + walks F cap batches * 320 + 18 * movedBytes cap batches) * cfg.regularOpCost +
      growthCount cap batches * cfg.linearOpBaseCost + cfg.linearOpUnitCost * pages cap batches := by
  induction batches generalizing F cap with
  | nil => simp [extraCost, growthCount, walks, movedBytes, pages]
  | cons ks batches ih =>
    have h1 := Segment.extraCost_le cfg F cap ks
    have h2 := ih (Segment.endFreeBound F cap ks) (Segment.next cap ks)
    simp only [extraCost, growthCount, walks, movedBytes, pages]
    simp only [Nat.add_mul, Nat.mul_add] at h1 h2 ⊢
    omega

def budget (cfg : WasmConfig) (F G P : Nat) : Nat :=
  (1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * P + 8)) * cfg.regularOpCost +
    G * cfg.linearOpBaseCost + cfg.linearOpUnitCost * ((4 * P + 16 + 66066 * G) / 65536)

theorem extraCost_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (batches : Batches) (hv : Valid cap batches) :
    extraCost cfg F cap batches ≤ budget cfg F (growthCount cap batches) (peak cap batches) := by
  have hwalk := walks_eq F cap batches
  have hmove := movedBytes_peak cap batches hv
  have hp := pages_scaled cap batches hv
  have ha := allocatedBytes_peak cap batches hv
  have hpage : pages cap batches ≤ (4 * peak cap batches + 16 + 66066 * growthCount cap batches) / 65536 := by omega
  have hw : walks F cap batches = F * growthCount cap batches + growthCount cap batches * growthCount cap batches - growthCount cap batches := by omega
  have hm := Nat.mul_le_mul_right cfg.regularOpCost (Nat.mul_le_mul_left 18 hmove)
  have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hpage
  have he := extraCost_le cfg F cap batches
  unfold budget
  rw [hw] at he
  simp only [Nat.add_mul] at he ⊢
  omega


theorem budget_mono_peak (cfg : WasmConfig) (F G P Q : Nat) (hp : P ≤ Q) : budget cfg F G P ≤ budget cfg F G Q := by
  have hw := Nat.mul_le_mul_right cfg.regularOpCost
    (show 1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * P + 8) ≤
      1790 * G + (F * G + G * G - G) * 320 + 18 * (2 * Q + 8) by omega)
  have hd : (4 * P + 16 + 66066 * G) / 65536 ≤ (4 * Q + 16 + 66066 * G) / 65536 := by omega
  have hh := Nat.mul_le_mul_left cfg.linearOpUnitCost hd
  unfold budget
  omega

theorem frames_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (ops : List Bool)
    (hv : SerdeIgnTrace.Valid cap 0 ops) (hc : cap.toNat < 2 ^ 28)
    (he : (SerdeIgnTrace.endState cap 0 ops).1.toNat < 2 ^ 28) :
    SerdeIgnTrace.extraCost cfg F cap 0 ops ≤
      budget cfg F (SerdeIgnTrace.growthCount cap 0 ops) (SerdeIgnTrace.peak 0 ops) := by
  have hvalid : Valid cap [.frames ops] := ⟨hc, hv, he⟩
  simpa only [extraCost, growthCount, peak, Segment.extraCost, Segment.growthCount,
    Segment.peak, Nat.add_zero, Nat.max_zero] using extraCost_budget cfg F cap [.frames ops] hvalid

theorem budget_le_frame_budget (cfg : WasmConfig) (F G P : Nat) :
    budget cfg F G P ≤ SerdeIgnTrace.budget cfg F G P := by
  have h := Nat.mul_le_mul_right cfg.regularOpCost
    (Nat.mul_le_mul_right 320 (Nat.sub_le (F * G + G * G) G))
  unfold budget SerdeIgnTrace.budget
  simp only [Nat.add_mul] at h ⊢
  omega

end WNear.Binary.ScratchMixedTrace
