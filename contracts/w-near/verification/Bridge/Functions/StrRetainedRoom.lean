import Bridge.Functions.StrRoom

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WNear.Binary.ParseStrRoom
open Wasm Wasm.Near WNear.Binary
open ParseStr ParseEscape ScratchGrow VecFromElem LookupMapOps

theorem no_fit_small (cap : UInt32) (u v : Nat) (hs : u + v ≤ 64)
    (hf : ¬ fits cap (UInt32.ofNat u) (UInt32.ofNat v)) : cap.toNat ≤ 128 := by
  have hu : (UInt32.ofNat u).toNat = u := by simp; omega
  have hv : (UInt32.ofNat v).toNat = v := by simp; omega
  simp only [fits, hu, hv] at hf
  omega

theorem reserve_capacity_any (cap : UInt32) (u v : Nat)
    (hu : u ≤ cap.toNat) (hs : u + v ≤ 64) :
    u + v ≤ (capAfter cap (UInt32.ofNat u) (UInt32.ofNat v)).toNat := by
  by_cases hf : fits cap (UInt32.ofNat u) (UInt32.ofNat v)
  · have hu32 : (UInt32.ofNat u).toNat = u := by simp; omega
    have hv32 : (UInt32.ofNat v).toNat = v := by simp; omega
    have hfit := hf
    simp only [fits, hu32, hv32] at hfit
    simp only [capAfter, if_pos hf]
    omega
  · exact (reserve_capacity cap u v (no_fit_small cap u v hs hf) hu hs).2

theorem reserve_grows_one_any (cap : UInt32) (u v hl hl' : Nat)
    (hs : u + v ≤ 64) (hh : hlAfter hl hl' cap (UInt32.ofNat u) (UInt32.ofNat v)) :
    hl' = hl ∨ hl' = hl + 65536 := by
  by_cases hf : fits cap (UInt32.ofNat u) (UInt32.ofNat v)
  · simp only [hlAfter, if_pos hf] at hh
    exact Or.inl hh
  · exact reserve_grows_one cap u v hl hl' (no_fit_small cap u v hs hf) hs hh

theorem reserve_room_any {k hl maxP : Nat} (cap : UInt32) (u v : Nat)
    (hs : u + v ≤ 64) (hr : HeapRoomK k hl maxP) (hk : 1 ≤ k) :
    roomRes hl maxP cap (UInt32.ofNat u) (UInt32.ofNat v) := by
  intro hf
  exact reserve_room cap u v (no_fit_small cap u v hs hf) hs hr hk hf

theorem roomRun_short_any (maxP hl : Nat) (cap : UInt32) (acc l bytes rest : List UInt8)
    (hu : acc.length ≤ cap.toNat) (hb : bytes.length ≤ 64)
    (hok : strRun l acc = .ok bytes rest)
    (hr : HeapRoomK (2 * (bytes.length - acc.length) + 3) hl maxP) :
    roomRun maxP hl cap acc l := by
  have hab := strRun_body_le l acc bytes rest hok
  have hsmall : acc.length + (l.takeWhile plain).length ≤ 64 := by omega
  have hcap1 := reserve_capacity_any cap acc.length (l.takeWhile plain).length hu hsmall
  apply (roomRun_unfold maxP hl cap acc l).2
  refine ⟨error_room hr (by omega), reserve_room_any cap _ _ hsmall hr (by omega), ?_⟩
  intro hl1 hh1
  have hg1 := reserve_grows_one_any cap _ _ hl hl1 hsmall hh1
  have hr1 : HeapRoomK (2 * (bytes.length - acc.length) + 2) hl1 maxP :=
    heap_room_after hr (by omega) hg1
  refine ⟨error_room hr1 (by omega), ?_⟩
  intro tail hd
  rw [strRun_cons l acc 0x5C tail hd] at hok
  simp only [show (0x5C : UInt8) ≠ 0x22 by decide, ite_false, ite_true] at hok
  cases he : escDecode tail with
  | none => simp only [he] at hok; cases hok
  | some pair =>
    obtain ⟨out, m⟩ := pair
    simp only [he] at hok
    have hnext := strRun_acc_le (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest hok
    have hpositive := escDecode_len tail out m he
    have hk : escK tail = out.length := by simp [escK, he]
    have hsmall2 : (acc ++ l.takeWhile plain).length + out.length ≤ 64 := by
      simp only [List.length_append] at hnext ⊢; omega
    have hcap2 := reserve_capacity_any (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
      (acc ++ l.takeWhile plain).length out.length (by simpa only [List.length_append] using hcap1) hsmall2
    rw [hk]
    refine ⟨reserve_room_any _ _ _ hsmall2 hr1 (by omega), ?_⟩
    intro hl2 hh2 out' m' he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    have hg2 := reserve_grows_one_any _ _ _ hl1 hl2 hsmall2 hh2
    have hr2 : HeapRoomK (2 * (bytes.length - acc.length) + 1) hl2 maxP :=
      heap_room_after hr1 (by omega) hg2
    apply roomRun_short_any maxP hl2 _ (acc ++ l.takeWhile plain ++ out) (tail.drop m) bytes rest (by simpa only [List.length_append] using hcap2) hb hok
    apply heap_room_mono hr2
    simp only [List.length_append] at hnext ⊢
    omega
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega


end WNear.Binary.ParseStrRoom
