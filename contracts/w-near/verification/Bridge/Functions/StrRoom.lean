import Bridge.Functions.StrCost
import Bridge.Functions.LookupMapOps
import Bridge.Functions.SerdeAccountIdEsc

/-! Space for every reserve in a successful short-string reader, including its
all-outcome error-box contracts. The numerical initial-memory allowance remains
explicit; this does not establish reachable method resources. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace WNear.Binary.ParseStrRoom
open Wasm Wasm.Near WNear.Binary
open ParseStr ParseEscape ScratchGrow VecFromElem LookupMapOps

theorem strRun_acc_le (l acc bytes rest : List UInt8)
    (h : strRun l acc = .ok bytes rest) : acc.length ≤ bytes.length := by
  match hd : l.dropWhile plain with
  | [] => rw [strRun_nil l acc hd] at h; cases h
  | x :: tail =>
    rw [strRun_cons l acc x tail hd] at h
    split at h
    · cases h
      simp
    · split at h
      · split at h
        · rename_i out m he
          have hh := strRun_acc_le (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest h
          simp only [List.length_append] at hh
          omega
        · cases h
      · cases h
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

theorem strRun_body_le (l acc bytes rest : List UInt8)
    (h : strRun l acc = .ok bytes rest) : acc.length + (l.takeWhile plain).length ≤ bytes.length := by
  match hd : l.dropWhile plain with
  | [] => rw [strRun_nil l acc hd] at h; cases h
  | x :: tail =>
    rw [strRun_cons l acc x tail hd] at h
    split at h
    · cases h; simp
    · split at h
      · split at h
        · rename_i out m he
          have hh := strRun_acc_le (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest h
          simp only [List.length_append] at hh
          omega
        · cases h
      · cases h

theorem reserve_capacity (cap : UInt32) (u v : Nat) (hc : cap.toNat ≤ 128)
    (hu : u ≤ cap.toNat) (hs : u + v ≤ 64) :
    (capAfter cap (UInt32.ofNat u) (UInt32.ofNat v)).toNat ≤ 128 ∧
    u + v ≤ (capAfter cap (UInt32.ofNat u) (UInt32.ofNat v)).toNat := by
  have hu32 : (UInt32.ofNat u).toNat = u := by simp; omega
  have hv32 : (UInt32.ofNat v).toNat = v := by simp; omega
  have hsum : (UInt32.ofNat u + UInt32.ofNat v).toNat = u + v := by
    rw [UInt32.toNat_add, hu32, hv32]; omega
  unfold capAfter
  split
  · rename_i hf
    simp only [fits, hu32, hv32] at hf
    exact ⟨hc, by omega⟩
  · rename_i hf
    simp only [fits, hu32, hv32] at hf
    rw [VecGrow.growCap_toNat _ _ (by omega), hsum]
    omega

theorem reserve_grows_one (cap : UInt32) (u v hl hl' : Nat)
    (hc : cap.toNat ≤ 128) (hs : u + v ≤ 64)
    (hh : hlAfter hl hl' cap (UInt32.ofNat u) (UInt32.ofNat v)) :
    hl' = hl ∨ hl' = hl + 65536 := by
  have hu32 : (UInt32.ofNat u).toNat = u := by simp; omega
  have hv32 : (UInt32.ofNat v).toNat = v := by simp; omega
  have hsum : (UInt32.ofNat u + UInt32.ofNat v).toNat = u + v := by
    rw [UInt32.toNat_add, hu32, hv32]; omega
  have hg : (VecGrow.growCap cap (UInt32.ofNat u + UInt32.ofNat v)).toNat ≤ 4096 := by
    rw [VecGrow.growCap_toNat _ _ (by omega), hsum]; omega
  unfold hlAfter at hh
  split at hh
  · exact Or.inl hh
  · simpa only [grownLen_le4096 _ _ hg] using hh

theorem heap_room_after {k j hl hl' maxP : Nat} (hr : HeapRoomK k hl maxP)
    (hj : j + 1 ≤ k) (hh : hl' = hl ∨ hl' = hl + 65536) : HeapRoomK j hl' maxP := by
  rcases hr with ⟨ha, hp, hm, hw⟩
  have hmul := Nat.mul_le_mul_right 65536 hj
  have hmul' := Nat.mul_le_mul_right 65536 (Nat.add_le_add_right hj 1)
  rcases hh with hh | hh
  · subst hl'
    have hle : j ≤ k := (Nat.le_succ j).trans hj
    exact ⟨ha, hp, (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 hle) hl).trans hm,
      (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 (Nat.add_le_add_right hle 1)) hl).trans hw⟩
  · subst hl'
    refine ⟨by simpa only [Nat.add_mod_right] using ha,
      Nat.lt_of_lt_of_le hp (Nat.le_add_right hl 65536), ?_, ?_⟩
    · calc
        hl + 65536 + j * 65536 = hl + (j + 1) * 65536 := by
          simp only [Nat.add_mul, Nat.one_mul]; ac_rfl
        _ ≤ hl + k * 65536 := Nat.add_le_add_left hmul hl
        _ ≤ maxP * 65536 := hm
    · calc
        hl + 65536 + (j + 1) * 65536 = hl + (j + 1 + 1) * 65536 := by
          simp only [Nat.add_mul, Nat.one_mul]; ac_rfl
        _ ≤ hl + (k + 1) * 65536 := Nat.add_le_add_left hmul' hl
        _ ≤ 2 ^ 32 := hw

theorem error_room {k hl maxP : Nat} (hr : HeapRoomK k hl maxP) (hk : 1 ≤ k) :
    SerdeErrBox.roomFor4 hl maxP 20 := by
  have hc : (AllocNewCell.cellPages (AllocAlloc.wordsOf 20) 4).toNat = 1 := by decide +kernel
  unfold HeapRoomK at *
  rcases hr with ⟨ha, hp, hm, hw⟩
  unfold SerdeErrBox.roomFor4
  rw [hc]
  exact ⟨ha, hp, by omega, by omega⟩

theorem reserve_room {k hl maxP : Nat} (cap : UInt32) (u v : Nat)
    (hc : cap.toNat ≤ 128) (hs : u + v ≤ 64)
    (hr : HeapRoomK k hl maxP) (hk : 1 ≤ k) :
    roomRes hl maxP cap (UInt32.ofNat u) (UInt32.ofNat v) := by
  intro hf
  apply roomFor_ofK _ (by
    rw [VecGrow.growCap_toNat _ _ (by omega), UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat']
    omega) hr (lenIn_zero hl hr.1) (by omega)

theorem heap_room_mono {k j hl maxP : Nat} (hr : HeapRoomK k hl maxP)
    (hj : j ≤ k) : HeapRoomK j hl maxP := by
  rcases hr with ⟨ha, hp, hm, hw⟩
  exact ⟨ha, hp, (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 hj) hl).trans hm,
    (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 (Nat.add_le_add_right hj 1)) hl).trans hw⟩

/-- Every scratch growth and every error-box reserve of a successful short string
fits a linear one-page budget in its remaining decoded bytes. -/
theorem roomRun_short (maxP hl : Nat) (cap : UInt32) (acc l bytes rest : List UInt8)
    (hc : cap.toNat ≤ 128) (hu : acc.length ≤ cap.toNat) (hb : bytes.length ≤ 64)
    (hok : strRun l acc = .ok bytes rest)
    (hr : HeapRoomK (2 * (bytes.length - acc.length) + 3) hl maxP) :
    roomRun maxP hl cap acc l := by
  have hab := strRun_body_le l acc bytes rest hok
  have hsmall : acc.length + (l.takeWhile plain).length ≤ 64 := by omega
  have hcap1 := reserve_capacity cap acc.length (l.takeWhile plain).length hc hu hsmall
  apply (roomRun_unfold maxP hl cap acc l).2
  refine ⟨error_room hr (by omega), reserve_room cap _ _ hc hsmall hr (by omega), ?_⟩
  intro hl1 hh1
  have hg1 := reserve_grows_one cap _ _ hl hl1 hc hsmall hh1
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
    have hcap2 := reserve_capacity (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
      (acc ++ l.takeWhile plain).length out.length hcap1.1 (by simpa only [List.length_append] using hcap1.2) hsmall2
    rw [hk]
    refine ⟨reserve_room _ _ _ hcap1.1 hsmall2 hr1 (by omega), ?_⟩
    intro hl2 hh2 out' m' he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    have hg2 := reserve_grows_one _ _ _ hl1 hl2 hcap1.1 hsmall2 hh2
    have hr2 : HeapRoomK (2 * (bytes.length - acc.length) + 1) hl2 maxP :=
      heap_room_after hr1 (by omega) hg2
    apply roomRun_short maxP hl2 _ (acc ++ l.takeWhile plain ++ out) (tail.drop m) bytes rest hcap2.1 (by simpa only [List.length_append] using hcap2.2) hb hok
    apply heap_room_mono hr2
    simp only [List.length_append] at hnext ⊢
    omega
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

/-- Model-accepted short strings discharge the parser's all-outcome room contract
under a concrete initial page allowance, including arbitrary valid escapes. -/
theorem roomRun_of_short_stringBody (maxP hl : Nat) (l rest : List UInt8) (s : String)
    (hs : NearInterface.Json.stringBody l [] = some (some s, rest))
    (hlen : s.toUTF8.toList.length ≤ 64) (hr : HeapRoomK 131 hl maxP) :
    roomRun maxP hl 0 [] l := by
  apply roomRun_short maxP hl 0 [] l s.toUTF8.toList rest (by decide) (by simp) hlen
    (SerdeAccountIdEsc.strRun_of_stringBody l s rest hs).1
  apply heap_room_mono hr
  simp only [List.length_nil, Nat.sub_zero]
  omega

end WNear.Binary.ParseStrRoom
