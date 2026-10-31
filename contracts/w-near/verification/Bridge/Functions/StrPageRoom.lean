import Bridge.Functions.StrRoom
import Bridge.Functions.StrGrowthTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WNear.Binary.ParseStrRoom
open Wasm Wasm.Near WNear.Binary
open ParseStr ParseEscape ScratchGrow VecFromElem LookupMapOps

def reservePages (cap len k : UInt32) : Nat :=
  if fits cap len k then 0 else (AllocNewCell.cellPages (AllocAlloc.wordsOf (capAfter cap len k)) 1).toNat

/-- A page budget covers the reserve and every permitted heap outcome. -/
theorem reserve_pages_room (cap len k : UInt32) (hl maxP tail : Nat) (ht : 1 ≤ tail)
    (hr : HeapRoomK (reservePages cap len k + tail) hl maxP) :
    roomRes hl maxP cap len k ∧
      ∀ hl', hlAfter hl hl' cap len k → HeapRoomK tail hl' maxP := by
  by_cases hf : fits cap len k
  · simp only [reservePages, if_pos hf, Nat.zero_add] at hr
    refine ⟨fun h => False.elim (h hf), ?_⟩
    intro hl' hh
    simp only [hlAfter, if_pos hf] at hh
    subst hl'
    exact hr
  · simp only [reservePages, if_neg hf, capAfter] at hr
    generalize hP : (AllocNewCell.cellPages (AllocAlloc.wordsOf (VecGrow.growCap cap (len + k))) 1).toNat = P at hr
    change HeapRoomK (P + tail) hl maxP at hr
    obtain ⟨ha, hp, hm, hw⟩ := hr
    have hroom : roomFor hl maxP (VecGrow.growCap cap (len + k)) := by
      unfold roomFor
      rw [hP]
      change hl % 65536 = 0 ∧ 0 < hl ∧ hl + P * 65536 + 65536 ≤ 2 ^ 32 ∧
        (hl + P * 65536) / 65536 ≤ maxP
      exact ⟨ha, hp, by omega, by omega⟩
    refine ⟨fun _ => hroom, ?_⟩
    intro hl' hh
    simp only [hlAfter, if_neg hf, grownLen] at hh
    rw [hP] at hh
    change hl' = hl ∨ hl' = hl + P * 65536 at hh
    clear hP hroom hf
    rcases hh with rfl | rfl
    · refine ⟨ha, hp, ?_, ?_⟩
      · exact (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 (Nat.le_add_left tail P)) hl').trans hm
      · exact (Nat.add_le_add_left (Nat.mul_le_mul_right 65536 (Nat.add_le_add_right (Nat.le_add_left tail P) 1)) hl').trans hw
    · refine ⟨?_, by omega, by omega, by omega⟩
      simpa [Nat.add_mod, Nat.mul_mod] using ha

/-- Room tracks every reserve, including the conservative borrowed-tail reserve. -/
def roomChunks (l acc : List UInt8) : List UInt32 :=
  match hd : l.dropWhile plain with
  | [] => [UInt32.ofNat (l.takeWhile plain).length]
  | x :: tail =>
    if x = 0x5C then
      match he : escDecode tail with
      | some (out, m) => UInt32.ofNat (l.takeWhile plain).length :: UInt32.ofNat out.length ::
          roomChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out)
      | none => [UInt32.ofNat (l.takeWhile plain).length]
    else [UInt32.ofNat (l.takeWhile plain).length]
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

theorem roomChunks_escape (l acc tail out : List UInt8) (m : Nat)
    (hd : l.dropWhile plain = 0x5C :: tail) (he : escDecode tail = some (out, m)) :
    roomChunks l acc = UInt32.ofNat (l.takeWhile plain).length :: UInt32.ofNat out.length ::
      roomChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out) := by
  rw [roomChunks]
  split
  · rename_i hh; simp [hd] at hh
  · rename_i x rest hh
    rw [hd] at hh
    simp only [List.cons.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only [ite_true]
    rw [he]

theorem roomChunks_plain (l acc tail : List UInt8) (x : UInt8)
    (hd : l.dropWhile plain = x :: tail) (hx : x ≠ 0x5C) :
    roomChunks l acc = [UInt32.ofNat (l.takeWhile plain).length] := by
  rw [roomChunks]
  split
  · rename_i hh; simp [hd] at hh
  · rename_i y rest hh
    rw [hd] at hh
    simp only [List.cons.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only [if_neg hx]

theorem roomRun_pages (maxP hl : Nat) (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest)
    (hr : HeapRoomK (growthPages cap (UInt32.ofNat acc.length) (roomChunks l acc) + 1) hl maxP) :
    roomRun maxP hl cap acc l := by
  match hd : l.dropWhile plain with
  | [] => rw [strRun_nil l acc hd] at hok; cases hok
  | x :: tail =>
    by_cases hx : x = 0x5C
    · subst x
      rw [strRun_cons l acc 0x5C tail hd] at hok
      simp only [show (0x5C : UInt8) ≠ 0x22 by decide, ite_false, ite_true] at hok
      cases he : escDecode tail with
      | none => simp only [he] at hok; cases hok
      | some pair =>
        obtain ⟨out, m⟩ := pair
        simp only [he] at hok
        rw [roomChunks_escape l acc tail out m hd he] at hr
        have hsum : UInt32.ofNat acc.length + UInt32.ofNat (l.takeWhile plain).length =
            UInt32.ofNat (acc ++ l.takeWhile plain).length := by simp [List.length_append, UInt32.ofNat_add]
        have hsum2 : UInt32.ofNat (acc ++ l.takeWhile plain).length + UInt32.ofNat out.length =
            UInt32.ofNat (acc ++ l.takeWhile plain ++ out).length := by simp [List.length_append, UInt32.ofNat_add, UInt32.add_assoc]
        change HeapRoomK (reservePages cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) +
          growthPages (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat acc.length + UInt32.ofNat (l.takeWhile plain).length)
            (UInt32.ofNat out.length :: roomChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out)) + 1) hl maxP at hr
        have hr0 := ParseStrRoom.heap_room_mono hr (show 1 ≤ _ by omega)
        have hr' : HeapRoomK (reservePages cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) +
          (growthPages (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat acc.length + UInt32.ofNat (l.takeWhile plain).length)
            (UInt32.ofNat out.length :: roomChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out)) + 1)) hl maxP := by
          simpa only [Nat.add_assoc] using hr
        obtain ⟨hres, hafter⟩ := reserve_pages_room cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)
          hl maxP _ (by omega) hr'
        apply (roomRun_unfold maxP hl cap acc l).2
        refine ⟨error_room hr0 (by decide), hres, ?_⟩
        intro hl1 hh1
        have hr1 := hafter hl1 hh1
        rw [hsum] at hr1
        refine ⟨error_room hr1 (by omega), ?_⟩
        intro tail' hd'
        rw [hd] at hd'
        cases hd'
        have hk : escK tail = out.length := by simp [escK, he]
        rw [hk]
        change HeapRoomK (reservePages (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
          (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length) +
          growthPages _ _ (roomChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out)) + 1) hl1 maxP at hr1
        have hr1' := hr1
        rw [Nat.add_assoc] at hr1'
        obtain ⟨hr2, ha2⟩ := reserve_pages_room _ _ _ hl1 maxP _ (by omega) hr1'
        refine ⟨hr2, ?_⟩
        intro hl2 hh2 out' m' he'
        rw [he] at he'
        cases he'
        apply roomRun_pages maxP hl2 _ (acc ++ l.takeWhile plain ++ out) (tail.drop m) bytes rest hok
        have hr2 := ha2 hl2 hh2
        simpa only [hsum2] using hr2
    · rw [roomChunks_plain l acc tail x hd hx] at hr
      change HeapRoomK (reservePages cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) + 1) hl maxP at hr
      have hr0 := ParseStrRoom.heap_room_mono hr (show 1 ≤ _ by omega)
      obtain ⟨hres, hafter⟩ := reserve_pages_room cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)
        hl maxP 1 (by decide) hr
      apply (roomRun_unfold maxP hl cap acc l).2
      refine ⟨error_room hr0 (by decide), hres, ?_⟩
      intro hl1 hh1
      refine ⟨error_room (hafter hl1 hh1) (by decide), ?_⟩
      intro tail' hd'
      rw [hd] at hd'
      cases hd'
      exact False.elim (hx rfl)
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

open WNear.Binary.ParseStrSuccess (appendChunks appendChunks_close appendChunks_esc)

theorem roomChunks_copied (l acc bytes rest : List UInt8) (hok : strRun l acc = .ok bytes rest)
    (hc : acc ≠ [] ∨ ¬ borrowed l) : roomChunks l acc = appendChunks l acc := by
  match hd : l.dropWhile plain with
  | [] => rw [strRun_nil l acc hd] at hok; cases hok
  | x :: tail =>
    rw [strRun_cons l acc x tail hd] at hok
    by_cases h22 : x = 0x22
    · subst x
      have ha : acc ≠ [] := by
        rcases hc with hc | hc
        · exact hc
        · exact False.elim (hc (by simp [borrowed, hd]))
      rw [roomChunks_plain l acc tail 0x22 hd (by decide), appendChunks_close l acc tail hd, if_neg ha]
    · simp only [h22, ite_false] at hok
      by_cases h92 : x = 0x5C
      · subst x
        simp only [ite_true] at hok
        cases he : escDecode tail with
        | none => simp [he] at hok
        | some pair =>
          obtain ⟨out, m⟩ := pair
          simp only [he] at hok
          have hp := escDecode_len tail out m he
          have hn : acc ++ l.takeWhile plain ++ out ≠ [] := by
            intro hn
            have hh := congrArg List.length hn
            simp only [List.length_append, List.length_nil] at hh
            omega
          rw [roomChunks_escape l acc tail out m hd he, appendChunks_esc l acc tail out m hd he,
            roomChunks_copied (tail.drop m) (acc ++ l.takeWhile plain ++ out) bytes rest hok (Or.inl hn)]
      · simp only [h92, ite_false] at hok
        cases hok
termination_by l.length
decreasing_by
  have hh := dropWhile_length_le l plain
  rw [hd] at hh
  simp only [List.length_cons, List.length_drop] at hh ⊢
  omega

end WNear.Binary.ParseStrRoom
