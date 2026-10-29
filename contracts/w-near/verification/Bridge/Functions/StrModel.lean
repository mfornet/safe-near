import Bridge.Functions.EscModel
import Bridge.Functions.ParseStrErr

/-!
# `parse_str` (646) as a run, against the model's `stringBody` (M6)

`parse_str` scans plain bytes; at a `\` it appends the bytes so far to the scratch, then the escape's
(649); at `"` it ends; at the end of the input or a control byte it fails. `strRun l acc` is that run
over the input `l` from the reader's position, the scratch holding `acc`:

* `.ok bytes rest`: the string ends, its bytes `bytes` (the scratch then the last plain bytes), the input
  `rest` after the `"`;
* `.eof`, `.ctrl`, `.badEsc`: the three rejections of the run itself.

`strRun_model`: `stringBody l acc.reverse` is `some (String.fromUTF8? bytes, rest)` on `.ok bytes rest`,
and `none` otherwise. The UTF-8 check on `bytes` is `as_str`'s (648), and it is the model's
`String.fromUTF8?`. So `parse_str` accepts exactly the strings the model accepts, with the same bytes.
-/

namespace WNear.Binary.ParseStr

open NearInterface.Json (stringBody)
open WNear.Binary.ParseEscape (escDecode)

/-- The outcome of `parse_str`'s run. -/
inductive StrOut where
  | ok (bytes rest : List UInt8)
  | eof
  | ctrl
  | badEsc
  deriving Repr

theorem dropWhile_length_le (l : List UInt8) (p : UInt8 → Bool) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.dropWhile_cons]; split <;> simp <;> omega

/-- `parse_str`'s run over `l`, the scratch holding `acc`. -/
def strRun (l acc : List UInt8) : StrOut :=
  match h : l.dropWhile plain with
  | [] => .eof
  | x :: rest =>
    if x = 0x22 then .ok (acc ++ l.takeWhile plain) rest
    else if x = 0x5C then
      match he : escDecode rest with
      | some (out, m) => strRun (rest.drop m) (acc ++ l.takeWhile plain ++ out)
      | none => .badEsc
    else .ctrl
termination_by l.length
decreasing_by
  have h1 := dropWhile_length_le l plain
  rw [h] at h1
  simp at h1
  simp only [List.length_drop]
  omega

theorem takeWhile_plain (l : List UInt8) : ∀ b ∈ l.takeWhile plain, plain b = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro b hb
    simp only [List.takeWhile_cons] at hb
    split at hb
    · rename_i ha
      simp at hb
      rcases hb with rfl | hb
      · exact ha
      · exact ih b hb
    · simp at hb

theorem dropWhile_head (l : List UInt8) (x : UInt8) (rest : List UInt8) (h : l.dropWhile plain = x :: rest) :
    plain x = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i ha
      simp at h
      rw [← h.1]; simpa using ha

theorem strRun_nil (l acc : List UInt8) (h : l.dropWhile plain = []) : strRun l acc = .eof := by
  unfold strRun; split <;> simp_all

theorem strRun_cons (l acc : List UInt8) (x : UInt8) (rest : List UInt8) (h : l.dropWhile plain = x :: rest) :
    strRun l acc =
      if x = 0x22 then .ok (acc ++ l.takeWhile plain) rest
      else if x = 0x5C then
        match escDecode rest with
        | some (out, m) => strRun (rest.drop m) (acc ++ l.takeWhile plain ++ out)
        | none => .badEsc
      else .ctrl := by
  rw [strRun]
  split
  · simp_all
  · rename_i x' rest' h'
    rw [h] at h'
    simp only [List.cons.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    split <;> (try rfl)
    split <;> (try rfl)
    split <;> simp_all

/-- **`parse_str`'s run against the model.** -/
theorem strRun_model (l acc : List UInt8) :
    stringBody l acc.reverse =
      match strRun l acc with
      | .ok bytes rest => some (String.fromUTF8? ⟨bytes.toArray⟩, rest)
      | _ => none := by
  induction h : l.length using Nat.strong_induction_on generalizing l acc with
  | _ len ih =>
    have hsplit := List.takeWhile_append_dropWhile (p := plain) (l := l)
    conv => lhs; rw [← hsplit]
    rw [stringBody_skip _ _ _ (takeWhile_plain l)]
    cases hd : l.dropWhile plain with
    | nil => rw [strRun_nil l acc hd]; simp [stringBody]
    | cons x rest =>
      rw [strRun_cons l acc x rest hd]
      have hx := dropWhile_head l x rest hd
      by_cases h22 : x = 0x22
      · subst h22
        simp only [ite_true]
        rw [stringBody.eq_2]
        simp
      · simp only [h22, ite_false]
        by_cases h5c : x = 0x5C
        · subst h5c
          rw [if_pos rfl]
          rw [ParseEscape.stringBody_esc]
          cases he : escDecode rest with
          | none => simp
          | some p =>
            obtain ⟨out, m⟩ := p
            simp only []
            have h1 := dropWhile_length_le l plain
            rw [hd] at h1
            simp at h1
            have := ih (rest.drop m).length (by simp; omega) (rest.drop m) (acc ++ l.takeWhile plain ++ out) rfl
            rw [← this]
            simp [List.reverse_append, List.append_assoc]
        · simp only [h5c, ite_false]
          have hlt : x < 0x20 := by
            simp only [plain, Bool.and_eq_false_imp, bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
            apply UInt8.lt_iff_toNat_lt.mpr
            have e22 : x.toNat ≠ 0x22 := fun e => h22 (UInt8.toNat_inj.mp (by rw [e]; rfl))
            have e5c : x.toNat ≠ 0x5C := fun e => h5c (UInt8.toNat_inj.mp (by rw [e]; rfl))
            by_contra hc
            have := hx (by simp at hc ⊢; omega)
            simp at this
            omega
          rw [stringBody] <;> simp_all

end WNear.Binary.ParseStr
