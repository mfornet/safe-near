import Bridge.Functions.IgnoreModel
import Bridge.Functions.SerdeRead

/-!
# Numbers in ignored values, as serde skips them (M6, pure)

`ignore_value` (81) skips a number with `ignore_integer` (83), `ignore_decimal` (86) and
`ignore_exponent` (87), after eating a leading `-` itself. They return only where the number ends.
This file states that reading on the model's side:

* `expR r`: after `e` or `E`, an optional sign and at least one digit (87);
* `afterExp v`: an optional exponent;
* `fracR r`: after `.`, at least one digit, then an optional exponent (86);
* `afterInt r`: after the integer part, a fraction, an exponent or nothing (83's tail);
* `intR s`: `0` not followed by a digit, or `[1-9][0-9]*`, then `afterInt` (83).

`number_intR`: where the model's `number` reads a number that starts with a digit (and is not `0`
followed by a digit, serde's early failure), `intR` reads it with the same rest.
-/

namespace WNear.SerdeNumModel

open NearInterface.Json WNear.JsonFuel WNear.IgnoreModel

/-- An optional sign. -/
def signPart (r : List UInt8) : List UInt8 × List UInt8 :=
  match r with
  | 0x2B :: x => ([0x2B], x)
  | 0x2D :: x => ([0x2D], x)
  | x => ([], x)

/-- After `e`/`E`: an optional sign, then at least one digit. -/
def expR (r : List UInt8) : Option (List UInt8) :=
  let u := (signPart r).2
  if (u.takeWhile isDigit).isEmpty then none else some (u.dropWhile isDigit)

/-- After the digits of a fraction (or the integer part): an optional exponent. -/
def afterExp (v : List UInt8) : Option (List UInt8) :=
  match v with
  | e :: x => if e = 0x65 ∨ e = 0x45 then expR x else some (e :: x)
  | [] => some []

/-- After `.`: at least one digit, then an optional exponent. -/
def fracR (r : List UInt8) : Option (List UInt8) :=
  match r with
  | d :: _ => if isDigit d then afterExp (r.dropWhile isDigit) else none
  | [] => none

/-- After the integer part. -/
def afterInt (r : List UInt8) : Option (List UInt8) :=
  match r with
  | 0x2E :: x => fracR x
  | _ => afterExp r

/-- The integer part (`0` not followed by a digit, or `[1-9][0-9]*`), then `afterInt`. -/
def intR (s : List UInt8) : Option (List UInt8) :=
  match s with
  | d :: r =>
    if d = 0x30 then
      match r with
      | e :: _ => if isDigit e then none else afterInt r
      | [] => some []
    else if isDigit d then afterInt (r.dropWhile isDigit) else none
  | [] => none

/-! ## `number`, piece by piece -/

/-- `number`'s code after the integer part, verbatim (its `do` join points), from the prefix `pre`. -/
def numFE (pre : List UInt8) (bs : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (frac, bs) ← match bs with
    | 0x2E :: rest =>
      let (ds, rest) := digits rest
      if ds.isEmpty then none else some (0x2E :: ds, rest)
    | _ => some ([], bs)
  let (exp, bs) ← match bs with
    | e :: rest =>
      if e == 0x65 || e == 0x45 then
        let (s, rest) : List UInt8 × List UInt8 := match rest with
          | 0x2B :: r => ([0x2B], r)
          | 0x2D :: r => ([0x2D], r)
          | r => ([], r)
        let (ds, rest) := digits rest
        if ds.isEmpty then none else some (e :: s ++ ds, rest)
      else some ([], bs)
    | [] => some ([], bs)
  pure (pre ++ frac ++ exp, bs)

theorem isDigit_range {d : UInt8} (h : isDigit d = true) : 0x30 ≤ d.toNat ∧ d.toNat ≤ 0x39 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h
  simpa using h

theorem tw_ne {r : List UInt8} (h : ¬ (r.takeWhile isDigit).isEmpty = true) :
    ∃ d t, r = d :: t ∧ isDigit d = true := by
  match r, h with
  | [], h => simp at h
  | d :: t, h =>
    refine ⟨d, t, rfl, ?_⟩
    simp only [List.takeWhile_cons] at h
    split at h
    · assumption
    · simp at h

theorem expR_plus (r : List UInt8) : expR (0x2B :: r) =
    if (r.takeWhile isDigit).isEmpty then none else some (r.dropWhile isDigit) := rfl

theorem expR_minus (r : List UInt8) : expR (0x2D :: r) =
    if (r.takeWhile isDigit).isEmpty then none else some (r.dropWhile isDigit) := rfl

theorem expR_other {y : List UInt8} (h1 : ∀ r, y ≠ 0x2B :: r) (h2 : ∀ r, y ≠ 0x2D :: r) :
    expR y = if (y.takeWhile isDigit).isEmpty then none else some (y.dropWhile isDigit) := by
  unfold expR
  have : signPart y = ([], y) := by
    unfold signPart
    split
    · exact absurd rfl (h1 _)
    · exact absurd rfl (h2 _)
    · rfl
  rw [this]

set_option hygiene false in
/-- The exponent part of `numFE`, from `h` about the exponent's match on `v`, to `afterExp v`. -/
local macro "expTac" : tactic => `(tactic| (
  split at h
  · rename_i e y
    show (if e = 0x65 ∨ e = 0x45 then expR y else some (e :: y)) = _
    by_cases he : (e == 0x65 || e == 0x45) = true
    · have he' : e = 0x65 ∨ e = 0x45 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at he; exact he
      rw [if_pos he']
      simp only [he, ↓reduceIte] at h
      split at h
      · rename_i r
        rw [expR_plus]
        simp only [digits] at h
        by_cases hc : (List.takeWhile isDigit r).isEmpty = true
        · simp [hc] at h
        · simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h ⊢
          exact h.2
      · rename_i r
        rw [expR_minus]
        simp only [digits] at h
        by_cases hc : (List.takeWhile isDigit r).isEmpty = true
        · simp [hc] at h
        · simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h ⊢
          exact h.2
      · rename_i h1 h2
        rw [expR_other h1 h2]
        simp only [digits] at h
        by_cases hc : (List.takeWhile isDigit y).isEmpty = true
        · simp [hc] at h
        · simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h ⊢
          exact h.2
    · have he' : ¬ (e = 0x65 ∨ e = 0x45) := by
        intro hh; apply he; rcases hh with rfl | rfl <;> decide
      rw [if_neg he']
      simp only [he, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact h.2
  · simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    show some [] = _
    rw [h.2]))

/-- After the integer part, `numFE` (the model) reads what `afterInt` reads. -/
theorem numFE_after {pre u text rest : List UInt8} (h : numFE pre u = some (text, rest)) :
    afterInt u = some rest := by
  unfold numFE at h
  split at h
  · rename_i x
    simp only [digits] at h
    by_cases hc : (List.takeWhile isDigit x).isEmpty = true
    · simp [hc] at h
    · simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨d, t, hx, hd⟩ := tw_ne hc
      show fracR x = some rest
      unfold fracR
      rw [hx]
      simp only [hd, ↓reduceIte]
      rw [← hx]
      generalize List.dropWhile isDigit x = v at h ⊢
      expTac
  · rename_i hn
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    have hai : afterInt u = afterExp u := by
      unfold afterInt
      split
      · exact absurd rfl (hn _)
      · rfl
    rw [hai]
    expTac

theorem digit_cases {d : UInt8} (h : isDigit d = true) (h0 : d ≠ 0x30) :
    d = 0x31 ∨ d = 0x32 ∨ d = 0x33 ∨ d = 0x34 ∨ d = 0x35 ∨ d = 0x36 ∨ d = 0x37 ∨ d = 0x38 ∨ d = 0x39 := by
  have hr := isDigit_range h
  have h0' : d.toNat ≠ 48 := fun e => h0 (UInt8.toNat_inj.mp (by rw [e]; rfl))
  have : d.toNat = 49 ∨ d.toNat = 50 ∨ d.toNat = 51 ∨ d.toNat = 52 ∨ d.toNat = 53 ∨ d.toNat = 54 ∨
    d.toNat = 55 ∨ d.toNat = 56 ∨ d.toNat = 57 := by omega
  rcases this with e | e | e | e | e | e | e | e | e <;> simp [← UInt8.toNat_inj, e]

theorem number_zero (t : List UInt8) : number (0x30 :: t) = numFE ([] ++ [0x30]) t := by
  unfold number numFE; rfl

theorem number_dig {d : UInt8} (t : List UInt8) (hd : isDigit d = true) (h0 : d ≠ 0x30) :
    number (d :: t) = numFE ([] ++ (d :: t).takeWhile isDigit) ((d :: t).dropWhile isDigit) := by
  rcases digit_cases hd h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold number numFE; rfl)

theorem dw_cons {d : UInt8} (t : List UInt8) (hd : isDigit d = true) :
    (d :: t).dropWhile isDigit = t.dropWhile isDigit := by
  simp [hd]

theorem numFE_digit {pre : List UInt8} {e : UInt8} {u : List UInt8} (hde : isDigit e = true) :
    numFE pre (e :: u) = some (pre ++ [] ++ [], e :: u) := by
  have := isDigit_range hde
  have h1 : e ≠ 0x2E := by intro x; rw [x] at this; simp at this
  have h2 : (e == 0x65 || e == 0x45) = false := by
    have a1 : e ≠ 0x65 := by intro x; rw [x] at this; simp at this
    have a2 : e ≠ 0x45 := by intro x; rw [x] at this; simp at this
    simp [a1, a2]
  unfold numFE
  split
  · rename_i x heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h1
  · simp only [Option.bind_eq_bind, Option.bind_some, h2, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- **The model's numbers, read as 83 reads them**: a number that starts with a digit, read by
`number` up to `rest`, and not `0` followed by a digit, is read by `intR` up to `rest`. -/
theorem number_intR {d : UInt8} {t text rest : List UInt8} (hd : isDigit d = true)
    (h : number (d :: t) = some (text, rest))
    (he : ¬ (text = [0x30] ∧ ∃ e u, rest = e :: u ∧ isDigit e = true)) : intR (d :: t) = some rest := by
  simp only [intR]
  by_cases h0 : d = 0x30
  · subst h0
    simp only [ite_true]
    rw [number_zero] at h
    match t, h, he with
    | [], h, _ =>
      have := numFE_after h
      simpa [afterInt, afterExp] using this
    | e :: u, h, he =>
      simp only
      by_cases hde : isDigit e = true
      · exfalso
        apply he
        rw [numFE_digit hde] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact ⟨by rw [← h1]; rfl, e, u, h2.symm, hde⟩
      · rw [if_neg hde]
        exact numFE_after h
  · rw [if_neg h0, if_pos hd]
    rw [number_dig t hd h0, dw_cons t hd] at h
    exact numFE_after h

theorem number_neg_zero (t : List UInt8) : number (0x2D :: 0x30 :: t) = numFE ([0x2D] ++ [0x30]) t := by
  unfold number numFE; rfl

theorem number_neg_dig {d : UInt8} (t : List UInt8) (hd : isDigit d = true) (h0 : d ≠ 0x30) :
    number (0x2D :: d :: t) = numFE ([0x2D] ++ (d :: t).takeWhile isDigit) ((d :: t).dropWhile isDigit) := by
  rcases digit_cases hd h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold number numFE; rfl)

theorem number_neg_bad {x : UInt8} (t : List UInt8) (hx : isDigit x = false) : number (0x2D :: x :: t) = none := by
  unfold number
  simp only
  split
  · rename_i r heq
    simp only [List.cons.injEq] at heq
    rw [heq.1] at hx; exact absurd hx (by decide)
  · rename_i b tl heq
    simp only [List.cons.injEq] at heq
    rw [← heq.1, hx]
    rfl
  · rename_i heq; simp at heq

theorem number_neg_nil : number [0x2D] = none := by
  unfold number; rfl

/-- `-` then a number that `intR` reads (not `-0` followed by a digit). -/
theorem number_neg_intR {t text rest : List UInt8} (h : number (0x2D :: t) = some (text, rest))
    (he : ¬ (text = [0x2D, 0x30] ∧ ∃ e u, rest = e :: u ∧ isDigit e = true)) : intR t = some rest := by
  match t, h, he with
  | [], h, _ => rw [number_neg_nil] at h; simp at h
  | d :: t, h, he =>
    by_cases hd : isDigit d = true
    · simp only [intR]
      by_cases h0 : d = 0x30
      · subst h0
        simp only [ite_true]
        rw [number_neg_zero] at h
        match t, h, he with
        | [], h, _ =>
          have := numFE_after h
          simpa [afterInt, afterExp] using this
        | e :: u, h, he =>
          simp only
          by_cases hde : isDigit e = true
          · exfalso
            apply he
            rw [numFE_digit hde] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            exact ⟨by rw [← h1]; rfl, e, u, h2.symm, hde⟩
          · rw [if_neg hde]
            exact numFE_after h
      · rw [if_neg h0, if_pos hd]
        rw [number_neg_dig t hd h0, dw_cons t hd] at h
        exact numFE_after h
    · rw [number_neg_bad t (by simpa using hd)] at h; simp at h

/-- The model's value at a digit is a number. -/
theorem valueR_num {d : UInt8} {t r : List UInt8} {v : Value} (hd : isDigit d = true)
    (h : valueR (d :: t) = some (v, r)) :
    ∃ text s, number (d :: t) = some (text, r) ∧ String.fromUTF8? ⟨text.toArray⟩ = some s ∧ v = .number s := by
  have := isDigit_range hd
  rw [valueR_eq, skip_of_not t (SerdeStructModel.isDigit_not_ws hd)] at h
  split at h
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at this; simp at this
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨text, r'⟩, hn, s, hs, rfl, rfl⟩ := h
    exact ⟨text, s, hn, hs, rfl⟩

/-- The model's value at `-` is a number. -/
theorem valueR_neg {t r : List UInt8} {v : Value} (h : valueR (0x2D :: t) = some (v, r)) :
    ∃ text s, number (0x2D :: t) = some (text, r) ∧ String.fromUTF8? ⟨text.toArray⟩ = some s ∧ v = .number s := by
  have hv : valueR (0x2D :: t) = (number (0x2D :: t)).bind fun x =>
      (String.fromUTF8? ⟨x.1.toArray⟩).map fun s => (Value.number s, x.2) := by
    rw [valueR_eq, skip_of_not t rfl]; rfl
  rw [hv] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨text, r'⟩, hn, s, hs, rfl, rfl⟩ := h
  exact ⟨text, s, hn, hs, rfl⟩

theorem utf8_zero : String.fromUTF8? ⟨#[0x30]⟩ = some "0" := by decide

theorem utf8_neg_zero : String.fromUTF8? ⟨#[0x2D, 0x30]⟩ = some "-0" := by decide

/-- **serde's skip of a number at a digit, as 83 reads it.** -/
theorem vSkip_num {d : UInt8} {t r : List UInt8} (hd : isDigit d = true) (h : vSkip (d :: t) = some r) :
    intR (d :: t) = some r := by
  unfold vSkip at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, r'⟩, hv, h2⟩ := h
  obtain ⟨text, s, hn, hs, rfl⟩ := valueR_num hd hv
  dsimp only at h2
  split at h2
  · simp at h2
  · rename_i hne
    simp only [Option.some.injEq] at h2
    subst h2
    refine number_intR hd hn ?_
    rintro ⟨rfl, e, u, rfl, hde⟩
    apply hne
    have : s = "0" := by
      have := utf8_zero
      simp only [List.toArray] at hs
      rw [show (⟨[0x30].toArray⟩ : ByteArray) = ⟨#[0x30]⟩ from rfl] at hs
      rw [hs] at this; exact Option.some.inj this
    subst this
    simp [early, hde]

/-- **serde's skip of a number at `-`**: after it, as 83 reads it. -/
theorem vSkip_neg {t r : List UInt8} (h : vSkip (0x2D :: t) = some r) : intR t = some r := by
  unfold vSkip at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, r'⟩, hv, h2⟩ := h
  obtain ⟨text, s, hn, hs, rfl⟩ := valueR_neg hv
  dsimp only at h2
  split at h2
  · simp at h2
  · rename_i hne
    simp only [Option.some.injEq] at h2
    subst h2
    refine number_neg_intR hn ?_
    rintro ⟨rfl, e, u, rfl, hde⟩
    apply hne
    have : s = "-0" := by
      have := utf8_neg_zero
      rw [show (⟨[0x2D, 0x30].toArray⟩ : ByteArray) = ⟨#[0x2D, 0x30]⟩ from rfl] at hs
      rw [hs] at this; exact Option.some.inj this
    subst this
    simp [early, hde]

end WNear.SerdeNumModel
