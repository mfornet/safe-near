import Model.Args

/-!
# `NearInterface.Json.value` without its fuel (M6, pure)

The model's `value`, `elements` and `members` take a fuel that bounds the nesting depth, and
`parse` gives them `2 · len + 2`. serde_json's code has no such fuel. This file shows the fuel
does not matter once it is large enough for the input:

* `skip_length`, `stringBody_length`, `number_length`: each reader returns a strict suffix
  (`stringBody`, `number`) or a suffix (`skipWhitespace`).
* `value_length`: `value`, `elements` and `members` consume at least one byte.
* `fuel_stable`: from `2 · len + 1` for `value` (`2 · len + 2` for `elements` and `members`),
  one more fuel gives the same result. `value_fuel`, `members_fuel`, `elements_fuel`: so any
  larger fuel does.
* `valueR`, `membersR`, `elementsR`: the fuel-free functions, and their unfolding equations
  (`valueR_eq`, `membersR_eq`, `elementsR_eq`), which read like the grammar.
-/

namespace WNear.JsonFuel

open NearInterface.Json

theorem skip_suffix (bs : List UInt8) : ∃ k, bs = k ++ skipWhitespace bs := by
  unfold skipWhitespace
  exact ⟨bs.takeWhile isWhitespace, (List.takeWhile_append_dropWhile).symm⟩

theorem skip_length (bs : List UInt8) : (skipWhitespace bs).length ≤ bs.length := by
  obtain ⟨k, hk⟩ := skip_suffix bs
  have := congrArg List.length hk
  simp at this; omega

theorem skip_idem (bs : List UInt8) : skipWhitespace (skipWhitespace bs) = skipWhitespace bs := by
  unfold skipWhitespace
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : isWhitespace b = true
    · simp only [List.dropWhile_cons, h, ite_true]; exact ih
    · simp only [List.dropWhile_cons, h]; simp [h]

/-- A list that starts with a non-whitespace byte after `skipWhitespace`. -/
theorem skip_cons {bs r : List UInt8} {b : UInt8} (h : skipWhitespace bs = b :: r) : isWhitespace b = false := by
  have := skip_idem bs
  rw [h] at this
  unfold skipWhitespace at this
  cases hb : isWhitespace b
  · rfl
  · simp only [List.dropWhile_cons, hb, ite_true] at this
    have h1 := congrArg List.length this
    have h2 := (List.dropWhile_sublist (p := isWhitespace) (l := r)).length_le
    simp at h1; omega

theorem skip_of_not {b : UInt8} (rest : List UInt8) (h : isWhitespace b = false) :
    skipWhitespace (b :: rest) = b :: rest := by
  simp [skipWhitespace, h]

/-- After `skipWhitespace`, a byte and the rest: the rest is shorter than the input. -/
theorem skip_cons_length {bs r : List UInt8} {b : UInt8} (h : skipWhitespace bs = b :: r) :
    r.length < bs.length := by
  have := skip_length bs
  rw [h] at this; simp at this; omega

theorem stringBody_length (n : Nat) : ∀ (bs acc : List UInt8) (s : Option String) (r : List UInt8),
    bs.length ≤ n → stringBody bs acc = some (s, r) → r.length < bs.length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro bs acc s r hn h
  rw [stringBody.eq_def] at h
  split at h
  all_goals (try simp at h)
  · obtain ⟨_, rfl⟩ := h; simp
  · split at h
    all_goals first
      | (have := ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h; simp; omega)
      | (split at h
         · split at h
           · have := ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h; simp; omega
           · simp at h
         · simp at h)
      | simp at h
  · have := ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h.2; simp; omega

theorem digits_length (bs : List UInt8) : (digits bs).2.length ≤ bs.length := by
  simp only [digits]; exact (List.dropWhile_sublist (p := isDigit) (l := bs)).length_le

theorem digits_length' {bs a r : List UInt8} (h : digits bs = (a, r)) : r.length ≤ bs.length := by
  have := digits_length bs; rw [h] at this; exact this

theorem number_length (bs t r : List UInt8) (h : number bs = some (t, r)) : r.length ≤ bs.length := by
  unfold number at h
  split at h
  rename_i x sign b0 hs
  have hs0 : b0.length ≤ bs.length := by
    split at hs <;> simp at hs <;> (obtain ⟨_, rfl⟩ := hs) <;> simp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i1, i2⟩, h1, h⟩ := h
  have hi : i2.length ≤ b0.length := by
    split at h1
    · simp at h1; obtain ⟨_, rfl⟩ := h1; simp
    · split at h1
      · simp at h1; have := digits_length' h1; omega
      · simp at h1
    · simp at h1
  simp only at h
  have hd := fun l => digits_length l
  repeat (any_goals (first | (simp only [Option.bind, Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
  all_goals (obtain ⟨-, rfl⟩ := h)
  all_goals grind

theorem stringBody_len {bs acc : List UInt8} {s : Option String} {r : List UInt8}
    (h : stringBody bs acc = some (s, r)) : r.length < bs.length :=
  stringBody_length bs.length bs acc s r le_rfl h

/-! ### `value` returns a suffix -/

theorem value_length (f : Nat) :
    (∀ bs v r, value f bs = some (v, r) → r.length ≤ bs.length) ∧
    (∀ bs acc vs r, elements f bs acc = some (vs, r) → r.length ≤ bs.length) ∧
    (∀ bs acc ms r, members f bs acc = some (ms, r) → r.length ≤ bs.length) := by
  induction f with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [value, elements, members]
  | succ f ih =>
    obtain ⟨ihv, ihe, ihm⟩ := ih
    have hsb : ∀ bs acc (x : Option String × List UInt8), stringBody bs acc = some x → x.2.length < bs.length :=
      fun bs acc x h => stringBody_len (s := x.1) (by simpa using h)
    have hnum : ∀ bs (x : List UInt8 × List UInt8), number bs = some x → x.2.length ≤ bs.length :=
      fun bs x h => number_length bs x.1 x.2 (by simpa using h)
    have hv' : ∀ bs (x : Value × List UInt8), value f bs = some x → x.2.length ≤ bs.length :=
      fun bs x h => ihv bs x.1 x.2 (by simpa using h)
    have he' : ∀ bs acc (x : List Value × List UInt8), elements f bs acc = some x → x.2.length ≤ bs.length :=
      fun bs acc x h => ihe bs acc x.1 x.2 (by simpa using h)
    have hm' : ∀ bs acc (x : List (Option String × Value) × List UInt8), members f bs acc = some x →
        x.2.length ≤ bs.length :=
      fun bs acc x h => ihm bs acc x.1 x.2 (by simpa using h)
    have hsk := fun l => skip_length l
    refine ⟨?_, ?_, ?_⟩
    · intro bs v r h
      rw [value.eq_def] at h
      have hsk := skip_length bs
      repeat (any_goals (first | (simp only [Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (obtain ⟨-, rfl⟩ := h)
      all_goals grind
    · intro bs acc vs r h
      rw [elements.eq_def] at h
      repeat (any_goals (first | (simp only [Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (try obtain ⟨-, rfl⟩ := h)
      all_goals grind
    · intro bs acc ms r h
      rw [members.eq_def] at h
      repeat (any_goals (first | (simp only [Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (try obtain ⟨-, rfl⟩ := h)
      all_goals grind

/-! ### The fuel does not matter once large enough -/

theorem fuel_stable (f : Nat) :
    (∀ bs, 2 * bs.length + 1 ≤ f → value f bs = value (f + 1) bs) ∧
    (∀ bs acc, 2 * bs.length + 2 ≤ f → elements f bs acc = elements (f + 1) bs acc) ∧
    (∀ bs acc, 2 * bs.length + 2 ≤ f → members f bs acc = members (f + 1) bs acc) := by
  induction f with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega
  | succ f ih =>
    obtain ⟨ihv, ihe, ihm⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro bs hf
      have hsk := skip_length bs
      unfold value
      generalize skipWhitespace bs = s at hsk ⊢
      split
      all_goals (try rfl)
      · rw [ihe _ _ (by simp at hsk; omega)]
      · rw [ihm _ _ (by simp at hsk; omega)]
    · intro bs acc hf
      unfold elements
      rw [ihv bs (by omega)]
      simp only [Option.bind_eq_bind]
      cases hv : value (f + 1) bs with
      | none => rfl
      | some x =>
        obtain ⟨v, r⟩ := x
        have hr := (value_length (f + 1)).1 bs v r hv
        simp only [Option.bind]
        split
        all_goals (try rfl)
        rename_i heq
        have := skip_cons_length heq
        rw [ihe _ _ (by omega)]
    · intro bs acc hf
      unfold members
      simp only [Option.bind_eq_bind]
      split
      all_goals (try rfl)
      rename_i rest heq
      have h1 := skip_cons_length heq
      cases hk : stringBody rest [] with
      | none => rfl
      | some x =>
        obtain ⟨key, r1⟩ := x
        have h2 := stringBody_len hk
        simp only [Option.bind]
        split
        all_goals (try rfl)
        rename_i r2 heq2
        have h3 := skip_cons_length heq2
        rw [ihv r2 (by omega)]
        cases hv : value (f + 1) r2 with
        | none => rfl
        | some x =>
          obtain ⟨v, r3⟩ := x
          have h4 := (value_length (f + 1)).1 r2 v r3 hv
          simp only
          split
          all_goals (try rfl)
          rename_i r4 heq4
          have h5 := skip_cons_length heq4
          rw [ihm _ _ (by omega)]

theorem value_fuel {f : Nat} {bs : List UInt8} (h : 2 * bs.length + 1 ≤ f) :
    value f bs = value (2 * bs.length + 1) bs := by
  obtain ⟨k, rfl⟩ : ∃ k, f = 2 * bs.length + 1 + k := ⟨f - (2 * bs.length + 1), by omega⟩
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, ← (fuel_stable _).1 bs (by omega), ih (by omega)]

theorem elements_fuel {f : Nat} {bs : List UInt8} {acc : List Value} (h : 2 * bs.length + 2 ≤ f) :
    elements f bs acc = elements (2 * bs.length + 2) bs acc := by
  obtain ⟨k, rfl⟩ : ∃ k, f = 2 * bs.length + 2 + k := ⟨f - (2 * bs.length + 2), by omega⟩
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, ← (fuel_stable _).2.1 bs acc (by omega), ih (by omega)]

theorem members_fuel {f : Nat} {bs : List UInt8} {acc : List (Option String × Value)}
    (h : 2 * bs.length + 2 ≤ f) :
    members f bs acc = members (2 * bs.length + 2) bs acc := by
  obtain ⟨k, rfl⟩ : ∃ k, f = 2 * bs.length + 2 + k := ⟨f - (2 * bs.length + 2), by omega⟩
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, ← (fuel_stable _).2.2 bs acc (by omega), ih (by omega)]

/-! ### The fuel-free grammar -/

/-- `value` with enough fuel. -/
def valueR (bs : List UInt8) : Option (Value × List UInt8) := value (2 * bs.length + 1) bs

/-- `elements` with enough fuel. -/
def elementsR (bs : List UInt8) (acc : List Value) : Option (List Value × List UInt8) :=
  elements (2 * bs.length + 2) bs acc

/-- `members` with enough fuel. -/
def membersR (bs : List UInt8) (acc : List (Option String × Value)) :
    Option (List (Option String × Value) × List UInt8) :=
  members (2 * bs.length + 2) bs acc

theorem valueR_length {bs : List UInt8} {v : Value} {r : List UInt8} (h : valueR bs = some (v, r)) :
    r.length ≤ bs.length := (value_length _).1 bs v r h

/-- `parse` is `valueR`, then only whitespace. -/
theorem parse_eq (bs : List UInt8) :
    parse bs = match valueR bs with
      | some (v, rest) => if skipWhitespace rest = [] then some v else none
      | none => none := by
  unfold parse valueR
  rw [value_fuel (f := 2 * bs.length + 2) (by omega)]
  cases value (2 * bs.length + 1) bs <;> rfl

theorem valueR_eq (bs : List UInt8) :
    valueR bs = match skipWhitespace bs with
    | 0x6E :: 0x75 :: 0x6C :: 0x6C :: rest => some (.null, rest)
    | 0x74 :: 0x72 :: 0x75 :: 0x65 :: rest => some (.bool true, rest)
    | 0x66 :: 0x61 :: 0x6C :: 0x73 :: 0x65 :: rest => some (.bool false, rest)
    | 0x22 :: rest => (stringBody rest []).map fun (s, rest) =>
      ((match s with | some s => .str s | none => .invalidStr), rest)
    | 0x5B :: rest =>
      match skipWhitespace rest with
      | 0x5D :: rest => some (.arr [], rest)
      | _ => (elementsR rest []).map fun (vs, rest) => (.arr vs, rest)
    | 0x7B :: rest =>
      match skipWhitespace rest with
      | 0x7D :: rest => some (.obj [], rest)
      | _ => (membersR rest []).map fun (ms, rest) => (.obj ms, rest)
    | bs => (number bs).bind fun (text, rest) =>
      (String.fromUTF8? ⟨text.toArray⟩).map fun t => (.number t, rest) := by
  unfold valueR elementsR membersR
  have hsk := skip_length bs
  unfold value
  generalize skipWhitespace bs = s at hsk ⊢
  split
  all_goals (try rfl)
  · rw [elements_fuel (by simp at hsk; omega)]; rfl
  · rw [members_fuel (by simp at hsk; omega)]; rfl
  · split <;> (try (exfalso; simp_all; done)) <;> rfl

/-- After an element: `,` and more elements, or `]`. -/
def elemEnd (v : Value) (acc : List Value) (rest : List UInt8) : Option (List Value × List UInt8) :=
  match skipWhitespace rest with
  | 0x2C :: rest => elementsR rest (v :: acc)
  | 0x5D :: rest => some ((v :: acc).reverse, rest)
  | _ => none

theorem elementsR_eq (bs : List UInt8) (acc : List Value) :
    elementsR bs acc = (valueR bs).bind fun (v, rest) => elemEnd v acc rest := by
  conv_lhs => unfold elementsR elements
  unfold valueR
  simp only [Option.bind_eq_bind]
  cases hv : value (2 * bs.length + 1) bs with
  | none => rfl
  | some x =>
    obtain ⟨v, r⟩ := x
    have hr := (value_length _).1 bs v r hv
    simp only [Option.bind, elemEnd]
    generalize hs : skipWhitespace r = s
    split
    · have := skip_cons_length hs
      rw [elements_fuel (by omega)]; rfl
    · rfl
    · split <;> (try (exfalso; simp_all; done)) <;> rfl

/-- A member's key: whitespace, then a string. -/
def keyAt (bs : List UInt8) : Option (Option String × List UInt8) :=
  match skipWhitespace bs with
  | 0x22 :: rest => stringBody rest []
  | _ => none

/-- A member's colon: whitespace, then `:`. -/
def colonAt (bs : List UInt8) : Option (List UInt8) :=
  match skipWhitespace bs with
  | 0x3A :: rest => some rest
  | _ => none

theorem keyAt_quote {bs rest : List UInt8} (h : skipWhitespace bs = 0x22 :: rest) :
    keyAt bs = stringBody rest [] := by
  unfold keyAt; rw [h]; rfl

theorem keyAt_other {bs : List UInt8} (h : ∀ rest, skipWhitespace bs ≠ 0x22 :: rest) : keyAt bs = none := by
  unfold keyAt; split
  · exact absurd ‹_› (h _)
  · rfl

theorem colonAt_colon {bs rest : List UInt8} (h : skipWhitespace bs = 0x3A :: rest) : colonAt bs = some rest := by
  unfold colonAt; rw [h]; rfl

theorem colonAt_other {bs : List UInt8} (h : ∀ rest, skipWhitespace bs ≠ 0x3A :: rest) : colonAt bs = none := by
  unfold colonAt; split
  · exact absurd ‹_› (h _)
  · rfl

/-- After a member: `,` and more members, or `}`. -/
def memberEnd (k : Option String) (v : Value) (acc : List (Option String × Value)) (rest : List UInt8) :
    Option (List (Option String × Value) × List UInt8) :=
  match skipWhitespace rest with
  | 0x2C :: rest => membersR rest ((k, v) :: acc)
  | 0x7D :: rest => some (((k, v) :: acc).reverse, rest)
  | _ => none

theorem membersR_eq (bs : List UInt8) (acc : List (Option String × Value)) :
    membersR bs acc = (keyAt bs).bind fun (key, rest) => (colonAt rest).bind fun rest =>
      (valueR rest).bind fun (v, rest) =>
      memberEnd key v acc rest := by
  conv_lhs => unfold membersR members
  simp only [Option.bind_eq_bind]
  split
  · rename_i rest hs0
    rw [keyAt_quote hs0]
    have h1 := skip_cons_length hs0
    cases hk : stringBody rest [] with
    | none => rfl
    | some x =>
      obtain ⟨key, r1⟩ := x
      have h2 := stringBody_len hk
      simp only [Option.bind]
      split
      · rename_i r2 hs1
        rw [colonAt_colon hs1]
        have h3 := skip_cons_length hs1
        rw [value_fuel (f := 2 * bs.length + 1) (by omega)]
        simp only [valueR]
        cases hv : value (2 * r2.length + 1) r2 with
        | none => rfl
        | some x =>
          obtain ⟨v, r3⟩ := x
          have h4 := (value_length _).1 r2 v r3 hv
          simp only [memberEnd]
          generalize hs2 : skipWhitespace r3 = s2
          split
          · have h5 := skip_cons_length hs2
            rw [members_fuel (by omega)]; rfl
          · rfl
          · split <;> (try (exfalso; simp_all; done)) <;> rfl
      · rename_i hn
        rw [colonAt_other (fun r h => hn r h)]
  · rename_i hn
    rw [keyAt_other (fun r h => hn r h)]
    rfl
end WNear.JsonFuel
