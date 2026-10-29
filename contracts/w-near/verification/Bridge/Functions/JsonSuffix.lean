import Bridge.Functions.SerdeStructModel

/-!
# The model's readers return a suffix of their input (M6, pure)

`JsonFuel` proves that each reader of `NearInterface.Json` consumes bytes (`value_length`,
`stringBody_len`). The binary's specifications speak of positions in the input (`bs.drop i`), so
the proofs of 228 and 66 need more: the rest a reader returns is a suffix of its input, hence the
input from the position `|bs| - |r|` (`drop_suf`). This file proves it for `skipWhitespace`,
`stringBody`, `number`, `value`/`elements`/`members` (`value_suf`), the fuel-free `valueR`, and
serde's struct machine (`structDe_suf`), from readers `dv` and `ign` that return suffixes; and
that a reader that agrees with the model (`Agrees`) returns a suffix and reads nothing from the
empty input (`agrees_suf`, `agrees_nil`).
-/

namespace WNear.JsonSuffix

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel

theorem drop_suf {r bs : List UInt8} (h : r <:+ bs) : bs.drop (bs.length - r.length) = r :=
  (List.suffix_iff_eq_drop.mp h).symm

theorem drop_suf' {r bs : List UInt8} {j : Nat} (h : r <:+ bs.drop j) : bs.drop (bs.length - r.length) = r :=
  drop_suf (h.trans (List.drop_suffix j bs))

theorem skip_suf (bs : List UInt8) : skipWhitespace bs <:+ bs := List.dropWhile_suffix _

theorem cons_suf {bs r : List UInt8} {b : UInt8} (h : skipWhitespace bs = b :: r) : r <:+ bs := by
  have := skip_suf bs
  rw [h] at this
  exact (List.suffix_cons b r).trans this

theorem hex4_suf {bs r : List UInt8} {n : Nat} (h : hex4 bs = some (n, r)) : r <:+ bs := by
  unfold hex4 at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact List.suffix_append [_, _, _, _] _
  · simp at h

theorem unicodeEscape_suf {bs r : List UInt8} {c : Char} (h : unicodeEscape bs = some (c, r)) : r <:+ bs := by
  unfold unicodeEscape at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨n, rest⟩, h1, h⟩ := h
  have s1 := hex4_suf h1
  split at h
  · split at h
    · rename_i rest2 hrest
      have s0 : rest2 <:+ rest := by
        simp only at hrest; rw [hrest]; exact List.suffix_append [0x5C, 0x75] rest2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨m, rest3⟩, h2, h⟩ := h
      have s2 := hex4_suf h2
      split at h
      · split at h
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact s2.trans (s0.trans s1)
        · simp at h
      · simp at h
    · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact s1
      · simp at h

theorem stringBody_suf (n : Nat) : ∀ (bs acc : List UInt8) (s : Option String) (r : List UInt8),
    bs.length ≤ n → stringBody bs acc = some (s, r) → r <:+ bs := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro bs acc s r hn h
  rw [stringBody.eq_def] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.suffix_cons _ _
  · rename_i e rest
    have hst : rest <:+ 0x5C :: e :: rest := (List.suffix_cons _ _).trans (List.suffix_cons _ _)
    split at h
    all_goals first
      | exact (ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h).trans hst
      | (split at h
         · rename_i c rest' hu
           split at h
           · exact ((ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h).trans (unicodeEscape_suf hu)).trans hst
           · simp at h
         · simp at h)
      | simp at h
  · rename_i b rest _ _
    split at h
    · simp at h
    · exact (ih _ (by simp at hn ⊢; omega) _ _ _ _ le_rfl h).trans (List.suffix_cons _ _)

theorem stringBody_suf' {bs acc : List UInt8} {s : Option String} {r : List UInt8}
    (h : stringBody bs acc = some (s, r)) : r <:+ bs :=
  stringBody_suf bs.length bs acc s r le_rfl h

theorem digits_suf (bs : List UInt8) : (digits bs).2 <:+ bs := by
  simp only [digits]; exact List.dropWhile_suffix _

theorem digits_suf' {bs a r : List UInt8} (h : digits bs = (a, r)) : r <:+ bs := by
  have := digits_suf bs; rw [h] at this; exact this

theorem number_suf {bs t r : List UInt8} (h : number bs = some (t, r)) : r <:+ bs := by
  unfold number at h
  split at h
  rename_i x sign b0 hs
  have hs0 : b0 <:+ bs := by
    split at hs <;> simp at hs <;> (obtain ⟨_, rfl⟩ := hs)
    · exact List.suffix_cons _ _
    · exact List.suffix_refl _
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i1, i2⟩, h1, h⟩ := h
  have hi : i2 <:+ b0 := by
    split at h1
    · simp at h1; obtain ⟨_, rfl⟩ := h1; exact List.suffix_cons _ _
    · split at h1
      · simp at h1; exact digits_suf' h1
      · simp at h1
    · simp at h1
  simp only at h
  have hd := fun l => digits_suf l
  have hc := fun (b : UInt8) (l : List UInt8) => List.suffix_cons b l
  repeat (any_goals (first | (simp only [Option.bind, Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
  all_goals (obtain ⟨-, rfl⟩ := h)
  all_goals grind [List.IsSuffix.trans]

theorem value_suf (f : Nat) :
    (∀ bs v r, value f bs = some (v, r) → r <:+ bs) ∧
    (∀ bs acc vs r, elements f bs acc = some (vs, r) → r <:+ bs) ∧
    (∀ bs acc ms r, members f bs acc = some (ms, r) → r <:+ bs) := by
  induction f with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [value, elements, members]
  | succ f ih =>
    obtain ⟨ihv, ihe, ihm⟩ := ih
    have hsb : ∀ bs acc (x : Option String × List UInt8), stringBody bs acc = some x → x.2 <:+ bs :=
      fun bs acc x h => stringBody_suf' (s := x.1) (by simpa using h)
    have hnum : ∀ bs (x : List UInt8 × List UInt8), number bs = some x → x.2 <:+ bs :=
      fun bs x h => number_suf (t := x.1) (by simpa using h)
    have hv' : ∀ bs (x : Value × List UInt8), value f bs = some x → x.2 <:+ bs :=
      fun bs x h => ihv bs x.1 x.2 (by simpa using h)
    have he' : ∀ bs acc (x : List Value × List UInt8), elements f bs acc = some x → x.2 <:+ bs :=
      fun bs acc x h => ihe bs acc x.1 x.2 (by simpa using h)
    have hm' : ∀ bs acc (x : List (Option String × Value) × List UInt8), members f bs acc = some x →
        x.2 <:+ bs :=
      fun bs acc x h => ihm bs acc x.1 x.2 (by simpa using h)
    have hsk := fun l => skip_suf l
    have hc := fun (b : UInt8) (l : List UInt8) => List.suffix_cons b l
    refine ⟨?_, ?_, ?_⟩
    · intro bs v r h
      rw [value.eq_def] at h
      have hsk := skip_suf bs
      repeat (any_goals (first | (simp only [Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (obtain ⟨-, rfl⟩ := h)
      all_goals grind [List.IsSuffix.trans]
    · intro bs acc vs r h
      rw [elements.eq_def] at h
      repeat (any_goals (first | (simp only [Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (try obtain ⟨-, rfl⟩ := h)
      all_goals grind [List.IsSuffix.trans]
    · intro bs acc ms r h
      rw [members.eq_def] at h
      repeat (any_goals (first | (simp only [Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
      all_goals (try obtain ⟨-, rfl⟩ := h)
      all_goals grind [List.IsSuffix.trans]


theorem valueR_suf {bs r : List UInt8} {v : Value} (h : valueR bs = some (v, r)) : r <:+ bs :=
  (value_suf _).1 bs v r h

theorem keyAt_suf {bs r : List UInt8} {k : Option String} (h : keyAt bs = some (k, r)) : r <:+ bs := by
  unfold keyAt at h
  split at h
  · rename_i rest hs
    exact (stringBody_suf' h).trans (cons_suf hs)
  · simp at h

theorem colonAt_suf {bs r : List UInt8} (h : colonAt bs = some r) : r <:+ bs := by
  unfold colonAt at h
  split at h
  · rename_i rest hs
    simp only [Option.some.injEq] at h
    subst h
    exact cons_suf hs
  · simp at h

theorem valueR_nil : valueR [] = none := by decide

section Agree

variable {α : Type}

theorem valueAs_suf (dec : Value → Option α) {bs r : List UInt8} {a : α} (h : valueAs dec bs = some (a, r)) :
    r <:+ bs := by
  unfold valueAs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, _, _, _, e⟩ := h
  simp only at e
  subst e
  exact valueR_suf hv

theorem valueSkip_suf {bs r : List UInt8} (h : valueSkip bs = some ((), r)) : r <:+ bs := by
  unfold valueSkip at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, _, rfl⟩ := h
  exact valueR_suf hv

/-- A reader that agrees with one that returns suffixes returns suffixes. -/
theorem agrees_suf {β : Type} {f g : List UInt8 → Option (β × List UInt8)} (h : Agrees f g)
    (hg : ∀ bs x r, g bs = some (x, r) → r <:+ bs) (bs : List UInt8) (x : β) (r : List UInt8)
    (hf : f bs = some (x, r)) : r <:+ bs := by
  rcases h bs with e | ⟨e, _⟩
  · rw [e] at hf; exact hg bs x r hf
  · rw [e] at hf; simp at hf

/-- A reader that agrees with one that reads nothing from the empty input reads nothing from it. -/
theorem agrees_nil {β : Type} {f g : List UInt8 → Option (β × List UInt8)} (h : Agrees f g) (hg : g [] = none) :
    f [] = none := by
  rcases h [] with e | ⟨e, _⟩
  · rw [e, hg]
  · exact e

theorem valueAs_nil (dec : Value → Option α) : valueAs dec [] = none := by
  unfold valueAs; rw [valueR_nil]; rfl

theorem valueSkip_nil : valueSkip [] = none := by
  unfold valueSkip; rw [valueR_nil]; rfl

end Agree

section Machine

variable {α : Type} (key : String) (dv : List UInt8 → Option (α × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8))

theorem objLoop_suf (hdv : ∀ bs a r, dv bs = some (a, r) → r <:+ bs)
    (hign : ∀ bs r, ign bs = some ((), r) → r <:+ bs) :
    ∀ (n : Nat) (seen : Option α) (bs : List UInt8) (res : Option α × List UInt8),
      objLoop key dv ign n seen bs = some res → res.2 <:+ bs := by
  intro n
  induction n with
  | zero => intro seen bs res h; simp [objLoop] at h
  | succ n ih =>
    intro seen bs res h
    unfold objLoop at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨k, rest⟩, hk, h⟩ := h
    have s1 := keyAt_suf hk
    cases k with
    | none => simp at h
    | some k =>
      simp only at h
      split at h
      · simp at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨rest2, hc, ⟨seen', r3⟩, hv, h⟩ := h
        have s2 := colonAt_suf hc
        have s3 : r3 <:+ rest2 := by
          split at hv
          · simp only [Option.map_eq_some_iff] at hv
            obtain ⟨⟨a', r⟩, hd, he⟩ := hv
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact hdv _ _ _ hd
          · simp only [Option.map_eq_some_iff] at hv
            obtain ⟨⟨u, r⟩, hd, he⟩ := hv
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact hign _ _ hd
        have s123 := s3.trans (s2.trans s1)
        split at h
        · rename_i r4 hs
          exact (ih _ _ _ h).trans ((cons_suf hs).trans s123)
        · rename_i r4 hs
          simp only [Option.some.injEq] at h
          subst h
          exact (cons_suf hs).trans s123
        · simp at h

/-- **serde's struct machine returns a suffix of its input**, given readers that do. -/
theorem structDe_suf (hdv : ∀ bs a r, dv bs = some (a, r) → r <:+ bs)
    (hign : ∀ bs r, ign bs = some ((), r) → r <:+ bs) {bs r : List UInt8} {a : α}
    (h : structDe key dv ign bs = some (a, r)) : r <:+ bs := by
  unfold structDe at h
  split at h
  · rename_i rest hs
    split at h
    · simp at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨seen, r1⟩, h1, h2⟩ := h
      cases seen with
      | none => simp at h2
      | some a2 =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact (objLoop_suf key dv ign hdv hign _ _ _ _ h1).trans (cons_suf hs)
  · rename_i rest hs
    split at h
    · simp at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨a1, r1⟩, h1, h2⟩ := h
      have s1 := hdv _ _ _ h1
      split at h2
      · rename_i r2 hs2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact (cons_suf hs2).trans (s1.trans ((skip_suf rest).trans (cons_suf hs)))
      · simp at h2
  · simp at h

end Machine


/-! ### A value reads at least one byte -/

theorem number_strict {bs t r : List UInt8} (h : number bs = some (t, r)) : r.length < bs.length := by
  unfold number at h
  split at h
  rename_i x sign b0 hs
  have hs0 : b0.length ≤ bs.length := by
    split at hs <;> simp at hs <;> (obtain ⟨_, rfl⟩ := hs) <;> simp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i1, i2⟩, h1, h⟩ := h
  have hi : i2.length < b0.length := by
    split at h1
    · simp at h1; obtain ⟨_, rfl⟩ := h1; simp
    · rename_i b tl _
      split at h1
      · rename_i hb
        simp at h1
        have hd := digits_length' h1
        have e : (digits (b :: tl)).2 = (digits tl).2 := by simp [digits, List.dropWhile_cons, hb]
        rw [h1] at e
        simp only at e
        have := digits_length tl
        rw [← e] at this
        simp; omega
      · simp at h1
    · simp at h1
  simp only at h
  have hd := fun l => digits_length l
  repeat (any_goals (first | (simp only [Option.bind, Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
  all_goals (obtain ⟨-, rfl⟩ := h)
  all_goals grind

theorem value_strict (f : Nat) (bs : List UInt8) (v : Value) (r : List UInt8) (h : value f bs = some (v, r)) :
    r.length < bs.length := by
  cases f with
  | zero => simp [value] at h
  | succ f =>
    have hsb : ∀ bs acc (x : Option String × List UInt8), stringBody bs acc = some x → x.2.length < bs.length :=
      fun bs acc x h => stringBody_len (s := x.1) (by simpa using h)
    have hnum : ∀ bs (x : List UInt8 × List UInt8), number bs = some x → x.2.length < bs.length :=
      fun bs x h => number_strict (t := x.1) (by simpa using h)
    have he' : ∀ bs acc (x : List Value × List UInt8), elements f bs acc = some x → x.2.length ≤ bs.length :=
      fun bs acc x h => (value_length f).2.1 bs acc x.1 x.2 (by simpa using h)
    have hm' : ∀ bs acc (x : List (Option String × Value) × List UInt8), members f bs acc = some x →
        x.2.length ≤ bs.length :=
      fun bs acc x h => (value_length f).2.2 bs acc x.1 x.2 (by simpa using h)
    have hsk := skip_length bs
    have hskA := fun l => skip_length l
    rw [value.eq_def] at h
    repeat (any_goals (first | (simp only [Option.map, Option.bind, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) | split at h))
    all_goals (obtain ⟨-, rfl⟩ := h)
    all_goals grind

theorem valueR_strict {bs r : List UInt8} {v : Value} (h : valueR bs = some (v, r)) : r.length < bs.length :=
  value_strict _ bs v r h

theorem valueAs_strict {α : Type} (dec : Value → Option α) {bs r : List UInt8} {a : α}
    (h : valueAs dec bs = some (a, r)) : r.length < bs.length := by
  unfold valueAs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, _, _, _, e⟩ := h
  simp only at e
  subst e
  exact valueR_strict hv

theorem valueSkip_strict {bs r : List UInt8} (h : valueSkip bs = some ((), r)) : r.length < bs.length := by
  unfold valueSkip at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, _, rfl⟩ := h
  exact valueR_strict hv

/-- A reader that agrees with one that reads at least a byte reads at least a byte. -/
theorem agrees_strict {β : Type} {f g : List UInt8 → Option (β × List UInt8)} (h : Agrees f g)
    (hg : ∀ bs x r, g bs = some (x, r) → r.length < bs.length) (bs : List UInt8) (x : β) (r : List UInt8)
    (hf : f bs = some (x, r)) : r.length < bs.length := by
  rcases h bs with e | ⟨e, _⟩
  · rw [e] at hf; exact hg bs x r hf
  · rw [e] at hf; simp at hf

end WNear.JsonSuffix
