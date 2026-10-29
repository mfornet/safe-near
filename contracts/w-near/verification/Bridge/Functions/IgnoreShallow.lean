import Bridge.Functions.IgnoreModel
import Bridge.Functions.JsonSuffix

/-!
# The shallow skip: a scalar, or one bracket of scalars (M6, pure)

`ignore_value` (81) keeps the frames of nested brackets on the scratch `Vec`, which it grows from
capacity 0 when a second bracket opens inside a first. The proof of 81 covers the values that never
push a frame: a scalar, or one `[`/`{` whose elements or members' values are scalars. `ign1` reads
exactly those, with the steps of `IgnoreModel.ignM` at depth at most 1:

* `scal s`: a value that is not a bracket, as serde skips it (`vSkip`);
* `cont1 f n r`: after a value in the frame `f`, `,` and the next scalar element or member, or the
  closing bracket (fuel `n`);
* `open1 f n r`: just after the bracket `f`, the closing bracket or the first element or member;
* `ign1 bs`: a scalar, or a bracket of scalars; `ign1R` in the shape of a value reader.

Soundness (`ign1_sound`): `ign1` reads what serde's skip reads (`vSkip`), so the struct machine with
`ign1R` accepts only where the model does (`decode_of_shallow`).
-/

namespace WNear.IgnoreShallow

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel WNear.IgnoreModel

/-- A key's body after its `"`, as 650 skips it. -/
def sk (r : List UInt8) : Option (List UInt8) := (stringBody r []).map (·.2)

/-- A value that is not a bracket. -/
def scal (s : List UInt8) : Option (List UInt8) :=
  match skipWhitespace s with
  | 0x5B :: _ => none
  | 0x7B :: _ => none
  | t => vSkip t

/-- After a value in the frame `f`, no frame deeper: `,` and the next element or member, or the
closing bracket. -/
def cont1 (f : UInt8) : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | n + 1, r =>
    match skipWhitespace r with
    | 0x2C :: r' =>
      if f = 0x5B then (scal r').bind (cont1 f n) else keyThen sk r' fun r3 => (scal r3).bind (cont1 f n)
    | 0x5D :: r' => if f = 0x5B then some r' else none
    | 0x7D :: r' => if f = 0x5B then none else some r'
    | _ => none

/-- Just after the bracket `f`: the closing bracket, or the first element or member. -/
def open1 (f : UInt8) (n : Nat) (r : List UInt8) : Option (List UInt8) :=
  if f = 0x5B then
    match skipWhitespace r with
    | 0x5D :: r' => some r'
    | s => (scal s).bind (cont1 f n)
  else
    match skipWhitespace r with
    | 0x7D :: r' => some r'
    | s => keyThen sk s fun r3 => (scal r3).bind (cont1 f n)

/-- **The shallow skip**: a scalar, or one bracket of scalars. -/
def ign1 (bs : List UInt8) : Option (List UInt8) :=
  match skipWhitespace bs with
  | 0x5B :: r => open1 0x5B bs.length r
  | 0x7B :: r => open1 0x7B bs.length r
  | t => vSkip t

/-- `ign1` as a value reader. -/
def ign1R (bs : List UInt8) : Option (Unit × List UInt8) := (ign1 bs).map fun r => ((), r)

/-! ## Soundness -/

theorem closeAll_nil (r : List UInt8) : closeAll [] r = some r := rfl

theorem bind_closeAll_nil (x : Option (List UInt8)) : x.bind (closeAll []) = x := by
  cases x <;> rfl

theorem scal_sound {s r : List UInt8} (h : scal s = some r) : vSkip s = some r := by
  unfold scal at h
  rw [← vSkip_skip]
  split at h
  · simp at h
  · simp at h
  · exact h

theorem sk_eq (r : List UInt8) : sk r = (stringBody r []).map (·.2) := rfl

/-- A key, `:`, then `k`, read by `keyThen` or the model's `keyAt`/`colonAt`. -/
theorem keyThen_mono (r : List UInt8) (k k' : List UInt8 → Option (List UInt8))
    (hk : ∀ x y, k x = some y → k' x = some y) {y : List UInt8} (h : keyThen sk r k = some y) :
    ((keyAt r).bind fun x => (colonAt x.2).bind k') = some y := by
  rw [keyThen_eq sk sk_eq] at h
  simp only [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨x, hx, r2, hc, hk2⟩ := h
  exact ⟨x, hx, r2, hc, hk _ _ hk2⟩

theorem cont1_sound (f : UInt8) (hf : Br f) :
    ∀ n r r', cont1 f n r = some r' → closeAll [f] r = some r' := by
  intro n
  induction n with
  | zero => intro r r' h; simp [cont1] at h
  | succ n ih =>
    intro r r' h
    unfold cont1 at h
    generalize hs : skipWhitespace r = s at h
    split at h
    · rename_i r1
      by_cases hfa : f = 0x5B
      · subst hfa
        simp only [ite_true, Option.bind_eq_some_iff] at h
        obtain ⟨r2, h2, h3⟩ := h
        rw [close_arr_comma hs, scal_sound h2]
        exact ih _ _ h3
      · have hfo : f = 0x7B := hf.resolve_left hfa
        subst hfo
        simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
        rw [close_obj_comma hs]
        unfold memberStep
        refine keyThen_mono r1 _ _ ?_ h
        intro x y hxy
        simp only [Option.bind_eq_some_iff] at hxy ⊢
        obtain ⟨r2, h2, h3⟩ := hxy
        exact ⟨r2, scal_sound h2, ih _ _ h3⟩
    · rename_i r1
      by_cases hfa : f = 0x5B
      · subst hfa
        simp only [ite_true, Option.some.injEq] at h
        subst h
        rw [close_arr_end hs]; rfl
      · simp [hfa] at h
    · rename_i r1
      by_cases hfa : f = 0x5B
      · simp [hfa] at h
      · have hfo : f = 0x7B := hf.resolve_left hfa
        subst hfo
        simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false, Option.some.injEq] at h
        subst h
        rw [close_obj_end hs]; rfl
    · simp at h

theorem open1_sound (f : UInt8) (hf : Br f) (n : Nat) {r r' : List UInt8} (h : open1 f n r = some r') :
    vSkip (f :: r) = some r' := by
  have e : vSkip (f :: r) = (vSkip (f :: r)).bind (closeAll []) := (bind_closeAll_nil _).symm
  unfold open1 at h
  by_cases hfa : f = 0x5B
  · subst hfa
    simp only [ite_true] at h
    have h0 : skipWhitespace (0x5B :: r) = 0x5B :: r := skip_of_not r rfl
    split at h
    · rename_i r1 heq
      simp only [Option.some.injEq] at h
      subst h
      rw [e, vSkip_arrE h0 heq]; rfl
    · rename_i hn
      rw [e, vSkip_arrM h0 (fun r1 e => hn r1 e)]
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨r2, h2, h3⟩ := h
      exact ⟨r2, by rw [← vSkip_skip]; exact scal_sound h2, cont1_sound _ (Or.inl rfl) _ _ _ h3⟩
  · have hfo : f = 0x7B := hf.resolve_left hfa
    subst hfo
    simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
    have h0 : skipWhitespace (0x7B :: r) = 0x7B :: r := skip_of_not r rfl
    split at h
    · rename_i r1 heq
      simp only [Option.some.injEq] at h
      subst h
      rw [e, vSkip_objE h0 heq]; rfl
    · rename_i hn
      rw [e, vSkip_objM h0 (fun r1 e => hn r1 e)]
      unfold memberStep
      rw [← keyAt_skip r]
      refine keyThen_mono _ _ _ ?_ h
      intro x y hxy
      simp only [Option.bind_eq_some_iff] at hxy ⊢
      obtain ⟨r2, h2, h3⟩ := hxy
      exact ⟨r2, scal_sound h2, cont1_sound _ (Or.inr rfl) _ _ _ h3⟩

/-- **The shallow skip reads what serde's skip reads.** -/
theorem ign1_sound {bs r : List UInt8} (h : ign1 bs = some r) : vSkip bs = some r := by
  unfold ign1 at h
  rw [← vSkip_skip]
  split at h
  · rename_i r1 heq
    rw [heq]; exact open1_sound _ (Or.inl rfl) _ h
  · rename_i r1 heq
    rw [heq]; exact open1_sound _ (Or.inr rfl) _ h
  · exact h

/-! ## What serde's skip returns -/

theorem vSkip_valueR {bs r : List UInt8} (h : vSkip bs = some r) : ∃ v, valueR bs = some (v, r) := by
  unfold vSkip at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, r'⟩, hv, h⟩ := h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨v, hv⟩

theorem vSkip_suf {bs r : List UInt8} (h : vSkip bs = some r) : r <:+ bs := by
  obtain ⟨v, hv⟩ := vSkip_valueR h
  exact JsonSuffix.valueR_suf hv

theorem vSkip_strict {bs r : List UInt8} (h : vSkip bs = some r) : r.length < bs.length := by
  obtain ⟨v, hv⟩ := vSkip_valueR h
  exact JsonSuffix.valueR_strict hv

theorem ign1R_suf {bs r : List UInt8} (h : ign1R bs = some ((), r)) : r <:+ bs := by
  unfold ign1R at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r', h1, h2⟩ := h
  cases h2
  exact vSkip_suf (ign1_sound h1)

theorem ign1R_strict {bs r : List UInt8} (h : ign1R bs = some ((), r)) : r.length < bs.length := by
  unfold ign1R at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r', h1, h2⟩ := h
  cases h2
  exact vSkip_strict (ign1_sound h1)

/-- serde's skip as a value reader; it agrees with the model. -/
def vSkipR (bs : List UInt8) : Option (Unit × List UInt8) := (vSkip bs).map fun r => ((), r)

theorem ign1R_vSkipR {bs : List UInt8} {r : List UInt8} (h : ign1R bs = some ((), r)) : vSkipR bs = some ((), r) := by
  unfold ign1R at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r', h1, h2⟩ := h
  cases h2
  unfold vSkipR; rw [ign1_sound h1]; rfl

/-! ## The struct machine with the shallow skip -/

section Mono

variable {α : Type} (key : String) (dv : List UInt8 → Option (α × List UInt8))

theorem objLoop_mono (ign ign' : List UInt8 → Option (Unit × List UInt8))
    (hi : ∀ bs r, ign bs = some ((), r) → ign' bs = some ((), r)) :
    ∀ n seen bs x, objLoop key dv ign n seen bs = some x → objLoop key dv ign' n seen bs = some x := by
  intro n
  induction n with
  | zero => intro seen bs x h; simp [objLoop] at h
  | succ n ih =>
    intro seen bs x h
    unfold objLoop at h ⊢
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨k, rest⟩, hk, h⟩ := h
    refine ⟨(k, rest), hk, ?_⟩
    dsimp only at h ⊢
    cases k with
    | none => simp at h
    | some k =>
      dsimp only at h ⊢
      split at h
      · simp at h
      · rename_i hdup
        rw [if_neg hdup]
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨rest2, hc, ⟨seen', rest3⟩, hv, h⟩ := h
        refine ⟨rest2, hc, (seen', rest3), ?_, ?_⟩
        · split at hv
          · rw [if_pos ‹_›]; exact hv
          · rw [if_neg ‹_›]
            simp only [Option.map_eq_some_iff] at hv ⊢
            obtain ⟨⟨u, r4⟩, h4, h5⟩ := hv
            exact ⟨(u, r4), hi _ _ h4, h5⟩
        · dsimp only at h ⊢
          split at h
          · exact ih _ _ _ h
          · exact h
          · simp at h

theorem structDe_mono (ign ign' : List UInt8 → Option (Unit × List UInt8))
    (hi : ∀ bs r, ign bs = some ((), r) → ign' bs = some ((), r)) (bs : List UInt8) (x : α × List UInt8)
    (h : structDe key dv ign bs = some x) : structDe key dv ign' bs = some x := by
  unfold structDe at h ⊢
  split at h
  · split at h
    · simp at h
    · simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨y, hy, h⟩ := h
      exact ⟨y, objLoop_mono key dv ign ign' hi _ _ _ _ hy, h⟩
  · exact h
  · rename_i h1 h2
    simp at h

end Mono

/-- **The shallow machine accepts only what the model accepts**: where serde's struct machine with
the shallow skip reads `a` and then only whitespace, `Call.decode` reads `ftBalanceOf a`. -/
theorem decode_of_shallow {bs : List UInt8} {a : WNear.AccountId} {r : List UInt8}
    (hS : structDe "account_id" (valueAs WNear.account) ign1R bs = some (a, r)) (hE : skipWhitespace r = []) :
    WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a) := by
  have hag : Agrees vSkipR valueSkip := vSkip_agrees
  rw [decode_balanceOf (valueAs WNear.account) vSkipR (fun _ => Or.inl rfl) hag bs]
  unfold fromSlice
  rw [structDe_mono "account_id" (valueAs WNear.account) ign1R vSkipR (fun _ _ h => ign1R_vSkipR h) bs _ hS]
  simp [endOk, hE]

end WNear.IgnoreShallow
