import Bridge.Functions.IgnoreShallow
import Bridge.Functions.SerdeNumModel
import Bridge.Functions.SerdeKeyNoEsc
import Bridge.Functions.SerdeIgnStr

/-!
# `ignore_value` (81): the model's side of its dispatch (M6, pure)

Where 81 reads a value at a byte `b` (after the whitespace), serde's skip `vSkip` says what follows:

* `vSkip_byte`: a string (`"` and a `stringBody`), a number (`-` or a digit, then `intR`), one of the
  literals `true`, `false`, `null`, or a bracket; nothing else, and nothing at the end of the input
  (`vSkip_nil`);
* `str_split`: on an input without `\`, a string body is plain bytes up to its closing `"`.
-/

namespace WNear.Binary.SerdeIgnPure

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel WNear.IgnoreModel WNear.SerdeNumModel
open WNear.Binary.ParseStr (plain)

theorem vSkip_nil : vSkip [] = none := by
  unfold vSkip; rw [JsonSuffix.valueR_nil]; rfl

theorem number_other {b : UInt8} (x : List UInt8) (hm : b ≠ 0x2D) (hd : isDigit b = false) :
    number (b :: x) = none := by
  have h0 : b ≠ 0x30 := by intro h; subst h; exact absurd hd (by decide)
  simp [number, hm, hd, h0]

theorem ite_none_some {c : Bool} {a b : List UInt8} (h : (if c = true then none else some a) = some b) : a = b := by
  cases c <;> simp at h; exact h

/-- **What serde's skip reads at the byte `b`.** -/
theorem vSkip_byte {b : UInt8} {x r : List UInt8} (hw : isWhitespace b = false) (h : vSkip (b :: x) = some r) :
    (b = 0x22 ∧ ∃ s, stringBody x [] = some (s, r)) ∨
    (b = 0x2D ∧ intR x = some r) ∨
    (isDigit b = true ∧ intR (b :: x) = some r) ∨
    (b = 0x74 ∧ x = [0x72, 0x75, 0x65] ++ r) ∨
    (b = 0x66 ∧ x = [0x61, 0x6C, 0x73, 0x65] ++ r) ∨
    (b = 0x6E ∧ x = [0x75, 0x6C, 0x6C] ++ r) ∨
    b = 0x5B ∨ b = 0x7B := by
  by_cases hm : b = 0x2D
  · subst hm; exact Or.inr (Or.inl ⟨rfl, vSkip_neg h⟩)
  by_cases hd : isDigit b = true
  · exact Or.inr (Or.inr (Or.inl ⟨hd, vSkip_num hd h⟩))
  have hd' : isDigit b = false := by simpa using hd
  unfold vSkip at h
  rw [valueR_eq, skip_of_not x hw] at h
  split at h
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [early] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [early] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [early] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, ⟨⟨s, r''⟩, hs, he⟩, h⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    dsimp only at h
    have := ite_none_some h
    subst this
    exact Or.inl ⟨rfl, s, hs⟩
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl heq.1))))))
  · rename_i rest heq
    simp only [List.cons.injEq] at heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr heq.1))))))
  · rw [number_other x hm hd'] at h
    simp at h

/-- On an input without `\`, a string body is its plain bytes, then the closing quote. -/
theorem str_split {bs : List UInt8} (hnb : (0x5C : UInt8) ∉ bs) {q : Nat} {s : Option String} {r : List UInt8}
    (hs : stringBody (bs.drop q) [] = some (s, r)) :
    bs.drop q = SerdeKeyNoEsc.keyBody bs q ++ 0x22 :: r ∧ ∀ b ∈ SerdeKeyNoEsc.keyBody bs q, plain b = true := by
  have hsplit : bs.drop q = SerdeKeyNoEsc.keyBody bs q ++ (bs.drop q).dropWhile plain :=
    List.takeWhile_append_dropWhile.symm
  have hplain : ∀ b ∈ SerdeKeyNoEsc.keyBody bs q, plain b = true := fun b hb => SerdeKeyNoEsc.takeWhile_mem hb
  have hstop : ∀ x rest, (bs.drop q).dropWhile plain = x :: rest → plain x = false ∧ x ≠ 0x5C := by
    intro x rest h
    refine ⟨SerdeKeyNoEsc.dropWhile_head h, ?_⟩
    intro e
    subst e
    apply hnb
    have hm : (0x5C : UInt8) ∈ (bs.drop q).dropWhile plain := by rw [h]; exact List.mem_cons_self
    exact List.mem_of_mem_drop ((List.dropWhile_sublist _).subset hm)
  rw [hsplit] at hs
  have ht := SerdeIgnStr.str_noesc_shape _ _ hplain hstop hs
  rw [ht] at hsplit
  exact ⟨hsplit, hplain⟩

/-! ## The shallow skip, step by step -/

open WNear.IgnoreShallow (scal cont1 open1 ign1 sk)

/-- A scalar at a byte: not a bracket, and serde's skip reads it. -/
theorem scal_cons {s x r1 : List UInt8} {b : UInt8} (h : scal s = some r1) (hs : skipWhitespace s = b :: x) :
    b ≠ 0x5B ∧ b ≠ 0x7B ∧ vSkip (b :: x) = some r1 := by
  unfold scal at h
  rw [hs] at h
  by_cases h1 : b = 0x5B
  · subst h1; simp at h
  by_cases h2 : b = 0x7B
  · subst h2; simp at h
  refine ⟨h1, h2, ?_⟩
  split at h
  · rename_i t heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h1
  · rename_i t heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h2
  · exact h

/-- The shallow skip at a byte: a bracket, or a scalar. -/
theorem ign1_cons {s x r : List UInt8} {b : UInt8} (h : ign1 s = some r) (hs : skipWhitespace s = b :: x) :
    (b = 0x5B ∧ open1 0x5B s.length x = some r) ∨ (b = 0x7B ∧ open1 0x7B s.length x = some r) ∨
      (b ≠ 0x5B ∧ b ≠ 0x7B ∧ vSkip (b :: x) = some r) := by
  unfold ign1 at h
  rw [hs] at h
  by_cases h1 : b = 0x5B
  · subst h1; exact Or.inl ⟨rfl, h⟩
  by_cases h2 : b = 0x7B
  · subst h2; exact Or.inr (Or.inl ⟨rfl, h⟩)
  refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
  split at h
  · rename_i t heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h1
  · rename_i t heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h2
  · exact h

theorem scal_nil {s : List UInt8} (hs : skipWhitespace s = []) : scal s = none := by
  unfold scal; rw [hs]; exact vSkip_nil

theorem keyThen_nil {s : List UInt8} {k : List UInt8 → Option (List UInt8)} (hs : skipWhitespace s = []) :
    keyThen sk s k = none := by
  unfold keyThen; rw [hs]

/-- Nothing left: the container does not end. -/
theorem cont_nil (fb : UInt8) (N : Nat) {s : List UInt8} (hs : skipWhitespace s = []) :
    open1 fb N s = none ∧ cont1 fb N s = none := by
  constructor
  · unfold open1
    rw [hs]
    split
    · show (scal []).bind (cont1 fb N) = none
      rw [scal_nil rfl]; rfl
    · exact keyThen_nil rfl
  · cases N with
    | zero => rfl
    | succ N => unfold cont1; rw [hs]

theorem vSkip_close {c : UInt8} {x : List UInt8} (hc : c = 0x5D ∨ c = 0x7D ∨ c = 0x2C) : vSkip (c :: x) = none := by
  cases h : vSkip (c :: x) with
  | none => rfl
  | some r =>
    exfalso
    have hw : isWhitespace c = false := by rcases hc with rfl | rfl | rfl <;> rfl
    rcases vSkip_byte hw h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨hd, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | rfl | rfl <;>
      (try (rcases hc with h | h | h <;> exact absurd h (by decide)))
    rcases hc with rfl | rfl | rfl <;> exact absurd hd (by decide)

theorem keyThen_other {c : UInt8} {x : List UInt8} {k : List UInt8 → Option (List UInt8)} (hw : isWhitespace c = false)
    (hc : c ≠ 0x22) : keyThen sk (c :: x) k = none := by
  unfold keyThen
  rw [skip_of_not x hw]
  split
  · rename_i r1 heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hc
  · rfl

/-- Just after a bracket, at the byte `c`: the closing bracket, or (not `]`, `}`, `,`) the first
element or member from there. -/
theorem open1_cons {fb : UInt8} {N : Nat} {s x r : List UInt8} {c : UInt8} (hf : Br fb)
    (h : open1 fb N s = some r) (hs : skipWhitespace s = c :: x) :
    (fb = 0x5B ∧ c = 0x5D ∧ r = x) ∨ (fb = 0x7B ∧ c = 0x7D ∧ r = x) ∨
    (c ≠ 0x5D ∧ c ≠ 0x7D ∧ c ≠ 0x2C ∧ (fb = 0x5B → (scal (c :: x)).bind (cont1 fb N) = some r) ∧
      (fb = 0x7B → keyThen sk (c :: x) (fun r3 => (scal r3).bind (cont1 fb N)) = some r)) := by
  have hw : isWhitespace c = false := skip_cons hs
  have hss : skipWhitespace (c :: x) = c :: x := skip_of_not x hw
  unfold open1 at h
  rw [hs] at h
  rcases hf with rfl | rfl
  · simp only [ite_true] at h
    by_cases h1 : c = 0x5D
    · subst h1; simp only [Option.some.injEq] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
    have h' : (scal (c :: x)).bind (cont1 0x5B N) = some r := by
      split at h
      · rename_i r' heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h1
      · exact h
    have hcl : c ≠ 0x7D ∧ c ≠ 0x2C := by
      constructor
      · intro e
        subst e
        have e1 := vSkip_close (c := 0x7D) (x := x) (by decide)
        unfold scal at h'
        rw [hss] at h'
        simp [e1] at h'
      · intro e
        subst e
        have e1 := vSkip_close (c := 0x2C) (x := x) (by decide)
        unfold scal at h'
        rw [hss] at h'
        simp [e1] at h'
    exact Or.inr (Or.inr ⟨h1, hcl.1, hcl.2, fun _ => h', fun e => absurd e (by decide)⟩)
  · simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
    by_cases h1 : c = 0x7D
    · subst h1; simp only [Option.some.injEq] at h; exact Or.inr (Or.inl ⟨rfl, rfl, h.symm⟩)
    have h' : keyThen sk (c :: x) (fun r3 => (scal r3).bind (cont1 0x7B N)) = some r := by
      split at h
      · rename_i r' heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h1
      · exact h
    have hq : c = 0x22 := by
      by_contra hq; rw [keyThen_other hw hq] at h'; simp at h'
    subst hq
    exact Or.inr (Or.inr ⟨by decide, by decide, by decide, fun e => absurd e (by decide), fun _ => h'⟩)

/-- After a value in the frame, at the byte `c`: the closing bracket, or `,` and the next element or
member. -/
theorem cont1_cons {fb : UInt8} {N : Nat} {s x r : List UInt8} {c : UInt8} (hf : Br fb)
    (h : cont1 fb N s = some r) (hs : skipWhitespace s = c :: x) :
    ∃ N', N = N' + 1 ∧ ((fb = 0x5B ∧ c = 0x5D ∧ r = x) ∨ (fb = 0x7B ∧ c = 0x7D ∧ r = x) ∨
      (c = 0x2C ∧ (fb = 0x5B → (scal x).bind (cont1 fb N') = some r) ∧
        (fb = 0x7B → keyThen sk x (fun r3 => (scal r3).bind (cont1 fb N')) = some r))) := by
  cases N with
  | zero => simp [cont1] at h
  | succ N' =>
    refine ⟨N', rfl, ?_⟩
    unfold cont1 at h
    rw [hs] at h
    by_cases h1 : c = 0x2C
    · subst h1
      simp only at h
      rcases hf with rfl | rfl
      · simp only [ite_true] at h
        exact Or.inr (Or.inr ⟨rfl, fun _ => h, fun e => absurd e (by decide)⟩)
      · simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
        exact Or.inr (Or.inr ⟨rfl, fun e => absurd e (by decide), fun _ => h⟩)
    by_cases h2 : c = 0x5D
    · subst h2
      simp only at h
      rcases hf with rfl | rfl
      · simp only [ite_true, Option.some.injEq] at h
        exact Or.inl ⟨rfl, rfl, h.symm⟩
      · simp at h
    by_cases h3 : c = 0x7D
    · subst h3
      simp only at h
      rcases hf with rfl | rfl
      · simp at h
      · simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false, Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨rfl, rfl, h.symm⟩)
    exfalso
    split at h
    · rename_i r' heq; simp only [List.cons.injEq] at heq; exact h1 heq.1
    · rename_i r' heq; simp only [List.cons.injEq] at heq; exact h2 heq.1
    · rename_i r' heq; simp only [List.cons.injEq] at heq; exact h3 heq.1
    · simp at h

theorem scal_suf {s r : List UInt8} (h : scal s = some r) : r <:+ s := by
  unfold scal at h
  split at h
  · simp at h
  · simp at h
  · exact (IgnoreShallow.vSkip_suf h).trans (JsonSuffix.skip_suf s)

/-- A key read by `keyThen`: `"`, its body, `:`. -/
theorem keyThen_some {r : List UInt8} {k : List UInt8 → Option (List UInt8)} {y : List UInt8}
    (h : keyThen sk r k = some y) :
    ∃ r1 s r2 r3, skipWhitespace r = 0x22 :: r1 ∧ stringBody r1 [] = some (s, r2) ∧
      skipWhitespace r2 = 0x3A :: r3 ∧ k r3 = some y := by
  unfold keyThen at h
  split at h
  · rename_i r1 heq
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r2, hs, h⟩ := h
    unfold sk at hs
    simp only [Option.map_eq_some_iff] at hs
    obtain ⟨⟨s, r2'⟩, hs, rfl⟩ := hs
    split at h
    · rename_i r3 heq3
      exact ⟨r1, s, r2', r3, heq, hs, heq3, h⟩
    · simp at h
  · simp at h

theorem keyThen_suf {r : List UInt8} {k : List UInt8 → Option (List UInt8)} {y : List UInt8}
    (hk : ∀ x z, k x = some z → z <:+ x) (h : keyThen sk r k = some y) : y <:+ r := by
  obtain ⟨r1, s, r2, r3, h1, h2, h3, h4⟩ := keyThen_some h
  exact (hk _ _ h4).trans ((JsonSuffix.cons_suf h3).trans ((JsonSuffix.stringBody_suf' h2).trans
    (JsonSuffix.cons_suf h1)))

theorem cont1_suf (f : UInt8) : ∀ n r r', cont1 f n r = some r' → r' <:+ r := by
  intro n
  induction n with
  | zero => intro r r' h; simp [cont1] at h
  | succ n ih =>
    intro r r' h
    unfold cont1 at h
    generalize hs : skipWhitespace r = s at h
    split at h
    · rename_i r1
      have s1 : r1 <:+ r := JsonSuffix.cons_suf hs
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨r2, h2, h3⟩ := h
        exact (ih _ _ h3).trans ((scal_suf h2).trans s1)
      · refine (keyThen_suf ?_ h).trans s1
        intro x z hz
        simp only [Option.bind_eq_some_iff] at hz
        obtain ⟨r2, h2, h3⟩ := hz
        exact (ih _ _ h3).trans (scal_suf h2)
    · rename_i r1
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact JsonSuffix.cons_suf hs
      · simp at h
    · rename_i r1
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h; subst h; exact JsonSuffix.cons_suf hs
    · simp at h

theorem scal_lt {s r : List UInt8} (h : scal s = some r) : r.length < (skipWhitespace s).length := by
  unfold scal at h
  split at h
  · simp at h
  · simp at h
  · exact IgnoreShallow.vSkip_strict h

theorem keyThen_lt {r : List UInt8} {k : List UInt8 → Option (List UInt8)} {y : List UInt8}
    (hk : ∀ x z, k x = some z → z <:+ x) (h : keyThen sk r k = some y) : y.length < (skipWhitespace r).length := by
  obtain ⟨r1, s, r2, r3, h1, h2, h3, h4⟩ := keyThen_some h
  rw [h1]
  have := ((hk _ _ h4).trans ((JsonSuffix.cons_suf h3).trans (JsonSuffix.stringBody_suf' h2))).length_le
  simp; omega

theorem kont_suf (f : UInt8) (N : Nat) : ∀ x z, (scal x).bind (cont1 f N) = some z → z <:+ x := by
  intro x z h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨r1, h1, h2⟩ := h
  exact (cont1_suf f N r1 z h2).trans (scal_suf h1)

/-- After a bracket, the container reads at least its first byte. -/
theorem open1_lt {fb : UInt8} {N : Nat} {s r : List UInt8} (hf : Br fb) (h : open1 fb N s = some r) :
    r.length < (skipWhitespace s).length := by
  cases hs : skipWhitespace s with
  | nil => rw [(cont_nil fb N hs).1] at h; simp at h
  | cons c x =>
    rcases open1_cons hf h hs with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, h5, h7⟩
    · simp
    · simp
    · have hw : isWhitespace c = false := skip_cons hs
      have hss : skipWhitespace (c :: x) = c :: x := skip_of_not x hw
      rcases hf with rfl | rfl
      · have h' := h5 rfl
        simp only [Option.bind_eq_some_iff] at h'
        obtain ⟨r1, h1, h2⟩ := h'
        have := scal_lt h1
        rw [hss] at this
        have := (cont1_suf _ _ _ _ h2).length_le
        omega
      · have := keyThen_lt (kont_suf _ N) (h7 rfl)
        rw [hss] at this
        exact this

/-- After a value in the frame, the container reads at least the next byte. -/
theorem cont1_lt {fb : UInt8} {N : Nat} {s r : List UInt8} (hf : Br fb) (h : cont1 fb N s = some r) :
    r.length < (skipWhitespace s).length := by
  cases hs : skipWhitespace s with
  | nil => rw [(cont_nil fb N hs).2] at h; simp at h
  | cons c x =>
    obtain ⟨N', -, hc⟩ := cont1_cons hf h hs
    rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, h5, h7⟩
    · simp
    · simp
    · rcases hf with rfl | rfl
      · have := (kont_suf _ N' _ _ (h5 rfl)).length_le
        simp; omega
      · have := (keyThen_suf (kont_suf _ N') (h7 rfl)).length_le
        simp; omega

end WNear.Binary.SerdeIgnPure
