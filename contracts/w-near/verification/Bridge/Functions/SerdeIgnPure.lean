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

end WNear.Binary.SerdeIgnPure
