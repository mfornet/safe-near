import Bridge.Functions.SerdeStructModel
import Bridge.Functions.SerdeRead
import Bridge.Functions.SerdeNextKey

/-!
# serde's object loop as 228 runs it (M6, pure)

`SerdeStructModel.objLoop` reads a member from the key: it starts after `{` or after `,`. The
binary's loop (228 around `next_key_seed`, 193) starts each iteration before the `,`: 193 skips the
whitespace and eats the `,` itself, unless it is the first key (`first`). `loopRes` is `objLoop`
seen from the binary's loop head, and the step lemmas say what one iteration of the binary reads,
by the input's indices (`bs.drop i`):

* `loop_end`: `}` after the whitespace ends the loop, with the field read (only after a member);
* `loop_member`: otherwise a member: the key's body from `keyQ` (193), the key, the colon, then
  the field's value (`dv`) or an ignored one (`ign`), and the loop again, one fuel less.
-/

namespace WNear.SerdeStructLoop

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen skipWhitespace_eq)
open WNear.Binary.SerdeNextKey (keyQ)

section Loop

variable {α : Type} (key : String) (dv : List UInt8 → Option (α × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8))

/-- The object loop from the binary's loop head: `objLoop` on the first key, else after a `,`, or
the end `}`. -/
def loopRes (N : Nat) (first : Bool) (seen : Option α) (rest : List UInt8) : Option (Option α × List UInt8) :=
  if first then objLoop key dv ign N seen rest
  else match skipWhitespace rest with
    | 0x2C :: r => objLoop key dv ign N seen r
    | 0x7D :: r => some (seen, r)
    | _ => none

theorem drop_cons {bs r : List UInt8} {x : Nat} {b : UInt8} (h : bs.drop x = b :: r) :
    bs[x]? = some b ∧ r = bs.drop (x + 1) := by
  have h1 : (bs.drop x)[0]? = some b := by rw [h]; rfl
  rw [List.getElem?_drop] at h1
  refine ⟨by simpa using h1, ?_⟩
  rw [← List.drop_drop, h]; rfl

theorem skip_drop (bs : List UInt8) (x : Nat) :
    skipWhitespace (bs.drop x) = bs.drop (x + wsLen (bs.drop x)) := by
  rw [skipWhitespace_eq, List.drop_drop]

theorem skip_drop_cons {bs r : List UInt8} {x : Nat} {b : UInt8} (h : skipWhitespace (bs.drop x) = b :: r) :
    bs[x + wsLen (bs.drop x)]? = some b ∧ r = bs.drop (x + wsLen (bs.drop x) + 1) := by
  rw [skip_drop] at h; exact drop_cons h

theorem skip_drop_of {bs : List UInt8} {x : Nat} {b : UInt8} (h : bs[x + wsLen (bs.drop x)]? = some b) :
    skipWhitespace (bs.drop x) = b :: bs.drop (x + wsLen (bs.drop x) + 1) := by
  rw [skip_drop]
  have hl : x + wsLen (bs.drop x) < bs.length := WNear.Binary.SerdeNextKey.getElem_lt h
  rw [List.drop_eq_getElem_cons hl]
  rw [List.getElem?_eq_getElem hl] at h
  simp only [Option.some.injEq] at h
  rw [h]

/-- The loop ends at `}`: only after a member, with the field read, the rest past the `}`. -/
theorem loop_end {N : Nat} {first : Bool} {seen : Option α} {bs rF : List UInt8} {i : Nat} {a : α}
    (h : loopRes key dv ign N first seen (bs.drop i) = some (some a, rF))
    (hb : bs[i + wsLen (bs.drop i)]? = some 0x7D) :
    first = false ∧ seen = some a ∧ rF = bs.drop (i + wsLen (bs.drop i) + 1) := by
  have hs := skip_drop_of hb
  cases first with
  | true =>
    exfalso
    simp only [loopRes, if_true] at h
    cases N with
    | zero => simp [objLoop] at h
    | succ n =>
      unfold objLoop at h
      rw [show keyAt (bs.drop i) = none by unfold keyAt; rw [hs]; rfl] at h
      simp at h
  | false =>
    simp only [loopRes, Bool.false_eq_true, if_false, hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, h.1, h.2.symm⟩

/-- One member of `objLoop`: the key, not a duplicate, the colon, the value, then the loop from
after the value (`loopRes … false`). -/
theorem objLoop_succ {n : Nat} {seen : Option α} {rest : List UInt8} {res : Option α × List UInt8}
    (h : objLoop key dv ign (n + 1) seen rest = some res) :
    ∃ k rest1, keyAt rest = some (some k, rest1) ∧ ¬ (k = key ∧ seen.isSome = true) ∧
      ∃ rest2, colonAt rest1 = some rest2 ∧
      ((k = key ∧ ∃ a' r3, dv rest2 = some (a', r3) ∧ loopRes key dv ign n false (some a') r3 = some res) ∨
       (k ≠ key ∧ ∃ r3, ign rest2 = some ((), r3) ∧ loopRes key dv ign n false seen r3 = some res)) := by
  unfold objLoop at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨k, rest1⟩, hk, h⟩ := h
  cases k with
  | none => simp at h
  | some k =>
    simp only at h
    split at h
    · simp at h
    · rename_i hdup
      refine ⟨k, rest1, hk, hdup, ?_⟩
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨rest2, hc, ⟨seen', r3⟩, hv, h⟩ := h
      refine ⟨rest2, hc, ?_⟩
      by_cases hkk : k = key
      · left
        refine ⟨hkk, ?_⟩
        simp only [hkk, if_true, Option.map_eq_some_iff] at hv
        obtain ⟨⟨a', r⟩, hd, he⟩ := hv
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨a', r, hd, ?_⟩
        simp only [loopRes, Bool.false_eq_true, if_false]
        exact h
      · right
        refine ⟨hkk, ?_⟩
        simp only [hkk, if_false, Option.map_eq_some_iff] at hv
        obtain ⟨⟨u, r⟩, hd, he⟩ := hv
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨r, hd, ?_⟩
        simp only [loopRes, Bool.false_eq_true, if_false]
        exact h

/-- A member at the binary's loop head (not `}`): one fuel less, the key's body at `keyQ`, then
`objLoop_succ`'s member. -/
theorem loop_member {N : Nat} {first : Bool} {seen : Option α} {bs : List UInt8} {res : Option α × List UInt8}
    {i : Nat} (h : loopRes key dv ign N first seen (bs.drop i) = some res)
    (hb : bs[i + wsLen (bs.drop i)]? ≠ some 0x7D) :
    ∃ n q k rest1, N = n + 1 ∧ keyQ first bs i = some q ∧ stringBody (bs.drop q) [] = some (some k, rest1) ∧
      ¬ (k = key ∧ seen.isSome = true) ∧
      ∃ rest2, colonAt rest1 = some rest2 ∧
      ((k = key ∧ ∃ a' r3, dv rest2 = some (a', r3) ∧ loopRes key dv ign n false (some a') r3 = some res) ∨
       (k ≠ key ∧ ∃ r3, ign rest2 = some ((), r3) ∧ loopRes key dv ign n false seen r3 = some res)) := by
  -- the rest after `{` or `,` where `objLoop` starts, and the key's body in it
  obtain ⟨x, hx, hq⟩ : ∃ x, objLoop key dv ign N seen (bs.drop x) = some res ∧
      ∀ k rest1, keyAt (bs.drop x) = some (some k, rest1) →
        ∃ q, keyQ first bs i = some q ∧ stringBody (bs.drop q) [] = some (some k, rest1) := by
    have key_of : ∀ y, (keyQ first bs i = some (y + wsLen (bs.drop y) + 1)) → bs[y + wsLen (bs.drop y)]? = some 0x22 →
        ∀ k rest1, keyAt (bs.drop y) = some (some k, rest1) →
        ∃ q, keyQ first bs i = some q ∧ stringBody (bs.drop q) [] = some (some k, rest1) := by
      intro y hy hy2 k rest1 hk
      refine ⟨_, hy, ?_⟩
      rw [keyAt_quote (skip_drop_of hy2)] at hk
      exact hk
    cases first with
    | true =>
      refine ⟨i, by simpa [loopRes] using h, ?_⟩
      intro k rest1 hk
      unfold keyAt at hk
      split at hk
      · rename_i rest hs
        obtain ⟨h1, -⟩ := skip_drop_cons hs
        exact key_of i (by simp [keyQ, h1]) h1 k rest1 (by unfold keyAt; rw [hs]; exact hk)
      · simp at hk
    | false =>
      simp only [loopRes, Bool.false_eq_true, if_false] at h
      split at h
      · rename_i r hs
        obtain ⟨h1, rfl⟩ := skip_drop_cons hs
        refine ⟨_, h, ?_⟩
        intro k rest1 hk
        unfold keyAt at hk
        split at hk
        · rename_i rest hs2
          obtain ⟨h2, -⟩ := skip_drop_cons hs2
          exact key_of _ (by simp [keyQ, h1, h2]) h2 k rest1 (by unfold keyAt; rw [hs2]; exact hk)
        · simp at hk
      · rename_i r hs
        exact absurd (skip_drop_cons hs).1 hb
      · simp at h
  cases N with
  | zero => simp [objLoop] at hx
  | succ n =>
    obtain ⟨k, rest1, hk, hdup, rest2, hc, hv⟩ := objLoop_succ key dv ign hx
    obtain ⟨q, hq1, hq2⟩ := hq k rest1 hk
    exact ⟨n, q, k, rest1, rfl, hq1, hq2, hdup, rest2, hc, hv⟩

end Loop

end WNear.SerdeStructLoop
