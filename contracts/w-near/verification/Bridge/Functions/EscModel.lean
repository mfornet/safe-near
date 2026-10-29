import Bridge.Functions.SerdeEscRead

/-!
# An escape in a JSON string, on the model's side (M6)

`escDecode` is what `parse_escape` (649) does with the bytes after a `\`, written with the model's own
`unicodeEscape`: the decoded bytes and how many bytes the escape takes, or `none`.

* `stringBody_esc`: `stringBody` on `\` then `rest` is `stringBody` on what follows the escape, the
  decoded bytes pushed, or `none` when `escDecode` fails. So 649 and the model agree on every escape.
-/

namespace WNear.Binary.ParseEscape

open NearInterface.Json (hexValue hex4 unicodeEscape stringBody)

/-- `parse_escape` on the bytes after the `\`, as the model decodes it: the bytes and how many
bytes the escape takes, or `none`. -/
def escDecode : List UInt8 → Option (List UInt8 × Nat)
  | [] => none
  | e :: rest =>
    if e = 0x22 then some ([0x22], 1) else if e = 0x5C then some ([0x5C], 1)
    else if e = 0x2F then some ([0x2F], 1) else if e = 0x62 then some ([0x08], 1)
    else if e = 0x66 then some ([0x0C], 1) else if e = 0x6E then some ([0x0A], 1)
    else if e = 0x72 then some ([0x0D], 1) else if e = 0x74 then some ([0x09], 1)
    else if e = 0x75 then
      (unicodeEscape rest).map fun (c, rest') => (String.utf8EncodeChar c, 1 + (rest.length - rest'.length))
    else none

/-- The number of bytes the escape appends (1 when it fails). -/
def escK (l : List UInt8) : Nat :=
  match escDecode l with | some (o, _) => o.length | none => 1

theorem hex4_some (l r : List UInt8) (v : Nat) (h : hex4 l = some (v, r)) : 4 ≤ l.length ∧ r = l.drop 4 := by
  rw [SerdeEsc.hex4_eq] at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    exact ⟨by assumption, rfl⟩
  · simp at h

/-- What `unicodeEscape` leaves is a suffix of its input, at least 4 bytes shorter. -/
theorem ue_suffix (rest r : List UInt8) (c : Char) (h : unicodeEscape rest = some (c, r)) :
    4 ≤ rest.length - r.length ∧ r = rest.drop (rest.length - r.length) := by
  unfold unicodeEscape at h
  cases h4 : hex4 rest with
  | none => simp [h4] at h
  | some p =>
    obtain ⟨n, r1⟩ := p
    obtain ⟨hl1, rfl⟩ := hex4_some _ _ _ h4
    simp only [h4, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · rename_i r2 heq
        cases h5 : hex4 r2 with
        | none => simp [h5] at h
        | some q =>
          obtain ⟨m, r3⟩ := q
          obtain ⟨hl2, rfl⟩ := hex4_some _ _ _ h5
          simp only [h5, Option.bind_some] at h
          split at h
          · split at h
            · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              have e : rest.drop 4 = 0x5C :: 0x75 :: r2 := heq
              have hl : (rest.drop 4).length = r2.length + 2 := by rw [e]; simp
              simp only [List.length_drop] at hl ⊢
              refine ⟨by omega, ?_⟩
              rw [show rest.length - (r2.length - 4) = 4 + 2 + 4 by omega, ← List.drop_drop, ← List.drop_drop, e]
              simp
            · simp at h
          · simp at h
      · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          simp only [List.length_drop]
          refine ⟨by omega, ?_⟩
          rw [show rest.length - (rest.length - 4) = 4 by omega]
        · simp at h

/-- **An escape against the model**: `stringBody` past a `\` follows `escDecode`. -/
theorem stringBody_esc (rest acc : List UInt8) :
    stringBody (0x5C :: rest) acc =
      match escDecode rest with
      | some (out, m) => stringBody (rest.drop m) (out.reverse ++ acc)
      | none => none := by
  match rest with
  | [] => simp [stringBody, escDecode]
  | e :: rest =>
    by_cases h22 : e = 0x22
    · subst h22; simp [escDecode, stringBody]
    by_cases h5c : e = 0x5C
    · subst h5c; simp [escDecode, stringBody]
    by_cases h2f : e = 0x2F
    · subst h2f; simp [escDecode, stringBody]
    by_cases h62 : e = 0x62
    · subst h62; simp [escDecode, stringBody]
    by_cases h66 : e = 0x66
    · subst h66; simp [escDecode, stringBody]
    by_cases h6e : e = 0x6E
    · subst h6e; simp [escDecode, stringBody]
    by_cases h72 : e = 0x72
    · subst h72; simp [escDecode, stringBody]
    by_cases h74 : e = 0x74
    · subst h74; simp [escDecode, stringBody]
    by_cases h75 : e = 0x75
    · subst h75
      rw [stringBody]
      simp only [escDecode, show (0x75 : UInt8) ≠ 0x22 by decide, show (0x75 : UInt8) ≠ 0x5C by decide,
        show (0x75 : UInt8) ≠ 0x2F by decide, show (0x75 : UInt8) ≠ 0x62 by decide,
        show (0x75 : UInt8) ≠ 0x66 by decide, show (0x75 : UInt8) ≠ 0x6E by decide,
        show (0x75 : UInt8) ≠ 0x72 by decide, show (0x75 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
      cases hu : unicodeEscape rest with
      | none => simp
      | some p =>
        obtain ⟨c, r⟩ := p
        obtain ⟨hl, hr⟩ := ue_suffix _ _ _ hu
        simp only [Option.map_some]
        rw [if_pos (by omega)]
        rw [show 1 + (rest.length - r.length) = (rest.length - r.length) + 1 by omega, List.drop_succ_cons, ← hr]
    · simp only [escDecode, h22, h5c, h2f, h62, h66, h6e, h72, h74, h75, ite_false]
      rw [stringBody] <;> simp_all

end WNear.Binary.ParseEscape
