import Bridge.Functions.JsonFuel

/-!
# serde's derived struct deserializer, as a pure machine (M6, pure)

The binary reads `{ account_id: ValidAccountId }` the way serde's derived `Deserialize` drives
serde_json: a stream that fails at the first error. The model (`Call.decode`) parses the whole
value first (`parse`), then picks the fields (`structFields`, `required`). This file defines the
streaming machine and proves the two agree (`fromSlice_eq`). That is the formal form of the
"no disagreement" check of `notes/todo/wnear_m6_parser_map.md`.

The machine, for a struct with one field `key`, is parameterized by the two value readers the
binary calls, as hypotheses with a spec:

* `dv`, the field's deserializer (169 for `ValidAccountId`): it must agree with `valueAs dec`, the
  model's `valueR` then the field decoder `dec`;
* `ign`, `ignore_value` (81) for unknown fields: it must agree with `valueSkip`.

"Agree" (`Agrees`) allows one difference. A reader may fail early where the model's `value`
succeeds with a rest that starts with a digit: serde rejects `01` at the second digit, the model
reads `0` and fails one step later, when the container sees `1`. Inside a struct both reject.

The machine (`structDe`, `fromSlice`) follows the binary:

* whitespace, then `{` or `[` (228); anything else is an error (340);
* the object form: `{` then `}` is a missing field (177); otherwise members (`objLoop`): the key
  (193: whitespace, `"`, `parse_str`, which must be UTF-8), then a duplicate check (166), then
  the colon (89), then `dv` for the field or `ign` for any other key (205/201), then `,` and the
  next member, or `}` (90);
* the array form: `[` then `]` is `invalid_length` (165); otherwise one element through `dv`
  (214), then `]` (91);
* then only whitespace (`end`, 320).

`fromSlice_eq`: for every input, `fromSlice` is `Call.decode`'s reading of the field.
-/

namespace WNear.SerdeStructModel

open NearInterface.Json WNear.JsonFuel

/-- `f` is `g`, except that `f` may fail where `g` succeeds with a rest that starts with a
digit. -/
def Agrees {β : Type} (f g : List UInt8 → Option (β × List UInt8)) : Prop :=
  ∀ bs, f bs = g bs ∨ (f bs = none ∧ ∃ x d t, g bs = some (x, d :: t) ∧ isDigit d = true)

/-- The model's reading of a field's value with the decoder `dec`. -/
def valueAs {α : Type} (dec : Value → Option α) (bs : List UInt8) : Option (α × List UInt8) :=
  (valueR bs).bind fun (v, r) => (dec v).map (·, r)

/-- The model's skipping of a value. -/
def valueSkip (bs : List UInt8) : Option (Unit × List UInt8) := (valueR bs).map fun (_, r) => ((), r)

/-- Only whitespace left. -/
def endOk {α : Type} (r : List UInt8) (a : α) : Option α := if skipWhitespace r = [] then some a else none

section Machine

variable {α : Type} (key : String) (dv : List UInt8 → Option (α × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8))

/-- The object's members after `{` or `,`, with the field read so far (`seen`): the key, the
duplicate check, the colon, the value, then `,` or `}`. `n` is fuel (the input's length is
enough). -/
def objLoop : Nat → Option α → List UInt8 → Option (Option α × List UInt8)
  | 0, _, _ => none
  | n + 1, seen, bs =>
    (keyAt bs).bind fun (k, rest) =>
    match k with
    | none => none
    | some k =>
      if k = key ∧ seen.isSome then none else
      (colonAt rest).bind fun rest =>
      (if k = key then (dv rest).map (fun (a, r) => (some a, r))
       else (ign rest).map (fun (_, r) => (seen, r))).bind fun (seen', rest) =>
      match skipWhitespace rest with
      | 0x2C :: rest => objLoop n seen' rest
      | 0x7D :: rest => some (seen', rest)
      | _ => none

/-- The struct, from either form. -/
def structDe (bs : List UInt8) : Option (α × List UInt8) :=
  match skipWhitespace bs with
  | 0x7B :: rest =>
    match skipWhitespace rest with
    | 0x7D :: _ => none
    | _ => (objLoop key dv ign (rest.length + 1) none rest).bind fun (seen, r) => seen.map (·, r)
  | 0x5B :: rest =>
    match skipWhitespace rest with
    | 0x5D :: _ => none
    | _ => (dv (skipWhitespace rest)).bind fun (a, r) =>
      match skipWhitespace r with
      | 0x5D :: r => some (a, r)
      | _ => none
  | _ => none

/-- `from_slice`: the struct, then only whitespace. -/
def fromSlice (bs : List UInt8) : Option α :=
  (structDe key dv ign bs).bind fun (a, r) => endOk r a

end Machine

/-! ## The model's side -/

section Model

variable {α : Type} (key : String) (dec : Value → Option α)

/-- `structFields [key]` on an object, then `required dec`. -/
def modelObj (ms : List (Option String × Value)) : Option α :=
  if ms.all (·.1.isSome) && decide ((ms.filter (·.1 == some key)).length ≤ 1) then
    ((ms.find? (·.1 == some key)).map (·.2)).bind dec
  else none

theorem decode_obj (ms : List (Option String × Value)) :
    (structFields [key] (.obj ms)).bind (fun fs => required dec fs[0]?.join) = modelObj key dec ms := by
  unfold structFields modelObj
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  split
  · simp only [Option.bind_some, List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.join_some]
    cases (ms.find? (·.1 == some key)).map (·.2) <;> rfl
  · rfl

theorem decode_arr (vs : List Value) :
    (structFields [key] (.arr vs)).bind (fun fs => required dec fs[0]?.join) =
      if vs.length = 1 then (vs[0]?).bind dec else none := by
  unfold structFields
  by_cases h : vs.length = 1
  · simp only [h, beq_self_eq_true, ite_true, List.length_cons, List.length_nil, Nat.zero_add,
      Option.bind_some]
    obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
      match vs, h with
      | [v], _ => exact ⟨v, rfl⟩
    rfl
  · simp [h]

end Model

/-! ## Lengths and prefixes -/

theorem keyAt_len {bs r : List UInt8} {k : Option String} (h : keyAt bs = some (k, r)) :
    r.length < bs.length := by
  unfold keyAt at h
  split at h
  · rename_i rest hs
    have := skip_cons_length hs
    have := stringBody_len h
    omega
  · simp at h

theorem colonAt_len {bs r : List UInt8} (h : colonAt bs = some r) : r.length < bs.length := by
  unfold colonAt at h
  split at h
  · rename_i rest hs
    simp only [Option.some.injEq] at h
    subst h
    exact skip_cons_length hs
  · simp at h

/-- `membersR` returns the members read before, then more. -/
theorem membersR_prefix (n : Nat) : ∀ (bs : List UInt8) (acc ms : List (Option String × Value)) (r : List UInt8),
    bs.length < n → membersR bs acc = some (ms, r) → ∃ suf, ms = acc.reverse ++ suf := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro bs acc ms r hn h
    rw [membersR_eq] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨k, r1⟩, hk, r2, hc, ⟨v, r3⟩, hv, h⟩ := h
    dsimp only at hc h
    have l1 : r1.length < bs.length := keyAt_len hk
    have l2 := colonAt_len hc
    have l3 : r3.length ≤ r2.length := valueR_length hv
    unfold memberEnd at h
    split at h
    · rename_i r4 hs
      have := skip_cons_length hs
      obtain ⟨suf, rfl⟩ := ih r4 _ ms r (by omega) h
      exact ⟨(k, v) :: suf, by simp⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[(k, v)], by rw [← h.1]; simp⟩
    · simp at h

theorem membersR_prefix' {bs : List UInt8} {acc ms : List (Option String × Value)} {r : List UInt8}
    (h : membersR bs acc = some (ms, r)) : ∃ suf, ms = acc.reverse ++ suf :=
  membersR_prefix (bs.length + 1) bs acc ms r (by omega) h

/-! ## The object form -/

section Obj

variable {α : Type} (key : String) (dec : Value → Option α)

/-- The members read so far (`pre`, in order) and the field read so far (`seen`): every key is
UTF-8, `key` at most once, and `seen` is its decoded value. -/
def Inv (pre : List (Option String × Value)) (seen : Option α) : Prop :=
  pre.all (·.1.isSome) = true ∧ (pre.filter (·.1 == some key)).length ≤ 1 ∧
    ((pre.find? (·.1 == some key)).map (·.2)).bind dec = seen ∧
    (seen = none → (pre.filter (·.1 == some key)).length = 0)

/-- The model's result after the members `pre ++ (k, v) :: _`, when that prefix is already bad. -/
theorem end_bad (k : Option String) (v : Value) (pre : List (Option String × Value)) (r3 : List UInt8)
    (hbad : ∀ suf, modelObj key dec (pre ++ (k, v) :: suf) = none) :
    (memberEnd k v pre.reverse r3).bind (fun x => (modelObj key dec x.1).bind (endOk x.2)) = none := by
  unfold memberEnd
  split
  · rename_i r4 _
    cases hm : membersR r4 ((k, v) :: pre.reverse) with
    | none => rfl
    | some x =>
      obtain ⟨ms, r⟩ := x
      obtain ⟨suf, rfl⟩ := membersR_prefix' hm
      simp only [Option.bind_some, List.reverse_cons, List.reverse_reverse, List.append_assoc,
        List.cons_append, List.nil_append, hbad suf, Option.bind_none]
  · simp only [List.reverse_cons, List.reverse_reverse, Option.bind_some]
    rw [hbad []]; rfl
  · rfl

theorem modelObj_none_key (pre : List (Option String × Value)) (v : Value) (suf : List (Option String × Value)) :
    modelObj key dec (pre ++ (none, v) :: suf) = none := by
  unfold modelObj
  simp [List.all_append]

theorem count_pos_of_some {pre : List (Option String × Value)} {seen : Option α} (h : Inv key dec pre seen)
    (hs : seen.isSome) : 1 ≤ (pre.filter (·.1 == some key)).length := by
  obtain ⟨_, _, h3, _⟩ := h
  by_contra hc
  have h0 : pre.filter (·.1 == some key) = [] := List.length_eq_zero_iff.mp (by omega)
  have : pre.find? (·.1 == some key) = none := by
    rw [List.find?_eq_none]
    intro x hx hp
    have : x ∈ pre.filter (·.1 == some key) := List.mem_filter.mpr ⟨hx, hp⟩
    rw [h0] at this; simp at this
  rw [this] at h3
  subst h3
  simp at hs

theorem modelObj_dup {pre : List (Option String × Value)} (h : 1 ≤ (pre.filter (·.1 == some key)).length)
    (v : Value) (suf : List (Option String × Value)) :
    modelObj key dec (pre ++ (some key, v) :: suf) = none := by
  unfold modelObj
  have : 2 ≤ ((pre ++ (some key, v) :: suf).filter (·.1 == some key)).length := by
    rw [List.filter_append, List.length_append]
    simp only [List.filter_cons, beq_self_eq_true, ite_true, List.length_cons]
    omega
  have h2 : decide (((pre ++ (some key, v) :: suf).filter (·.1 == some key)).length ≤ 1) = false := by
    simp; omega
  rw [h2, Bool.and_false]
  rfl

theorem find_none_of_count {pre : List (Option String × Value)} (h : (pre.filter (·.1 == some key)).length = 0) :
    pre.find? (·.1 == some key) = none := by
  rw [List.find?_eq_none]
  intro x hx hp
  have : x ∈ pre.filter (·.1 == some key) := List.mem_filter.mpr ⟨hx, hp⟩
  rw [List.length_eq_zero_iff.mp h] at this; simp at this

theorem modelObj_decfail {pre : List (Option String × Value)} (h : (pre.filter (·.1 == some key)).length = 0)
    (v : Value) (hv : dec v = none) (suf : List (Option String × Value)) :
    modelObj key dec (pre ++ (some key, v) :: suf) = none := by
  unfold modelObj
  rw [List.find?_append, find_none_of_count key h]
  simp [hv]

theorem modelObj_key {pre : List (Option String × Value)} (h : Inv key dec pre none) (v : Value) (a : α)
    (hv : dec v = some a) : modelObj key dec (pre ++ [(some key, v)]) = some a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h0 := h4 rfl
  unfold modelObj
  rw [List.find?_append, find_none_of_count key h0]
  simp only [List.all_append, h1, List.filter_append, List.length_append, h0]
  simp [hv]

theorem modelObj_other {pre : List (Option String × Value)} {seen : Option α} (h : Inv key dec pre seen)
    (k : String) (hk : k ≠ key) (v : Value) : modelObj key dec (pre ++ [(some k, v)]) = seen := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold modelObj
  have hb : (((some k, v) : Option String × Value).1 == some key) = false := by simp [hk]
  rw [List.find?_append]
  simp only [List.all_append, h1, List.filter_append, List.length_append, List.find?_cons, hb,
    List.filter_cons, List.find?_nil, List.filter_nil, Option.or_none]
  simp only [Bool.false_eq_true, ite_false, List.length_nil, Nat.add_zero, List.all_cons, List.all_nil,
    Option.isSome_some, Bool.and_true, Bool.true_and]
  rw [← h3]
  simp [h2]

theorem inv_key {pre : List (Option String × Value)} (h : Inv key dec pre none) (v : Value) (a : α)
    (hv : dec v = some a) : Inv key dec (pre ++ [(some key, v)]) (some a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h0 := h4 rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.all_append, h1]
  · simp [List.filter_append, h0]
  · rw [List.find?_append, find_none_of_count key h0]; simp [hv]
  · simp

theorem inv_other {pre : List (Option String × Value)} {seen : Option α} (h : Inv key dec pre seen)
    (k : String) (hk : k ≠ key) (v : Value) : Inv key dec (pre ++ [(some k, v)]) seen := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hb : (((some k, v) : Option String × Value).1 == some key) = false := by simp [hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.all_append, h1]
  · simp only [List.filter_append, List.filter_cons, hb, List.filter_nil]; simpa using h2
  · rw [List.find?_append]; simp only [List.find?_cons, hb, List.find?_nil]; simpa using h3
  · intro hs; simp only [List.filter_append, List.filter_cons, hb, List.filter_nil]; simpa using h4 hs

theorem isDigit_not_ws {d : UInt8} (h : isDigit d = true) : isWhitespace d = false := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isWhitespace, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro e <;> subst e <;> revert h <;> decide

theorem memberEnd_digit (k : Option String) (v : Value) (acc : List (Option String × Value)) {d : UInt8}
    (t : List UInt8) (h : isDigit d = true) : memberEnd k v acc (d :: t) = none := by
  unfold memberEnd
  rw [skip_of_not t (isDigit_not_ws h)]
  split
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at h; exact absurd h (by decide)
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at h; exact absurd h (by decide)
  · rfl

/-- The model's side is `none` once the members read so far are bad. -/
theorem rhs_bad (k : Option String) (pre : List (Option String × Value)) (r1 : List UInt8)
    (hbad : ∀ v suf, modelObj key dec (pre ++ (k, v) :: suf) = none) :
    ((colonAt r1).bind fun r2 => (valueR r2).bind fun x => memberEnd k x.1 pre.reverse x.2).bind
      (fun x => (modelObj key dec x.1).bind (endOk x.2)) = none := by
  cases colonAt r1 with
  | none => rfl
  | some r2 =>
    simp only [Option.bind_some]
    cases valueR r2 with
    | none => rfl
    | some y =>
      obtain ⟨v, r3⟩ := y
      exact end_bad key dec k v pre r3 (hbad v)

variable (dv : List UInt8 → Option (α × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))

/-- **The members**: serde's member loop and the model's `members`, followed by the field's
decoding and the end, give the same. -/
theorem objLoop_spec (hdv : Agrees dv (valueAs dec)) (hign : Agrees ign valueSkip) (n : Nat) :
    ∀ (bs : List UInt8) (pre : List (Option String × Value)) (seen : Option α),
    bs.length < n → Inv key dec pre seen →
    (objLoop key dv ign n seen bs).bind (fun x => x.1.bind (endOk x.2)) =
      (membersR bs pre.reverse).bind (fun x => (modelObj key dec x.1).bind (endOk x.2)) := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro bs pre seen hn hinv
    rw [membersR_eq]
    unfold objLoop
    cases hk : keyAt bs with
    | none => rfl
    | some x =>
      obtain ⟨k, r1⟩ := x
      have l1 : r1.length < bs.length := keyAt_len hk
      simp only [Option.bind_some]
      cases k with
      | none =>
        simp only [Option.bind_none]
        exact (rhs_bad key dec none pre r1 (modelObj_none_key key dec pre)).symm
      | some k =>
        dsimp only
        by_cases hkey : k = key
        · subst hkey
          by_cases hs : seen.isSome = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hs⟩)]
            exact (rhs_bad k dec (some k) pre r1
              (fun v suf => modelObj_dup k dec (count_pos_of_some k dec hinv hs) v suf)).symm
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hs h.2))]
            have hseen : seen = none := by cases seen <;> simp_all
            subst hseen
            simp only [ite_true]
            cases hc : colonAt r1 with
            | none => rfl
            | some r2 =>
              have l2 := colonAt_len hc
              simp only [Option.bind_some]
              rcases hdv r2 with hd | ⟨hd, x, d, t, hg, hdig⟩
              · rw [hd]; unfold valueAs
                cases hv : valueR r2 with
                | none => rfl
                | some y =>
                  obtain ⟨v, r3⟩ := y
                  have l3 : r3.length ≤ r2.length := valueR_length hv
                  simp only [Option.bind_some]
                  cases hdec : dec v with
                  | none =>
                    simp only [Option.map_none, Option.bind_none]
                    exact (end_bad k dec (some k) v pre r3 (modelObj_decfail k dec (hinv.2.2.2 rfl) v hdec)).symm
                  | some a =>
                    simp only [Option.map_some, Option.bind_some]
                    unfold memberEnd
                    generalize hs3 : skipWhitespace r3 = s3
                    split
                    · rename_i r4
                      have l4 := skip_cons_length hs3
                      rw [ih r4 (pre ++ [(some k, v)]) (some a) (by omega) (inv_key k dec hinv v a hdec),
                        List.reverse_append]
                      rfl
                    · simp only [Option.bind_some, List.reverse_cons, List.reverse_reverse,
                        modelObj_key k dec hinv v a hdec]
                    · split <;> (try (exfalso; simp_all; done)) <;> rfl
              · rw [hd]
                unfold valueAs at hg
                simp only [Option.bind_eq_some_iff] at hg
                obtain ⟨⟨v, r3⟩, hv, hg⟩ := hg
                simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hg
                obtain ⟨_, _, _, rfl⟩ := hg
                rw [hv]
                simp only [Option.bind_some, Option.map_none, Option.bind_none]
                rw [memberEnd_digit _ _ _ _ hdig]
                rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hkey h.1))]
          simp only [hkey, ite_false]
          cases hc : colonAt r1 with
          | none => rfl
          | some r2 =>
            have l2 := colonAt_len hc
            simp only [Option.bind_some]
            rcases hign r2 with hd | ⟨hd, x, d, t, hg, hdig⟩
            · rw [hd]; unfold valueSkip
              cases hv : valueR r2 with
              | none => rfl
              | some y =>
                obtain ⟨v, r3⟩ := y
                have l3 : r3.length ≤ r2.length := valueR_length hv
                simp only [Option.map_some, Option.bind_some]
                unfold memberEnd
                generalize hs3 : skipWhitespace r3 = s3
                split
                · rename_i r4
                  have l4 := skip_cons_length hs3
                  rw [ih r4 (pre ++ [(some k, v)]) seen (by omega) (inv_other key dec hinv k hkey v),
                    List.reverse_append]
                  rfl
                · simp only [Option.bind_some, List.reverse_cons, List.reverse_reverse,
                    modelObj_other key dec hinv k hkey v]
                · split <;> (try (exfalso; simp_all; done)) <;> rfl
            · rw [hd]
              unfold valueSkip at hg
              simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hg
              obtain ⟨⟨v, r3⟩, hv, _, rfl⟩ := hg
              rw [hv]
              simp only [Option.bind_some, Option.map_none, Option.bind_none]
              rw [memberEnd_digit _ _ _ _ hdig]
              rfl

end Obj

/-! ## The value's shape, case by case -/

theorem valueR_skip (bs : List UInt8) : valueR (skipWhitespace bs) = valueR bs := by
  rw [valueR_eq, valueR_eq bs, skip_idem]

theorem valueR_objE {bs rest r : List UInt8} (h : skipWhitespace bs = 0x7B :: rest)
    (h' : skipWhitespace rest = 0x7D :: r) : valueR bs = some (.obj [], r) := by
  have e : valueR bs = match skipWhitespace rest with
      | 0x7D :: rest => some (.obj [], rest)
      | _ => (membersR rest []).map fun (ms, rest) => (.obj ms, rest) := by
    rw [valueR_eq, h]; rfl
  rw [e, h']; rfl

theorem valueR_objM {bs rest : List UInt8} (h : skipWhitespace bs = 0x7B :: rest)
    (h' : ∀ r, skipWhitespace rest ≠ 0x7D :: r) :
    valueR bs = (membersR rest []).map fun x => (.obj x.1, x.2) := by
  have e : valueR bs = match skipWhitespace rest with
      | 0x7D :: rest => some (.obj [], rest)
      | _ => (membersR rest []).map fun (ms, rest) => (.obj ms, rest) := by
    rw [valueR_eq, h]; rfl
  rw [e]; split
  · exact absurd ‹_› (h' _)
  · rfl

theorem valueR_arrE {bs rest r : List UInt8} (h : skipWhitespace bs = 0x5B :: rest)
    (h' : skipWhitespace rest = 0x5D :: r) : valueR bs = some (.arr [], r) := by
  have e : valueR bs = match skipWhitespace rest with
      | 0x5D :: rest => some (.arr [], rest)
      | _ => (elementsR rest []).map fun (vs, rest) => (.arr vs, rest) := by
    rw [valueR_eq, h]; rfl
  rw [e, h']; rfl

theorem valueR_arrM {bs rest : List UInt8} (h : skipWhitespace bs = 0x5B :: rest)
    (h' : ∀ r, skipWhitespace rest ≠ 0x5D :: r) :
    valueR bs = (elementsR rest []).map fun x => (.arr x.1, x.2) := by
  have e : valueR bs = match skipWhitespace rest with
      | 0x5D :: rest => some (.arr [], rest)
      | _ => (elementsR rest []).map fun (vs, rest) => (.arr vs, rest) := by
    rw [valueR_eq, h]; rfl
  rw [e]; split
  · exact absurd ‹_› (h' _)
  · rfl

/-- A value that does not start with `{` or `[` is not a struct. -/
theorem valueR_other {bs : List UInt8} (h1 : ∀ r, skipWhitespace bs ≠ 0x7B :: r)
    (h2 : ∀ r, skipWhitespace bs ≠ 0x5B :: r) {v : Value} {r : List UInt8} (hv : valueR bs = some (v, r)) :
    (∀ ms, v ≠ .obj ms) ∧ (∀ vs, v ≠ .arr vs) := by
  rw [valueR_eq] at hv
  split at hv
  · simp only [Option.some.injEq, Prod.mk.injEq] at hv; obtain ⟨rfl, _⟩ := hv; simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hv; obtain ⟨rfl, _⟩ := hv; simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hv; obtain ⟨rfl, _⟩ := hv; simp
  · simp only [Option.map_eq_some_iff] at hv
    obtain ⟨⟨s, r'⟩, _, hv⟩ := hv
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, _⟩ := hv
    split <;> simp
  · exact absurd ‹_› (h2 _)
  · exact absurd ‹_› (h1 _)
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨_, _, _, _, hv⟩ := hv
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, _⟩ := hv
    simp

/-- `elementsR` returns the elements read before, then at least one more. -/
theorem elementsR_prefix (n : Nat) : ∀ (bs : List UInt8) (acc vs : List Value) (r : List UInt8),
    bs.length < n → elementsR bs acc = some (vs, r) → ∃ suf, vs = acc.reverse ++ suf ∧ suf ≠ [] := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro bs acc vs r hn h
    rw [elementsR_eq] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨v, r1⟩, hv, h⟩ := h
    have l1 : r1.length ≤ bs.length := valueR_length hv
    dsimp only at h
    unfold elemEnd at h
    split at h
    · rename_i r2 hs
      have := skip_cons_length hs
      obtain ⟨suf, rfl, _⟩ := ih r2 _ vs r (by omega) h
      exact ⟨v :: suf, by simp, by simp⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[v], by rw [← h.1]; simp, by simp⟩
    · simp at h

theorem elementsR_prefix' {bs : List UInt8} {acc vs : List Value} {r : List UInt8}
    (h : elementsR bs acc = some (vs, r)) : ∃ suf, vs = acc.reverse ++ suf ∧ suf ≠ [] :=
  elementsR_prefix (bs.length + 1) bs acc vs r (by omega) h

section Top

variable {α : Type} (key : String) (dec : Value → Option α)
  (dv : List UInt8 → Option (α × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))

theorem structDe_objE {bs rest r : List UInt8} (h : skipWhitespace bs = 0x7B :: rest)
    (h' : skipWhitespace rest = 0x7D :: r) : structDe key dv ign bs = none := by
  have e : structDe key dv ign bs = match skipWhitespace rest with
      | 0x7D :: _ => none
      | _ => (objLoop key dv ign (rest.length + 1) none rest).bind fun (seen, r) => seen.map (·, r) := by
    unfold structDe; rw [h]; rfl
  rw [e, h']; rfl

theorem structDe_objM {bs rest : List UInt8} (h : skipWhitespace bs = 0x7B :: rest)
    (h' : ∀ r, skipWhitespace rest ≠ 0x7D :: r) :
    structDe key dv ign bs = (objLoop key dv ign (rest.length + 1) none rest).bind fun x => x.1.map (·, x.2) := by
  have e : structDe key dv ign bs = match skipWhitespace rest with
      | 0x7D :: _ => none
      | _ => (objLoop key dv ign (rest.length + 1) none rest).bind fun (seen, r) => seen.map (·, r) := by
    unfold structDe; rw [h]; rfl
  rw [e]; split
  · exact absurd ‹_› (h' _)
  · rfl

theorem structDe_arrE {bs rest r : List UInt8} (h : skipWhitespace bs = 0x5B :: rest)
    (h' : skipWhitespace rest = 0x5D :: r) : structDe key dv ign bs = none := by
  have e : structDe key dv ign bs = match skipWhitespace rest with
      | 0x5D :: _ => none
      | _ => (dv (skipWhitespace rest)).bind fun (a, r) =>
        match skipWhitespace r with
        | 0x5D :: r => some (a, r)
        | _ => none := by
    unfold structDe; rw [h]; rfl
  rw [e, h']; rfl

/-- After the one element: `]`. -/
def arrEnd {α : Type} (a : α) (r : List UInt8) : Option (α × List UInt8) :=
  match skipWhitespace r with
  | 0x5D :: r => some (a, r)
  | _ => none

theorem structDe_arrM {bs rest : List UInt8} (h : skipWhitespace bs = 0x5B :: rest)
    (h' : ∀ r, skipWhitespace rest ≠ 0x5D :: r) :
    structDe key dv ign bs = (dv (skipWhitespace rest)).bind fun x => arrEnd x.1 x.2 := by
  have e : structDe key dv ign bs = match skipWhitespace rest with
      | 0x5D :: _ => none
      | _ => (dv (skipWhitespace rest)).bind fun (a, r) =>
        match skipWhitespace r with
        | 0x5D :: r => some (a, r)
        | _ => none := by
    unfold structDe; rw [h]; rfl
  rw [e]; split
  · exact absurd ‹_› (h' _)
  · rfl

theorem structDe_other {bs : List UInt8} (h1 : ∀ r, skipWhitespace bs ≠ 0x7B :: r)
    (h2 : ∀ r, skipWhitespace bs ≠ 0x5B :: r) : structDe key dv ign bs = none := by
  unfold structDe
  split
  · exact absurd ‹_› (h1 _)
  · exact absurd ‹_› (h2 _)
  · rfl

theorem elemEnd_comma {v : Value} {acc : List Value} {r r' : List UInt8} (h : skipWhitespace r = 0x2C :: r') :
    elemEnd v acc r = elementsR r' (v :: acc) := by
  unfold elemEnd; rw [h]; rfl

theorem elemEnd_close {v : Value} {acc : List Value} {r r' : List UInt8} (h : skipWhitespace r = 0x5D :: r') :
    elemEnd v acc r = some ((v :: acc).reverse, r') := by
  unfold elemEnd; rw [h]; rfl

theorem elemEnd_other {v : Value} {acc : List Value} {r : List UInt8} (h1 : ∀ r', skipWhitespace r ≠ 0x2C :: r')
    (h2 : ∀ r', skipWhitespace r ≠ 0x5D :: r') : elemEnd v acc r = none := by
  unfold elemEnd; split
  · exact absurd ‹_› (h1 _)
  · exact absurd ‹_› (h2 _)
  · rfl

theorem arrEnd_close {β : Type} {a : β} {r r' : List UInt8} (h : skipWhitespace r = 0x5D :: r') :
    arrEnd a r = some (a, r') := by
  unfold arrEnd; rw [h]; rfl

theorem arrEnd_other {β : Type} {a : β} {r : List UInt8} (h2 : ∀ r', skipWhitespace r ≠ 0x5D :: r') :
    arrEnd a r = none := by
  unfold arrEnd; split
  · exact absurd ‹_› (h2 _)
  · rfl

/-- The model's reading after `valueR`: only whitespace, then the struct's field. -/
def rhsF (x : Value × List UInt8) : Option α :=
  if skipWhitespace x.2 = [] then (structFields [key] x.1).bind (fun fs => required dec fs[0]?.join) else none

theorem decode_eq (bs : List UInt8) :
    ((parse bs).bind (structFields [key])).bind (fun fs => required dec fs[0]?.join) =
      (valueR bs).bind (rhsF key dec) := by
  rw [parse_eq]
  cases valueR bs with
  | none => rfl
  | some x =>
    obtain ⟨v, r⟩ := x
    simp only [Option.bind_some, rhsF]
    split <;> rfl

theorem rhs_obj (ms : List (Option String × Value)) (r : List UInt8) :
    (modelObj key dec ms).bind (endOk r) = rhsF key dec (.obj ms, r) := by
  unfold rhsF endOk
  rw [decode_obj]
  by_cases hr : skipWhitespace r = [] <;> simp only [hr, ite_true, ite_false] <;> cases modelObj key dec ms <;> rfl

/-- The array form, the model's side: exactly one element, then `]`. -/
theorem rhs_arr (v : Value) (r : List UInt8) :
    ((elemEnd v [] r).map (fun x => (Value.arr x.1, x.2))).bind (rhsF key dec) =
      (arrEnd v r).bind (fun x => (dec x.1).bind (endOk x.2)) := by
  by_cases hc : ∃ r', skipWhitespace r = 0x2C :: r'
  · obtain ⟨r', hc⟩ := hc
    rw [elemEnd_comma hc, arrEnd_other (fun r'' e => by rw [hc] at e; simp at e)]
    cases he : elementsR r' [v] with
    | none => rfl
    | some y =>
      obtain ⟨vs, r''⟩ := y
      obtain ⟨suf, rfl, hsuf⟩ := elementsR_prefix' he
      simp only [Option.map_some, Option.bind_some, Option.bind_none, rhsF, decode_arr]
      have : ¬ ([v].reverse ++ suf).length = 1 := by
        cases suf with
        | nil => exact absurd rfl hsuf
        | cons _ _ => simp
      simp [hsuf]
  · by_cases hcl : ∃ r', skipWhitespace r = 0x5D :: r'
    · obtain ⟨r', hcl⟩ := hcl
      rw [elemEnd_close hcl, arrEnd_close hcl]
      simp only [Option.map_some, Option.bind_some, rhsF, decode_arr, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.length_singleton, ite_true, List.getElem?_cons_zero, endOk]
      by_cases hr : skipWhitespace r' = [] <;> simp only [hr, ite_true, ite_false] <;> cases dec v <;> simp [endOk, hr]
    · rw [elemEnd_other (fun r' e => hc ⟨r', e⟩) (fun r' e => hcl ⟨r', e⟩),
        arrEnd_other (fun r' e => hcl ⟨r', e⟩)]
      rfl

/-- **serde's struct deserializer agrees with the model**: for a struct with the one field `key`,
`from_slice` with the field reader `dv` and `ignore_value` `ign` accepts exactly what
`Call.decode` accepts (`parse`, `structFields [key]`, `required dec`), with the same field. -/
theorem fromSlice_eq (hdv : Agrees dv (valueAs dec)) (hign : Agrees ign valueSkip) (bs : List UInt8) :
    fromSlice key dv ign bs =
      ((parse bs).bind (structFields [key])).bind (fun fs => required dec fs[0]?.join) := by
  rw [decode_eq]
  unfold fromSlice
  by_cases ho : ∃ rest, skipWhitespace bs = 0x7B :: rest
  · obtain ⟨rest, h⟩ := ho
    by_cases he : ∃ r, skipWhitespace rest = 0x7D :: r
    · obtain ⟨r, h'⟩ := he
      rw [structDe_objE key dv ign h h', valueR_objE h h']
      simp only [Option.bind_none, Option.bind_some, ← rhs_obj]
      unfold modelObj
      simp
    · have h' : ∀ r, skipWhitespace rest ≠ 0x7D :: r := fun r e => he ⟨r, e⟩
      rw [structDe_objM key dv ign h h', valueR_objM h h']
      have hl := objLoop_spec key dec dv ign hdv hign (rest.length + 1) rest [] none (by omega)
        ⟨by simp, by simp, by simp, by simp⟩
      simp only [List.reverse_nil] at hl
      calc _ = (objLoop key dv ign (rest.length + 1) none rest).bind (fun x => x.1.bind (endOk x.2)) := by
            rw [Option.bind_assoc]; congr 1; funext y; rcases y with ⟨_ | a, r⟩ <;> rfl
        _ = _ := hl
        _ = _ := by
          rw [Option.bind_map]; congr 1; funext x; exact rhs_obj key dec x.1 x.2
  · by_cases ha : ∃ rest, skipWhitespace bs = 0x5B :: rest
    · obtain ⟨rest, h⟩ := ha
      by_cases he : ∃ r, skipWhitespace rest = 0x5D :: r
      · obtain ⟨r, h'⟩ := he
        rw [structDe_arrE key dv ign h h', valueR_arrE h h']
        simp [rhsF, decode_arr]
      · have h' : ∀ r, skipWhitespace rest ≠ 0x5D :: r := fun r e => he ⟨r, e⟩
        rw [structDe_arrM key dv ign h h', valueR_arrM h h', elementsR_eq]
        rcases hdv (skipWhitespace rest) with hd | ⟨hd, x, d, t, hg, hdig⟩
        · rw [hd]
          unfold valueAs
          rw [valueR_skip]
          cases valueR rest with
          | none => rfl
          | some y =>
            obtain ⟨v, r⟩ := y
            simp only [Option.bind_some]
            rw [rhs_arr]
            by_cases hcl : ∃ r', skipWhitespace r = 0x5D :: r'
            · obtain ⟨r', hcl⟩ := hcl
              rw [arrEnd_close hcl]
              cases hdv' : dec v <;> simp [hdv', arrEnd_close hcl]
            · have h2 : ∀ r', skipWhitespace r ≠ 0x5D :: r' := fun r' e => hcl ⟨r', e⟩
              rw [arrEnd_other h2]
              cases hdv' : dec v <;> simp [hdv', arrEnd_other h2]
        · rw [hd]
          unfold valueAs at hg
          rw [valueR_skip] at hg
          simp only [Option.bind_eq_some_iff] at hg
          obtain ⟨⟨v, r3⟩, hv, hg⟩ := hg
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hg
          obtain ⟨_, _, _, rfl⟩ := hg
          rw [hv]
          simp only [Option.bind_none, Option.bind_some]
          rw [rhs_arr, arrEnd_other]
          · rfl
          · intro r' e
            rw [skip_of_not t (isDigit_not_ws hdig)] at e
            simp only [List.cons.injEq] at e
            rw [e.1] at hdig
            exact absurd hdig (by decide)
    · have h1 : ∀ r, skipWhitespace bs ≠ 0x7B :: r := fun r e => ho ⟨r, e⟩
      have h2 : ∀ r, skipWhitespace bs ≠ 0x5B :: r := fun r e => ha ⟨r, e⟩
      rw [structDe_other key dv ign h1 h2]
      cases hv : valueR bs with
      | none => rfl
      | some y =>
        obtain ⟨v, r⟩ := y
        obtain ⟨n1, n2⟩ := valueR_other h1 h2 hv
        simp only [Option.bind_none, Option.bind_some, rhsF]
        split
        · cases v with
          | obj ms => exact absurd rfl (n1 ms)
          | arr vs => exact absurd rfl (n2 vs)
          | _ => rfl
        · rfl

end Top

/-- **`ft_balance_of`'s arguments**: `Call.decode` is serde's machine with the field `account_id`,
for any account-id reader `dv` and any `ignore_value` `ign` that agree with the model. -/
theorem decode_balanceOf (dv : List UInt8 → Option (WNear.AccountId × List UInt8))
    (ign : List UInt8 → Option (Unit × List UInt8)) (hdv : Agrees dv (valueAs WNear.account))
    (hign : Agrees ign valueSkip) (bs : List UInt8) :
    WNear.Call.decode "ft_balance_of" bs = (fromSlice "account_id" dv ign bs).map WNear.Call.ftBalanceOf := by
  rw [fromSlice_eq "account_id" WNear.account dv ign hdv hign bs]
  simp only [WNear.Call.decode]
  cases (parse bs).bind (structFields ["account_id"]) with
  | none => rfl
  | some fs =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases required WNear.account fs[0]?.join <;> rfl

end WNear.SerdeStructModel
