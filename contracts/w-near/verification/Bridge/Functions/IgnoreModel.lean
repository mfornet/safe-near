import Bridge.Functions.SerdeStructModel

/-!
# `ignore_value` (81) as an iterative machine (M6, pure)

serde_json skips an unknown field's value without recursion: the open `[` and `{` are kept on a
stack of frames (the innermost in a local, the others in the scratch `Vec`). The model's `value`
is recursive. This file states the iteration on the model's side and proves it reads the same.

* `vSkip bs`: what serde's skip of one value returns, the rest after it. It is the model's
  `valueR`, except that it fails on a number `0` or `-0` followed by a digit (`early`): serde
  rejects the second digit (`InvalidNumber`), the model reads `0` and leaves the digit.
  `vSkip_agrees`: so `vSkip` agrees with `valueSkip` (`SerdeStructModel.Agrees`).
* `contM f r`: after a complete value inside the frame `f` (`[` or `{`), the rest of the
  container: `,` and more, or the closing bracket. `closeAll stk r` closes every frame of `stk`.
* The step equations, which are 81's loop body:
  * `vSkip_arr`, `vSkip_obj`: a value that opens a frame;
  * `open_arr`, `open_obj`: just after the bracket, the closing bracket or a first element or
    member (`[`: a value with the frame pushed; `{`: a key, `:`, a value);
  * `cont_arr`, `cont_obj`: after a value, `,` and the next element or member, or the closing
    bracket and the frame popped.
* `ignM`: the machine, with fuel, run from the equations; `ignM_eq`: it is `vSkip`.

The scalars (`null`, `true`, `false`, numbers, strings) are a parameter of the machine: `sv`, with
the hypothesis `sv bs = vSkip bs` on a scalar's first byte, which the Wasm proof of 81's scalar
branch (323, 83/86/87, 650) provides. Keys are skipped by `sk` (650 after the `"`), with
`sk bs = (stringBody bs []).map (·.2)`.
-/

namespace WNear.IgnoreModel

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel

/-- serde fails early: a number `0` or `-0` followed by a digit. -/
def early (v : Value) (r : List UInt8) : Bool :=
  (match v with | .number t => t == "0" || t == "-0" | _ => false) &&
    (match r with | d :: _ => isDigit d | [] => false)

/-- serde's skip of one value: the rest after it. -/
def vSkip (bs : List UInt8) : Option (List UInt8) :=
  (valueR bs).bind fun x => if early x.1 x.2 then none else some x.2

/-- After a value inside the frame `f`: `,` and more, or the closing bracket. -/
def contM (f : UInt8) (r : List UInt8) : Option (List UInt8) :=
  match skipWhitespace r with
  | 0x2C :: r' => if f = 0x5B then (elementsR r' []).map (·.2) else (membersR r' []).map (·.2)
  | 0x5D :: r' => if f = 0x5B then some r' else none
  | 0x7D :: r' => if f = 0x7B then some r' else none
  | _ => none

/-- Close every frame of the stack (innermost first). -/
def closeAll : List UInt8 → List UInt8 → Option (List UInt8)
  | [], r => some r
  | f :: stk, r => (contM f r).bind (closeAll stk)

theorem vSkip_agrees : Agrees (fun bs => (vSkip bs).map fun r => ((), r)) valueSkip := by
  intro bs
  dsimp only
  unfold vSkip valueSkip
  cases valueR bs with
  | none => left; rfl
  | some x =>
    obtain ⟨v, r⟩ := x
    simp only [Option.bind_some]
    by_cases he : early v r = true
    · right
      simp only [he, ite_true, Option.map_none, Option.map_some, true_and]
      unfold early at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨_, he⟩ := he
      cases r with
      | nil => simp at he
      | cons d t => exact ⟨(), d, t, rfl, he⟩
    · left
      simp [he]

/-- A rest that starts with a digit closes no frame. -/
theorem contM_digit (f : UInt8) {d : UInt8} (t : List UInt8) (h : isDigit d = true) : contM f (d :: t) = none := by
  unfold contM
  rw [skip_of_not t (isDigit_not_ws h)]
  split
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at h; exact absurd h (by decide)
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at h; exact absurd h (by decide)
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1] at h; exact absurd h (by decide)
  · rfl

/-- Inside a frame, serde's early failure changes nothing. -/
theorem vSkip_cons (bs : List UInt8) (f : UInt8) (stk : List UInt8) :
    (vSkip bs).bind (closeAll (f :: stk)) = (valueR bs).bind fun x => closeAll (f :: stk) x.2 := by
  unfold vSkip
  cases valueR bs with
  | none => rfl
  | some x =>
    obtain ⟨v, r⟩ := x
    simp only [Option.bind_some]
    by_cases he : early v r = true
    · simp only [he, ite_true, Option.bind_none]
      unfold early at he
      simp only [Bool.and_eq_true] at he
      obtain ⟨_, he⟩ := he
      cases r with
      | nil => simp at he
      | cons d t => simp only [closeAll, contM_digit f t he, Option.bind_none]
    · simp [he]

/-! ## The rest after the elements or members does not depend on what was read before -/

theorem elementsR_rest (n : Nat) : ∀ (r : List UInt8) (acc : List Value), r.length < n →
    (elementsR r acc).map (·.2) = (elementsR r []).map (·.2) := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro r acc hn
    rw [elementsR_eq, elementsR_eq r []]
    cases hv : valueR r with
    | none => rfl
    | some x =>
      obtain ⟨v, r1⟩ := x
      have l1 : r1.length ≤ r.length := valueR_length hv
      simp only [Option.bind_some]
      unfold elemEnd
      split
      · rename_i r2 hs
        have := skip_cons_length hs
        rw [ih r2 _ (by omega), ih r2 [v] (by omega)]
      · rfl
      · rfl

theorem membersR_rest (n : Nat) : ∀ (r : List UInt8) (acc : List (Option String × Value)), r.length < n →
    (membersR r acc).map (·.2) = (membersR r []).map (·.2) := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro r acc hn
    rw [membersR_eq, membersR_eq r []]
    cases hk : keyAt r with
    | none => simp
    | some x =>
      obtain ⟨k, r1⟩ := x
      have l1 : r1.length < r.length := keyAt_len hk
      simp only [Option.bind_some]
      cases hc : colonAt r1 with
      | none => simp [hc]
      | some r2 =>
        have l2 := colonAt_len hc
        simp only [Option.bind_some]
        cases hv : valueR r2 with
        | none => simp [hv]
        | some y =>
          obtain ⟨v, r3⟩ := y
          have l3 : r3.length ≤ r2.length := valueR_length hv
          simp only [Option.bind_some]
          unfold memberEnd
          split
          · rename_i r4 hs
            have := skip_cons_length hs
            rw [ih r4 _ (by omega), ih r4 [(k, v)] (by omega)]
          · rfl
          · rfl

theorem elements_cont (r : List UInt8) :
    (elementsR r []).map (·.2) = (valueR r).bind fun x => contM 0x5B x.2 := by
  rw [elementsR_eq]
  cases valueR r with
  | none => rfl
  | some x =>
    obtain ⟨v, r1⟩ := x
    simp only [Option.bind_some]
    unfold elemEnd contM
    generalize skipWhitespace r1 = s
    split
    · rename_i r2
      simp only [ite_true]
      exact elementsR_rest (r2.length + 1) r2 [v] (by omega)
    · rfl
    · split <;> (try (exfalso; simp_all; done)) <;> simp_all

theorem members_cont (r : List UInt8) :
    (membersR r []).map (·.2) =
      (keyAt r).bind fun x => (colonAt x.2).bind fun r2 => (valueR r2).bind fun y => contM 0x7B y.2 := by
  rw [membersR_eq]
  cases keyAt r with
  | none => rfl
  | some x =>
    obtain ⟨k, r1⟩ := x
    simp only [Option.bind_some]
    cases colonAt r1 with
    | none => rfl
    | some r2 =>
      simp only [Option.bind_some]
      cases valueR r2 with
      | none => rfl
      | some y =>
        obtain ⟨v, r3⟩ := y
        simp only [Option.bind_some]
        unfold memberEnd contM
        generalize skipWhitespace r3 = s
        split
        · rename_i r4
          simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false]
          exact membersR_rest (r4.length + 1) r4 [(k, v)] (by omega)
        · rfl
        · split <;> (try (exfalso; simp_all; done)) <;> simp_all

/-! ## The step equations -/

section Steps

variable {stk : List UInt8}

theorem vSkip_arrE {bs r r' : List UInt8} (h : skipWhitespace bs = 0x5B :: r) (h' : skipWhitespace r = 0x5D :: r') :
    (vSkip bs).bind (closeAll stk) = closeAll stk r' := by
  unfold vSkip; rw [valueR_arrE h h']; rfl

theorem vSkip_arrM {bs r : List UInt8} (h : skipWhitespace bs = 0x5B :: r) (h' : ∀ r', skipWhitespace r ≠ 0x5D :: r') :
    (vSkip bs).bind (closeAll stk) = (vSkip r).bind (closeAll (0x5B :: stk)) := by
  have e1 : vSkip bs = (elementsR r []).map (·.2) := by
    unfold vSkip; rw [valueR_arrM h h']; cases elementsR r [] <;> rfl
  rw [e1, elements_cont, vSkip_cons, Option.bind_assoc]; rfl

theorem vSkip_objE {bs r r' : List UInt8} (h : skipWhitespace bs = 0x7B :: r) (h' : skipWhitespace r = 0x7D :: r') :
    (vSkip bs).bind (closeAll stk) = closeAll stk r' := by
  unfold vSkip; rw [valueR_objE h h']; rfl

/-- The members after `,` (or the first one): a key, `:`, a value, with the frame `{`. -/
def memberStep (stk : List UInt8) (r : List UInt8) : Option (List UInt8) :=
  (keyAt r).bind fun x => (colonAt x.2).bind fun r2 => (vSkip r2).bind (closeAll (0x7B :: stk))

theorem members_step (r : List UInt8) :
    ((membersR r []).map (·.2)).bind (closeAll stk) = memberStep stk r := by
  rw [members_cont]
  unfold memberStep
  cases keyAt r with
  | none => rfl
  | some x =>
    simp only [Option.bind_some]
    cases colonAt x.2 with
    | none => rfl
    | some r2 =>
      simp only [Option.bind_some]
      rw [vSkip_cons, Option.bind_assoc]; rfl

theorem vSkip_objM {bs r : List UInt8} (h : skipWhitespace bs = 0x7B :: r) (h' : ∀ r', skipWhitespace r ≠ 0x7D :: r') :
    (vSkip bs).bind (closeAll stk) = memberStep stk r := by
  have e1 : vSkip bs = (membersR r []).map (·.2) := by
    unfold vSkip; rw [valueR_objM h h']; cases membersR r [] <;> rfl
  rw [e1, members_step]

theorem close_arr_comma {r r' : List UInt8} (h : skipWhitespace r = 0x2C :: r') :
    closeAll (0x5B :: stk) r = (vSkip r').bind (closeAll (0x5B :: stk)) := by
  have e : contM 0x5B r = (elementsR r' []).map (·.2) := by unfold contM; rw [h]; rfl
  conv_lhs => rw [closeAll]
  rw [e, elements_cont, vSkip_cons, Option.bind_assoc]; rfl

theorem close_obj_comma {r r' : List UInt8} (h : skipWhitespace r = 0x2C :: r') :
    closeAll (0x7B :: stk) r = memberStep stk r' := by
  have e : contM 0x7B r = (membersR r' []).map (·.2) := by unfold contM; rw [h]; rfl
  conv_lhs => rw [closeAll]
  rw [e, members_step]

theorem close_arr_end {r r' : List UInt8} (h : skipWhitespace r = 0x5D :: r') :
    closeAll (0x5B :: stk) r = closeAll stk r' := by
  have e : contM 0x5B r = some r' := by unfold contM; rw [h]; rfl
  conv_lhs => rw [closeAll]
  rw [e]; rfl

theorem close_obj_end {r r' : List UInt8} (h : skipWhitespace r = 0x7D :: r') :
    closeAll (0x7B :: stk) r = closeAll stk r' := by
  have e : contM 0x7B r = some r' := by unfold contM; rw [h]; rfl
  conv_lhs => rw [closeAll]
  rw [e]; rfl

theorem close_arr_none {r : List UInt8} (h1 : ∀ r', skipWhitespace r ≠ 0x2C :: r')
    (h2 : ∀ r', skipWhitespace r ≠ 0x5D :: r') : closeAll (0x5B :: stk) r = none := by
  have e : contM 0x5B r = none := by
    unfold contM; split
    · exact absurd ‹_› (h1 _)
    · exact absurd ‹_› (h2 _)
    · rfl
    · rfl
  conv_lhs => rw [closeAll]
  rw [e]; rfl

theorem close_obj_none {r : List UInt8} (h1 : ∀ r', skipWhitespace r ≠ 0x2C :: r')
    (h3 : ∀ r', skipWhitespace r ≠ 0x7D :: r') : closeAll (0x7B :: stk) r = none := by
  have e : contM 0x7B r = none := by
    unfold contM; split
    · exact absurd ‹_› (h1 _)
    · rfl
    · exact absurd ‹_› (h3 _)
    · rfl
  conv_lhs => rw [closeAll]
  rw [e]; rfl

end Steps

/-! ## The machine -/

/-- Where the machine is: expecting a value, just after the bracket `f`, or after a value in the
frame `f`. -/
inductive Mode
  | val
  | opened (f : UInt8)
  | cont (f : UInt8)

/-- A key, then `:`, then `k`. -/
def keyThen (sk : List UInt8 → Option (List UInt8)) (r : List UInt8) (k : List UInt8 → Option (List UInt8)) :
    Option (List UInt8) :=
  match skipWhitespace r with
  | 0x22 :: r1 => (sk r1).bind fun r2 =>
    match skipWhitespace r2 with
    | 0x3A :: r3 => k r3
    | _ => none
  | _ => none

/-- Pop a frame: done when the stack is empty. -/
def popThen (stk r : List UInt8) (k : UInt8 → List UInt8 → List UInt8 → Option (List UInt8)) :
    Option (List UInt8) :=
  match stk with
  | [] => some r
  | g :: stk => k g stk r

/-- **serde's `ignore_value` (81)**, with fuel: the frames on a stack (`stk`, innermost first, not
counting the current frame of `opened` and `cont`), the scalars skipped by `sv`, the keys by `sk`. -/
def ignM (sv sk : List UInt8 → Option (List UInt8)) : Nat → Mode → List UInt8 → List UInt8 → Option (List UInt8)
  | 0, _, _, _ => none
  | n + 1, .val, stk, bs =>
    match skipWhitespace bs with
    | 0x5B :: r => ignM sv sk n (.opened 0x5B) stk r
    | 0x7B :: r => ignM sv sk n (.opened 0x7B) stk r
    | s => (sv s).bind fun r => popThen stk r fun g stk r => ignM sv sk n (.cont g) stk r
  | n + 1, .opened f, stk, r =>
    if f = 0x5B then
      match skipWhitespace r with
      | 0x5D :: r' => popThen stk r' fun g stk r => ignM sv sk n (.cont g) stk r
      | s => ignM sv sk n .val (0x5B :: stk) s
    else
      match skipWhitespace r with
      | 0x7D :: r' => popThen stk r' fun g stk r => ignM sv sk n (.cont g) stk r
      | s => keyThen sk s (ignM sv sk n .val (0x7B :: stk))
  | n + 1, .cont f, stk, r =>
    match skipWhitespace r with
    | 0x2C :: r' => if f = 0x5B then ignM sv sk n .val (0x5B :: stk) r' else keyThen sk r' (ignM sv sk n .val (0x7B :: stk))
    | 0x5D :: r' => if f = 0x5B then popThen stk r' (fun g stk r => ignM sv sk n (.cont g) stk r) else none
    | 0x7D :: r' => if f = 0x5B then none else popThen stk r' (fun g stk r => ignM sv sk n (.cont g) stk r)
    | _ => none

/-- A frame: `[` or `{`. -/
def Br (f : UInt8) : Prop := f = 0x5B ∨ f = 0x7B

theorem vSkip_length {bs r : List UInt8} (h : vSkip bs = some r) : r.length ≤ bs.length := by
  unfold vSkip at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨v, r'⟩, hv, h⟩ := h
  have := valueR_length hv
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact this

theorem vSkip_skip (bs : List UInt8) : vSkip (skipWhitespace bs) = vSkip bs := by
  unfold vSkip; rw [valueR_skip]

theorem keyAt_skip (bs : List UInt8) : keyAt (skipWhitespace bs) = keyAt bs := by
  unfold keyAt; rw [skip_idem]

theorem keyThen_eq (sk : List UInt8 → Option (List UInt8)) (hsk : ∀ r, sk r = (stringBody r []).map (·.2))
    (r : List UInt8) (k : List UInt8 → Option (List UInt8)) :
    keyThen sk r k = (keyAt r).bind fun x => (colonAt x.2).bind k := by
  unfold keyThen
  split
  · rename_i r1 heq
    rw [keyAt_quote heq, hsk]
    cases stringBody r1 [] with
    | none => rfl
    | some x =>
      obtain ⟨s, r2⟩ := x
      simp only [Option.map_some, Option.bind_some]
      unfold colonAt
      split
      · rename_i r3 heq3
        rw [heq3]; rfl
      · rename_i hn
        split
        · exact absurd ‹_› (hn _)
        · rfl
  · rename_i hn
    rw [keyAt_other (fun r1 e => hn r1 e)]
    rfl

section Spec

variable (sv sk : List UInt8 → Option (List UInt8))

theorem pop_eq (n : Nat) (stk r : List UInt8) (hstk : ∀ g ∈ stk, Br g)
    (ihc : ∀ f stk r, Br f → (∀ g ∈ stk, Br g) → 2 * r.length < n →
      ignM sv sk n (.cont f) stk r = closeAll (f :: stk) r) (hn : 2 * r.length < n) :
    popThen stk r (fun g stk r => ignM sv sk n (.cont g) stk r) = closeAll stk r := by
  cases stk with
  | nil => rfl
  | cons g stk =>
    exact ihc g stk r (hstk g (List.mem_cons_self ..)) (fun x hx => hstk x (List.mem_cons_of_mem _ hx)) hn

theorem br_cons {f : UInt8} {stk : List UInt8} (hf : Br f) (hstk : ∀ g ∈ stk, Br g) : ∀ g ∈ f :: stk, Br g := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hstk g hg

theorem key_step (n : Nat) (stk r : List UInt8) (hstk : ∀ g ∈ stk, Br g)
    (ihv : ∀ stk bs, (∀ g ∈ stk, Br g) → 2 * bs.length + 1 < n →
      ignM sv sk n .val stk bs = (vSkip bs).bind (closeAll stk)) (hn : 2 * r.length + 1 < n) :
    ((keyAt r).bind fun x => (colonAt x.2).bind (ignM sv sk n .val (0x7B :: stk))) =
      (keyAt r).bind fun x => (colonAt x.2).bind fun r2 => (vSkip r2).bind (closeAll (0x7B :: stk)) := by
  cases hk : keyAt r with
  | none => rfl
  | some x =>
    obtain ⟨k, r1⟩ := x
    have l1 : r1.length < r.length := keyAt_len hk
    simp only [Option.bind_some]
    cases hc : colonAt r1 with
    | none => rfl
    | some r2 =>
      have l2 := colonAt_len hc
      simp only [Option.bind_some]
      exact ihv _ _ (br_cons (Or.inr rfl) hstk) (by omega)

/-- **The machine reads what the model reads**: from a value, after the bracket `f`, and after a
value inside the frame `f`, with enough fuel. -/
theorem ignM_spec (hsv : ∀ s, skipWhitespace s = s → (∀ r, s ≠ 0x5B :: r) → (∀ r, s ≠ 0x7B :: r) → sv s = vSkip s)
    (hsk : ∀ r, sk r = (stringBody r []).map (·.2)) (n : Nat) :
    (∀ stk bs, (∀ g ∈ stk, Br g) → 2 * bs.length + 1 < n →
      ignM sv sk n .val stk bs = (vSkip bs).bind (closeAll stk)) ∧
    (∀ f stk r, Br f → (∀ g ∈ stk, Br g) → 2 * r.length + 2 < n →
      ignM sv sk n (.opened f) stk r = (vSkip (f :: r)).bind (closeAll stk)) ∧
    (∀ f stk r, Br f → (∀ g ∈ stk, Br g) → 2 * r.length < n →
      ignM sv sk n (.cont f) stk r = closeAll (f :: stk) r) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
    obtain ⟨ihv, iho, ihc⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro stk bs hstk hn
      rw [ignM, ← vSkip_skip]
      have hsk0 := skip_length bs
      generalize hs : skipWhitespace bs = s at hsk0 ⊢
      split
      · rename_i r
        exact iho 0x5B stk r (Or.inl rfl) hstk (by simp at hsk0; omega)
      · rename_i r
        exact iho 0x7B stk r (Or.inr rfl) hstk (by simp at hsk0; omega)
      · rename_i h1 h2
        have hss : skipWhitespace s = s := by rw [← hs, skip_idem]
        rw [hsv s hss (fun r e => h1 r e) (fun r e => h2 r e)]
        cases hv : vSkip s with
        | none => rfl
        | some r =>
          have := vSkip_length hv
          exact pop_eq sv sk n stk r hstk ihc (by omega)
    · intro f stk r hf hstk hn
      rw [ignM]
      by_cases hfa : f = 0x5B
      · subst hfa
        simp only [ite_true]
        have h0 : skipWhitespace (0x5B :: r) = 0x5B :: r := skip_of_not r rfl
        split
        · rename_i r' heq
          have := skip_cons_length heq
          rw [vSkip_arrE h0 heq]
          exact pop_eq sv sk n stk r' hstk ihc (by omega)
        · rename_i hn'
          rw [vSkip_arrM h0 (fun r' e => hn' r' e), ← vSkip_skip r]
          have := skip_length r
          rw [ihv (0x5B :: stk) _ (by intro g hg; rcases List.mem_cons.mp hg with rfl | hg
                                      · exact Or.inl rfl
                                      · exact hstk g hg) (by omega)]
      · have hfo : f = 0x7B := hf.resolve_left hfa
        subst hfo
        simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false]
        have h0 : skipWhitespace (0x7B :: r) = 0x7B :: r := skip_of_not r rfl
        split
        · rename_i r' heq
          have := skip_cons_length heq
          rw [vSkip_objE h0 heq]
          exact pop_eq sv sk n stk r' hstk ihc (by omega)
        · rename_i hn'
          rw [vSkip_objM h0 (fun r' e => hn' r' e), keyThen_eq sk hsk]
          unfold memberStep
          rw [← keyAt_skip r]
          have := skip_length r
          exact key_step sv sk n stk _ hstk ihv (by omega)
    · intro f stk r hf hstk hn
      rw [ignM]
      generalize hs : skipWhitespace r = s
      split
      · rename_i r'
        have := skip_cons_length hs
        by_cases hfa : f = 0x5B
        · subst hfa
          simp only [ite_true]
          rw [close_arr_comma hs, ihv _ _ (br_cons (Or.inl rfl) hstk) (by omega)]
        · have hfo : f = 0x7B := hf.resolve_left hfa
          subst hfo
          simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false]
          rw [close_obj_comma hs, keyThen_eq sk hsk]
          exact key_step sv sk n stk _ hstk ihv (by omega)
      · rename_i r'
        have := skip_cons_length hs
        by_cases hfa : f = 0x5B
        · subst hfa
          simp only [ite_true]
          rw [close_arr_end hs]
          exact pop_eq sv sk n stk r' hstk ihc (by omega)
        · have hfo : f = 0x7B := hf.resolve_left hfa
          subst hfo
          simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false]
          rw [close_obj_none (by intro r2 e; rw [hs] at e; simp at e) (by intro r2 e; rw [hs] at e; simp at e)]
      · rename_i r'
        have := skip_cons_length hs
        by_cases hfa : f = 0x5B
        · subst hfa
          simp only [ite_true]
          rw [close_arr_none (by intro r2 e; rw [hs] at e; simp at e) (by intro r2 e; rw [hs] at e; simp at e)]
        · have hfo : f = 0x7B := hf.resolve_left hfa
          subst hfo
          simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false]
          rw [close_obj_end hs]
          exact pop_eq sv sk n stk r' hstk ihc (by omega)
      · rename_i h1 h2 h3
        rcases hf with rfl | rfl
        · rw [close_arr_none (fun r2 e => h1 r2 (hs ▸ e)) (fun r2 e => h2 r2 (hs ▸ e))]
        · rw [close_obj_none (fun r2 e => h1 r2 (hs ▸ e)) (fun r2 e => h3 r2 (hs ▸ e))]

/-- **`ignore_value` reads one value as the model does**, up to serde's early failure on `0`
followed by a digit (`vSkip_agrees`). -/
theorem ignM_eq (hsv : ∀ s, skipWhitespace s = s → (∀ r, s ≠ 0x5B :: r) → (∀ r, s ≠ 0x7B :: r) → sv s = vSkip s)
    (hsk : ∀ r, sk r = (stringBody r []).map (·.2)) (bs : List UInt8) :
    ignM sv sk (2 * bs.length + 2) .val [] bs = vSkip bs := by
  rw [(ignM_spec sv sk hsv hsk _).1 [] bs (by simp) (by omega)]
  cases vSkip bs <;> rfl

theorem ignM_agrees (hsv : ∀ s, skipWhitespace s = s → (∀ r, s ≠ 0x5B :: r) → (∀ r, s ≠ 0x7B :: r) → sv s = vSkip s)
    (hsk : ∀ r, sk r = (stringBody r []).map (·.2)) :
    Agrees (fun bs => (ignM sv sk (2 * bs.length + 2) .val [] bs).map fun r => ((), r)) valueSkip := by
  intro bs
  dsimp only
  rw [ignM_eq sv sk hsv hsk bs]
  exact vSkip_agrees bs

end Spec

end WNear.IgnoreModel
