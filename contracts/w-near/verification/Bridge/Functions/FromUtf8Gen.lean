import Bridge.Functions.FromUtf8

/-!
# `core::str::from_utf8` (927) on any bytes (M6)

The general `from_utf8`, against `Utf8.utf8Ok`, for every input. `FromUtf8.f927_spec_ascii` covered
the ASCII paths (the unaligned step, the word loop, the byte loop); this file adds the branch for a
first byte `b ≥ 0x80`:

```wat
w := UTF8_CHAR_WIDTH[b]                  ;; the table at 1071704 (`utf8Width`, `widthData_segment`)
w = 2: [i+1] continuation                ;; else Err
w = 3: [i+1] in the range `b` allows      ;; E0: A0..BF, ED: 80..9F, else 80..BF (`ok3`)
       [i+2] continuation
w = 4: [i+1] in the range `b` allows      ;; F0: 90..BF, F4: 80..8F, else 80..BF (`ok4`)
       [i+2], [i+3] continuations
w = 0: Err                                ;; 80..C1, F5..FF
any byte past the end: Err
i += w; back to the main loop
```

* `utf8Width`, `widthData_segment`, `width_at`: the table, read off the data segment.
* The byte tests (`t_cont`, `t_e0`, `t_pos`, `t_lt160`, …) and the second `br_table`s (`idx3`,
  `idx4`) are `decide`d over the 256 bytes. `mwpi_br_table_k` takes a `br_table` to a label computed
  beforehand: rewriting the label inside the goal, or keeping such a fact in context while stepping,
  sends the step tactics into a deep recursion. For the same reason the facts about the first
  byte's sign extension `s` are kept as one `Hide`, opened only where used.
* `ok_bad0`, `ok_end`, `ok_two`, `ok_three_*`, `ok_four_*`: `utf8Ok` at a non-ASCII first byte,
  one equation per path of the code.
* `f927_spec`: on any `bs`, `Ok(&str)` (`(0, p, len)`) exactly when `utf8Ok bs`, else `Err` with
  some 8 bytes of `Utf8Error`, at `cost927 len = 100 + 100 · len`. The main loop's invariant is
  `FromUtf8.inv927` unchanged (`100` per byte left): a `w`-byte character is paid by its `w` bytes,
  and a rejection by the byte it fails at.

The proof is one declaration, the ASCII paths copied from `f927_spec_ascii`, and takes about four
minutes to check.
-/

namespace WNear.Binary.FromUtf8Gen

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.FromUtf8

/-- The first-byte width class of `core::str::UTF8_CHAR_WIDTH`. -/
def wcls (k : Nat) : Nat :=
  if k < 0x80 then 1 else if k < 0xC2 then 0 else if k < 0xE0 then 2 else if k < 0xF0 then 3
  else if k < 0xF5 then 4 else 0

/-- `UTF8_CHAR_WIDTH`, the table 927 reads at 1071704. -/
def utf8Width : List UInt8 := (List.range 256).map fun k => UInt8.ofNat (wcls k)

set_option maxRecDepth 100000 in
/-- The table is the data segment's bytes at 1071704. -/
theorem widthData_segment :
    (List.range 256).map (fun k => wNearSource.read (159306 + (1071704 - 1048576) + k)) = utf8Width := by
  decide +kernel

theorem utf8Width_length : utf8Width.length = 256 := by simp [utf8Width]

set_option maxRecDepth 100000 in
theorem width_at (b : UInt8) :
    (utf8Width[b.toNat]'(by rw [utf8Width_length]; exact b.toNat_lt)).toUInt32 = UInt32.ofNat (wcls b.toNat) := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem wcls_0 (k : Nat) (h : 128 ≤ k) (h' : k < 0xC2 ∨ 0xF5 ≤ k) : wcls k = 0 := by
  unfold wcls; split_ifs <;> omega
theorem wcls_2 (k : Nat) (h : 0xC2 ≤ k) (h' : k < 0xE0) : wcls k = 2 := by
  unfold wcls; split_ifs <;> omega
theorem wcls_3 (k : Nat) (h : 0xE0 ≤ k) (h' : k < 0xF0) : wcls k = 3 := by
  unfold wcls; split_ifs <;> omega
theorem wcls_4 (k : Nat) (h : 0xF0 ≤ k) (h' : k < 0xF5) : wcls k = 4 := by
  unfold wcls; split_ifs <;> omega

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem res927_err (n : Nat) (out p len : UInt32) (bs : List UInt8) (hbad : Utf8.utf8Ok bs = false)
    (v : Value) :
    n ↦[i32][ out.toNat ] 1 ∗ n ↦[wms][ out.toNat + 4 ] storeBytes v 8 ⊢ res927 (GF := GF) n out p len bs := by
  iintro ⟨H0, H4⟩
  unfold res927
  rw [hbad]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iexists storeBytes v 8
  iframe H0 H4
  ipureintro; simp [storeBytes]

end Res

/-! ## `utf8Ok` at a non-ASCII first byte -/

theorem ok_end (b : UInt8) (h : 128 ≤ b.toNat) : Utf8.utf8Ok [b] = false := by
  simp [Utf8.utf8Ok]; omega

theorem ok_two (b x : UInt8) (r : List UInt8) (h : 0xC2 ≤ b.toNat) (h' : b.toNat < 0xE0) :
    Utf8.utf8Ok (b :: x :: r) = (Utf8.cont x && Utf8.utf8Ok r) := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = true := by simp [Utf8.lead2]; omega
  simp only [this, hl, ↓reduceIte]

/-! ## The byte tests -/

theorem ofNat_add1 (i : Nat) (h : i + 1 < 2 ^ 32) : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
  apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega
theorem ofNat_add2 (i : Nat) (h : i + 2 < 2 ^ 32) : UInt32.ofNat i + 2 = UInt32.ofNat (i + 2) := by
  apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega
theorem ofNat_add3 (i : Nat) (h : i + 3 < 2 ^ 32) : UInt32.ofNat i + 3 = UInt32.ofNat (i + 3) := by
  apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega

theorem geu_ofNat (j : Nat) (len : UInt32) (h : j < 2 ^ 32) :
    Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat j) len) = if len.toNat ≤ j then 1 else 0 := by
  have e : (UInt32.ofNat j).toNat = j := by simp; omega
  simp only [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le, e]
  by_cases hj : len.toNat ≤ j <;> simp [hj]

set_option maxRecDepth 100000 in
/-- `[x] & 0xC0 = 0x80`: a continuation byte. -/
theorem t_cont (x : UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq (x.toUInt32 &&& 192) 128) = if Utf8.cont x then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_ncont (x : UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.ne (x.toUInt32 &&& 192) 128) = if Utf8.cont x then 0 else 1 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

theorem ok_bad0 (b : UInt8) (r : List UInt8) (h : 128 ≤ b.toNat) (h' : b.toNat < 0xC2 ∨ 0xF5 ≤ b.toNat) :
    Utf8.utf8Ok (b :: r) = false := by
  rcases r with _ | ⟨x, r⟩
  · simp [Utf8.utf8Ok]; omega
  · rw [Utf8.utf8Ok.eq_def]
    have : ¬ b.toNat < 128 := by omega
    have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
    have h3 : Utf8.ok3 b x = false := by simp [Utf8.ok3]; omega
    have h4 : Utf8.ok4 b x = false := by simp [Utf8.ok4]; omega
    simp only [this, hl, h3, h4, ↓reduceIte, Bool.false_eq_true]

theorem ok_three_bad (b x : UInt8) (r : List UInt8) (h : 0xE0 ≤ b.toNat) (h' : b.toNat < 0xF0)
    (h3 : Utf8.ok3 b x = false) : Utf8.utf8Ok (b :: x :: r) = false := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  have h4 : Utf8.ok4 b x = false := by simp [Utf8.ok4]; omega
  simp only [this, hl, h3, h4, ↓reduceIte, Bool.false_eq_true]

theorem ok_three_end (b x : UInt8) (h : 0xE0 ≤ b.toNat) (h' : b.toNat < 0xF0) : Utf8.utf8Ok [b, x] = false := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  have h4 : Utf8.ok4 b x = false := by simp [Utf8.ok4]; omega
  simp only [this, hl, h4, ↓reduceIte, Bool.false_eq_true]
  split <;> rfl

theorem ok_three_ok (b x y : UInt8) (r : List UInt8) (h : 0xE0 ≤ b.toNat) (h' : b.toNat < 0xF0)
    (h3 : Utf8.ok3 b x = true) : Utf8.utf8Ok (b :: x :: y :: r) = (Utf8.cont y && Utf8.utf8Ok r) := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  simp only [this, hl, h3, ↓reduceIte, Bool.false_eq_true]

theorem ok_four_bad (b x : UInt8) (r : List UInt8) (h : 0xF0 ≤ b.toNat) (h' : b.toNat < 0xF5)
    (h4 : Utf8.ok4 b x = false) : Utf8.utf8Ok (b :: x :: r) = false := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  have h3 : Utf8.ok3 b x = false := by simp [Utf8.ok3]; omega
  simp only [this, hl, h3, h4, ↓reduceIte, Bool.false_eq_true]

theorem ok_four_short (b x : UInt8) (r : List UInt8) (hr : r.length < 2) (h : 0xF0 ≤ b.toNat)
    (h' : b.toNat < 0xF5) : Utf8.utf8Ok (b :: x :: r) = false := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  have h3 : Utf8.ok3 b x = false := by simp [Utf8.ok3]; omega
  simp only [this, hl, h3, ↓reduceIte, Bool.false_eq_true]
  rcases r with _ | ⟨y, _ | ⟨z, r⟩⟩
  · split <;> rfl
  · split <;> rfl
  · simp at hr; omega

theorem ok_four_ok (b x y z : UInt8) (r : List UInt8) (h : 0xF0 ≤ b.toNat) (h' : b.toNat < 0xF5)
    (h4 : Utf8.ok4 b x = true) :
    Utf8.utf8Ok (b :: x :: y :: z :: r) = (Utf8.cont y && Utf8.cont z && Utf8.utf8Ok r) := by
  rw [Utf8.utf8Ok.eq_def]
  have : ¬ b.toNat < 128 := by omega
  have hl : Utf8.lead2 b = false := by simp [Utf8.lead2]; omega
  have h3 : Utf8.ok3 b x = false := by simp [Utf8.ok3]; omega
  simp only [this, hl, h3, h4, ↓reduceIte, Bool.false_eq_true]

section Join
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem join2 (P Q : IProp GF) : P ∗ Q ⊢ P ∗ Q := .rfl
end Join

set_option maxRecDepth 100000 in
theorem idx3 : ∀ b : UInt8, 0xE0 ≤ b.toNat → b.toNat < 0xF0 →
    ([0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967072).toNat]?.getD 2 =
      if b.toNat = 0xE0 then 0 else if b.toNat = 0xED then 1 else 2 :=
  SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem idx4 : ∀ b : UInt8, 0xF0 ≤ b.toNat → b.toNat < 0xF5 →
    ([0, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967056).toNat]?.getD 2 =
      if b.toNat = 0xF0 then 0 else if b.toNat = 0xF4 then 1 else 2 :=
  SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_e0 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq (x.toUInt32 &&& 224) 160) =
    if 0xA0 ≤ x.toNat ∧ x.toNat < 0xC0 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_pos (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.gt_s (sb x) 4294967295) =
    if x.toNat < 128 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_lt160 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (x.toUInt32 &&& 255) 160) =
    if x.toNat < 160 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_lt192 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (x.toUInt32 &&& 255) 192) =
    if x.toNat < 192 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_gt191 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (x.toUInt32 &&& 255) 191) =
    if 191 < x.toNat then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_ge144 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (x.toUInt32 &&& 255) 144) =
    if 144 ≤ x.toNat then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_f0 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ge_u ((x.toUInt32 + 112) &&& 255) 48) =
    if 0x90 ≤ x.toNat ∧ x.toNat < 0xC0 then 0 else 1 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_b31 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((sb b + 31) &&& 255) 11) =
    if 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_b254 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ne (sb b &&& 254) 238) =
    if b.toNat = 0xEE ∨ b.toNat = 0xEF then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t_b15 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((sb b + 15) &&& 255) 2) =
    if 0xF1 ≤ b.toNat ∧ b.toNat ≤ 0xF3 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- An equation kept out of reach of the step tactics. -/
def Hide (p : Prop) : Prop := p

section BrT
variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF}

/-- `br_table` to a label computed beforehand (`hk`), so that no rewrite touches the goal. -/
theorem mwpi_br_table_k {ls : List Nat} {dflt k : Nat} {rest : List Value} {c : UInt32}
    (hk : ls[c.toNat]?.getD dflt = k) :
    ⌜vs.reverse = .i32 c :: rest⌝ ∗ Φ.br k rest.reverse f ⊢ mwpi cfg lim d f vs [.br_table ls dflt] Φ := by
  subst hk; exact mwpi_br_table'
end BrT


set_option hygiene false in
/-- A `br_if` taken (the condition `h`), out of the enclosing blocks. -/
local macro "brt " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, $h⟩
  mctrl_norm; repeat mpay))

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

set_option hygiene false in
/-- Out of the main loop with `Ok` (`hok'` for `j ≥ len` in context): the result `(0, p, len)`. -/
local macro "exit927" : tactic => `(tactic| (
  icases Ho with ⟨Ho, Ht⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ O4 with ⟨O4, O8⟩
  mstep; mstep
  mstep [O4]
  mstep; mstep; mstep; mstep
  mstep [O8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep [O0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hb Ht
  iapply res927_ok n out p len bs (by rw [hok', List.drop_eq_nil_of_le (by omega)]; simp [Utf8.utf8Ok])
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe O0 O4 O8))

set_option hygiene false in
/-- The main loop's test `j < len` at its end (`hok'` for `j` in context): back to the invariant
at `j`, or out of the loop with `Ok` when `j = len`. -/
local macro "tail927 " j:term:max : tactic => `(tactic| (
  by_cases hj : $j < bs.length
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) ≠ 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hc⟩
    (try simp only [Post.mloop]); (try dsimp only); (try simp only [List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil, List.drop_length])
    iapply pure_pay_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by simp, by omega⟩
    inext
    iintro Hc
    iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ $j _ _ _ _ _ hj hok'
    iframe Hb Ho
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) = 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    brn hc
    mstep
    (try simp only [Post.mloop]); (try dsimp only); (try simp only [List.append_nil, List.nil_append])
    repeat mpay
    exit927))

set_option hygiene false in
/-- The byte loop at `k` on an ASCII byte `x` (`hxa`, `hokk'` for `k + 1`, `hZ'` in context): on to
`k + 1`, or out with `Ok` at the end. -/
local macro "bascii10" : tactic => `(tactic| (
  mstep; mstep
  have hn0 := sx_neg x
  rw [if_pos hxa] at hn0
  generalize sx x = sv at hn0 ⊢
  brn hn0
  clear hn0
  mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.ofNat_succ k (by omega)]
  by_cases hk1 : k + 1 < bs.length
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne len (UInt32.ofNat (k + 1))) ≠ 0 := by
      have hu : (UInt32.ofNat (k + 1)).toNat = k + 1 := by simp; omega
      generalize UInt32.ofNat (k + 1) = u at hu ⊢
      have : len ≠ u := fun e => by subst e; omega
      simp [Numeric.bool, Numeric.irelop32, this]
    iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hc⟩
    mctrl_norm
    simp only [Post.mloop, List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
    iapply pure_pay_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by simp, by omega⟩
    inext
    iintro Hc
    iapply invA_intro n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len _ a s l8 l9 l10 bs i _ (k + 1) _
      (by omega) (by omega) hokk'
    iframe Hb Ho
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [if_neg (by omega)]
    rw [show bs.length - (k + 1) = bs.length - (k + 1 + 1) + 1 by omega, Nat.mul_add, Nat.add_mul] at hZ'
    omega
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne len (UInt32.ofNat (k + 1))) = 0 := by
      have hu : (UInt32.ofNat (k + 1)).toNat = k + 1 := by simp; omega
      generalize UInt32.ofNat (k + 1) = u at hu ⊢
      have : len = u := by apply UInt32.toNat_inj.mp; omega
      simp [Numeric.bool, Numeric.irelop32, this]
    brn hc
    mstep
    simp only [Post.mloop]
    mctrl_norm
    repeat mpay
    have hok' := hokk'
    exit927))

set_option hygiene false in
/-- The byte loop's body (`invA … 1`, entered at `i` whose byte `b` is ASCII: `hbk`, `hasc`). -/
local macro "body10" : tactic => `(tactic| (
  iintro %X %l HI
  iunfold invA at HI
  icases HI with ⟨%k, %l6', %⟨hX, hfr', hik, hkl, hokk⟩, Hc, Hb, Ho⟩
  subst hX
  rw [hfr']
  simp only [fr927]
  clear hfr'
  have hkb : k < bs.length := by omega
  ihave Hb := MemCpy.memBytes_pick n p.toNat k bs hkb $$ Hb
  icases Hb with ⟨B1, Bk, B2⟩
  obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
  rw [hxk]
  have hdk : bs.drop k = x :: bs.drop (k + 1) := by rw [List.drop_eq_getElem_cons hkb, hxk]
  have esk : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
  by_cases hki : k = i
  next =>
    rw [if_pos hki, show 100 * (bs.length - (k + 1)) * cfg.regularOpCost + 104 * cfg.regularOpCost + R =
      104 * cfg.regularOpCost + (100 * (bs.length - (k + 1)) * cfg.regularOpCost + R) by omega]
    generalize hZ' : 100 * (bs.length - (k + 1)) * cfg.regularOpCost = Z'
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    rw [load8s]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    rw [esk]
    have hxa : x.toNat < 128 := by subst hki; rw [hbk] at hxk; subst hxk; exact hasc
    have hokk' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (k + 1)) := by
      rw [hokk, hdk, Utf8.utf8Ok_ascii x _ hxa]
    bascii10
  next =>
    rw [if_neg hki, show 100 * (bs.length - (k + 1)) * cfg.regularOpCost + 186 * cfg.regularOpCost + R =
      186 * cfg.regularOpCost + (100 * (bs.length - (k + 1)) * cfg.regularOpCost + R) by omega]
    generalize hZ' : 100 * (bs.length - (k + 1)) * cfg.regularOpCost = Z'
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    rw [load8s]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    rw [esk]
    by_cases hxa : x.toNat < 128
    next =>
      have hokk' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (k + 1)) := by
        rw [hokk, hdk, Utf8.utf8Ok_ascii x _ hxa]
      bascii10
    next =>
      mstep; mstep
      have hn1 := sx_neg x
      rw [if_neg hxa] at hn1
      generalize sx x = sv at hn1 ⊢
      iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, by rw [hn1]; decide⟩
      mctrl_norm
      simp only [Post.mloop]
      mctrl_norm
      repeat mpay
      clear hn1
      have hok' := hokk
      have hZk : 100 * (bs.length - k) * cfg.regularOpCost = 100 * cfg.regularOpCost + Z' := by
        rw [← hZ', show bs.length - k = bs.length - (k + 1) + 1 by omega, Nat.mul_add, Nat.add_mul]; omega
      mstep; mstep; mstep
      by_cases hj : k < bs.length
      next =>
        have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat k) len) ≠ 0 := by
          rw [ltu_ofNat _ _ (by omega)]; simp; omega
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, hc⟩
        dsimp only
        simp only [List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ k _ _ _ _ _ hj hok'
        iframe Hb Ho
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      next => exfalso; omega))

set_option hygiene false in
/-- After the word loop, at `j` (`hok'` for `j`, `hji : i ≤ j`, `j ≤ len`): `j < len` runs the byte
loop from `j`; `j = len` is `Ok`. -/
local macro "bytes10 " j:term:max : tactic => `(tactic| (
    have hg2 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat $j) len) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    brn hg2
    clear hg2
    iapply MemCpy.mwpi_loop0 (Cg := Cg)
      (R := 100 * (bs.length - ($j + 1)) * cfg.regularOpCost + (ite ($j = i) 104 186) * cfg.regularOpCost + R)
      (I := invA n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len (UInt32.ofNat (len.toNat - 7)) a s l8 l9 l10
        bs i iprop(n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1071704 ] utf8Width)) _ _ rfl
    isplitr
    · imodintro
      body10
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      split <;> omega
    inext
    iintro Hc
    iapply invA_intro n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len _ a s l8 l9 l10 bs i _ $j _ hji
      (by omega) hok'
    iframe Hb Ho Hc))

set_option hygiene false in
/-- `after10` where `j < len`. -/
local macro "after10x " j:term:max : tactic => `(tactic| (
  mstep; mstep; mstep
  by_cases hjl : $j < bs.length
  next => bytes10 $j
  next => exfalso; omega))

set_option hygiene false in
local macro "after10 " j:term:max : tactic => `(tactic| (
  mstep; mstep; mstep
  by_cases hjl : $j < bs.length
  next => bytes10 $j
  next =>
    have hg2 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat $j) len) ≠ 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    brt hg2
    clear hg2
    mstep; mstep; mstep
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) = 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    brn hc
    mstep
    exit927))

set_option hygiene false in
/-- The word loop's body at `j` (`j + 8 ≤ len`), the credits `D · c + (Zj + R)`. -/
local macro "word11" : tactic => `(tactic| (
  ihave Hb := window_split n p.toNat j bs hj8 $$ Hb
  icases Hb with ⟨W0, Wa, Wb, W2⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [Wb] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep [Wa] with (simp [UInt32.toNat_add]; omega)
  ihave Hb := window_join n p.toNat j bs hj8 $$ [W0 Wa Wb W2]
  · iframe W0 Wa Wb W2
  mstep; mstep; mstep
  by_cases hm : (UInt32.ofNat (Memory.decodeLE (List.drop 4 (List.take 8 (List.drop j bs)))) |||
      UInt32.ofNat (Memory.decodeLE (List.take 4 (List.take 8 (List.drop j bs))))) &&& 2155905152 = 0
  · have h8 := window_ascii _ _ (by simp; omega) (by simp; omega) hm
    have hok8 : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (j + 8)) := by
      rw [hokj, utf8Ok_skip bs j 8 (by intro b hb; apply h8; rw [List.take_append_drop]; exact hb)]
    clear h8
    generalize (UInt32.ofNat (Memory.decodeLE (List.drop 4 (List.take 8 (List.drop j bs)))) |||
      UInt32.ofNat (Memory.decodeLE (List.take 4 (List.take 8 (List.drop j bs))))) &&& 2155905152 = mv at hm ⊢
    subst hm
    brn rfl
    mstep; mstep; mstep; mstep
    rw [show UInt32.ofNat j + 8 = UInt32.ofNat (j + 8) by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega]
    mstep; mstep
    by_cases hj16 : j + 8 + 8 ≤ bs.length
    · have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (j + 8)) (UInt32.ofNat (len.toNat - 7))) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, hc⟩
      simp only [Post.mloop, List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iapply invA_intro n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len _ a s l8 l9 l10 bs i _ (j + 8) _
        (by omega) hj16 hok8
      iframe Hb Ho
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      rw [if_neg (by omega)]
      omega
    · have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (j + 8)) (UInt32.ofNat (len.toNat - 7))) = 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      brn hc
      mstep
      simp only [Post.mloop, List.append_nil]
      repeat mpay
      have hok' := hok8
      have hji' : i ≤ j + 8 := by omega
      clear hji
      have hji := hji'
      after10 (j + 8)
  · iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hm⟩
    mctrl_norm
    simp only [Post.mloop]
    mctrl_norm
    repeat mpay
    clear hm
    have hok' := hokj
    after10x j))


set_option hygiene false in
/-- The error store (`hbad : utf8Ok bs = false` in context): `(1, Utf8Error)` at `out`, then `return`. -/
local macro "err927" : tactic => `(tactic| (
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [O4] with (simp [hob]; omega)
  mstep; mstep
  mstep [O0]
  mstep
  (try simp only [Post.mloop]); mctrl_norm; repeat mpay
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hb Ht
  iapply res927_err n out p len bs hbad _
  iframe O0 O4))

set_option hygiene false in
/-- Load the input byte at `k` (`k < len`), naming it `x` (`hx : bs[k] = x`). -/
local macro "ldb " k:term:max x:ident hx:ident : tactic => `(tactic| (
  ihave Hb := MemCpy.memBytes_pick n p.toNat $k bs (by omega) $$ Hb
  icases Hb with ⟨B1, Bk, B2⟩
  obtain ⟨$x, $hx⟩ : ∃ x, bs[$k]'(by omega) = x := ⟨_, rfl⟩
  rw [$hx:ident]
  mstep [Bk] with (simp [UInt32.toNat_add]; omega)
  simp only [SerdeKey.load8]
  ihave Hb := MemCpy.memBytes_unpick n p.toNat $k (bs.take $k) $x (bs.drop ($k + 1)) (by simp; omega) $$ [B1 Bk B2]
  · iframe B1 Bk B2
  rw [show List.take $k bs ++ $x :: List.drop ($k + 1) bs = bs by rw [← $hx]; simp]))

set_option hygiene false in
/-- Put the output bytes and the width table back together (the loop invariants' frame). -/
local macro "rejoin" : tactic => `(tactic| (
  ihave Ho := join2 (n ↦[wms][ out.toNat ] ob) (n ↦[wms][ 1071704 ] utf8Width) $$ [Ho Ht]
  · iframe Ho Ht))

set_option hygiene false in
/-- The 7-instruction error prelude (`l8`, `l9` set, then `br 1`) before the error store. -/
local macro "err7" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep
  err927))

set_option hygiene false in
/-- The third byte of a three-byte character (`hok3 : ok3 b x` and `hd1` in context). -/
local macro "cont3" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep
  rw [ofNat_add2 i (by omega)]
  mstep; mstep; mstep
  rw [geu_ofNat _ _ (by omega)]
  by_cases h2 : i + 2 < bs.length
  next =>
    rw [if_neg (by omega)]
    brn rfl
    mstep; mstep; mstep
    ldb (i + 2) y hy
    have hd2 : bs.drop (i + 2) = y :: bs.drop (i + 3) := by rw [List.drop_eq_getElem_cons h2, hy]
    mstep; mstep; mstep; mstep
    rw [t_cont]
    by_cases hcy : Utf8.cont y
    next =>
      rw [if_pos hcy]
      brt (by decide)
      mstep; mstep; mstep
      rw [ofNat_add1 (i + 2) (by omega)]
      mstep; mstep
      have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (i + 3)) := by
        rw [hok, hdrop, hd1, hd2, ok_three_ok b x y _ (by omega) hc3 hok3, hcy, Bool.true_and]
      have hZ3 : Z = 200 * cfg.regularOpCost + 100 * (bs.length - (i + 3)) * cfg.regularOpCost := by
        rw [← hZ, show bs.length - (i + 1) = (bs.length - (i + 3)) + 2 by omega, Nat.mul_add, Nat.add_mul]; omega
      mstep; mstep; mstep
      rw [show i + 2 + 1 = i + 3 by omega]
      rejoin
      tail927 (i + 3)
    next =>
      rw [if_neg hcy]
      brn rfl
      mstep
      mstep; mstep; mstep; mstep
      have hbad : Utf8.utf8Ok bs = false := by
        rw [hok, hdrop, hd1, hd2, ok_three_ok b x y _ (by omega) hc3 hok3]; simp [hcy]
      err927
  next =>
    rw [if_pos (by omega)]
    brt (by decide)
    have hbad : Utf8.utf8Ok bs = false := by
      rw [hok, hdrop, hd1, List.drop_eq_nil_of_le (by omega)]; exact ok_three_end b x (by omega) hc3
    err927))

set_option hygiene false in
/-- The sign test `(x << 24 >>s 24) > -1` on the byte `x`: leaves `x < 128` on the stack. -/
local macro "sgn " x:ident : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep
  rw [show Numeric.intToUInt32 ((UInt8.toUInt32 $x <<< ((24 : UInt32) % 32)).toIntS >>> ((24 : UInt32) % 32).toNat) = sb $x from rfl]
  have hp := t_pos $x
  generalize sb $x = u at hp ⊢
  mstep; mstep
  rw [hp]
  clear hp))

set_option hygiene false in
/-- The last two bytes of a four-byte character (`hok4 : ok4 b x`, `hd1`, `hc4'`, `hc4` in context). -/
local macro "cont4" : tactic => `(tactic| (
  mstep
  mstep; mstep; mstep
  rw [ofNat_add2 i (by omega)]
  mstep; mstep; mstep
  rw [ltu_ofNat _ _ (by omega)]
  by_cases h2 : i + 2 < bs.length
  next =>
    rw [if_pos (by omega)]
    brt (by decide)
    mstep; mstep; mstep
    ldb (i + 2) y hy
    have hd2 : bs.drop (i + 2) = y :: bs.drop (i + 3) := by rw [List.drop_eq_getElem_cons h2, hy]
    mstep; mstep; mstep; mstep
    rw [t_ncont]
    by_cases hcy : Utf8.cont y
    next =>
      rw [if_pos hcy]
      brn rfl
      mstep; mstep; mstep; mstep; mstep
      rw [ofNat_add3 i (by omega)]
      mstep; mstep; mstep
      rw [geu_ofNat _ _ (by omega)]
      by_cases h3 : i + 3 < bs.length
      next =>
        rw [if_neg (by omega)]
        brn rfl
        mstep; mstep; mstep
        ldb (i + 3) z hz
        have hd3 : bs.drop (i + 3) = z :: bs.drop (i + 4) := by rw [List.drop_eq_getElem_cons h3, hz]
        mstep; mstep; mstep; mstep
        rw [t_cont]
        by_cases hcz : Utf8.cont z
        next =>
          rw [if_pos hcz]
          brt (by decide)
          mstep; mstep; mstep
          rw [ofNat_add1 (i + 3) (by omega)]
          mstep; mstep
          have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (i + 4)) := by
            rw [hok, hdrop, hd1, hd2, hd3, ok_four_ok b x y z _ hc4' hc4 hok4, hcy, hcz]; simp
          have hZ4 : Z = 300 * cfg.regularOpCost + 100 * (bs.length - (i + 4)) * cfg.regularOpCost := by
            rw [← hZ, show bs.length - (i + 1) = (bs.length - (i + 4)) + 3 by omega, Nat.mul_add, Nat.add_mul]; omega
          mstep; mstep; mstep
          rw [show i + 3 + 1 = i + 4 by omega]
          rejoin
          tail927 (i + 4)
        next =>
          rw [if_neg hcz]
          brn rfl
          mstep; mstep; mstep; mstep; mstep
          have hbad : Utf8.utf8Ok bs = false := by
            rw [hok, hdrop, hd1, hd2, hd3, ok_four_ok b x y z _ hc4' hc4 hok4]; simp [hcz]
          err927
      next =>
        rw [if_pos (by omega)]
        brt (by decide)
        have hbad : Utf8.utf8Ok bs = false := by
          rw [hok, hdrop, hd1]; exact ok_four_short b x _ (by simp; omega) hc4' hc4
        err927
    next =>
      rw [if_neg hcy]
      brt (by decide)
      mstep; mstep; mstep; mstep
      have hbad : Utf8.utf8Ok bs = false := by
        rw [hok, hdrop, hd1, hd2]
        rcases e : bs.drop (i + 3) with _ | ⟨z, r⟩
        · exact ok_four_short b x _ (by simp) hc4' hc4
        · rw [ok_four_ok b x y z r hc4' hc4 hok4]; simp [hcy]
      err927
  next =>
    rw [if_neg (by omega)]
    brn rfl
    mstep; mstep; mstep
    have hbad : Utf8.utf8Ok bs = false := by
      rw [hok, hdrop, hd1]; exact ok_four_short b x _ (by simp; omega) hc4' hc4
    err927))

section L927

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`core::str::from_utf8(out, p, len)`** (927) on any `bs` at `p`, the width table at 1071704
owned: `Ok(&str)` exactly when `utf8Ok bs`, else `Err` (`res927`), at `cost927 len = 100 + 100 · len`. -/
theorem f927_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out p len : UInt32) (ob bs : List UInt8)
    (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = len.toNat)
    (hp : p.toNat + len.toNat ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f927 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 p, .i32 len]⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
          (n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1071704 ] utf8Width)))
        (fun _ => cost927 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[wms][ p.toNat ] bs ∗ res927 n out p len bs ∗ n ↦[wms][ 1071704 ] utf8Width)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hb, Ho⟩
  subst hargs
  simp only [f927, cost927]
  have hlt := len.toNat_lt
  by_cases hl0 : len.toNat = 0
  · have hl : len = 0 := by apply UInt32.toNat_inj.mp; simpa using hl0
    mstep; mstep; mstep
    mstep_taken with simp [hl, Numeric.bool]
    have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (List.drop 0 bs) := rfl
    exit927
  have hne : len ≠ 0 := fun e => by simp [e] at hl0
  rw [show (100 + 100 * len.toNat) * cfg.regularOpCost + R = 30 * cfg.regularOpCost + (70 * cfg.regularOpCost + 100 * len.toNat * cfg.regularOpCost + R) by rw [Nat.add_mul]; omega]
  generalize hM : 70 * cfg.regularOpCost + 100 * len.toNat * cfg.regularOpCost + R = M
  repeat mstep
  iapply mwpi_cons
  iapply mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; omega
  inext
  iintro Hc
  rw [wlim_eq]
  mctrl_norm
  repeat mstep
  generalize ha : (p + 3 &&& 4294967292) - p = a
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := M)
    (I := inv927 n inst mi Cg cfg.regularOpCost 100 70 R out p len (UInt32.ofNat (len.toNat - 7)) a bs
      iprop(n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1071704 ] utf8Width)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv927 at HI
    icases HI with ⟨%i, %l6, %l7, %l8, %l9, %l10, %⟨hX, hfr, hi, hok⟩, Hc, Hb, Ho⟩
    subst hX
    rw [hfr]
    simp only [fr927]
    rw [show 100 * (bs.length - i) * cfg.regularOpCost + 70 * cfg.regularOpCost + R =
      170 * cfg.regularOpCost + (100 * (bs.length - (i + 1)) * cfg.regularOpCost + R) by
        rw [show 100 * (bs.length - i) = 100 + 100 * (bs.length - (i + 1)) by omega, Nat.add_mul]; omega]
    generalize hZ : 100 * (bs.length - (i + 1)) * cfg.regularOpCost = Z
    ihave Hb := MemCpy.memBytes_pick n p.toNat i bs (by omega) $$ Hb
    icases Hb with ⟨B1, Bk, B2⟩
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    simp only [SerdeKey.load8]
    obtain ⟨b, hbk⟩ : ∃ b, bs[i] = b := ⟨_, rfl⟩
    rw [hbk]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat i (bs.take i) b (bs.drop (i + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    have es : List.take i bs ++ b :: List.drop (i + 1) bs = bs := by rw [← hbk]; simp
    rw [es]
    have hdrop : bs.drop i = b :: bs.drop (i + 1) := by rw [List.drop_eq_getElem_cons hi, hbk]
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    rw [show Numeric.intToUInt32 ((b.toUInt32 <<< ((24 : UInt32) % 32)).toIntS >>> ((24 : UInt32) % 32).toNat) = sb b from rfl]
    by_cases hasc : b.toNat < 128
    · have hn0 := sb_neg b
      rw [if_pos hasc] at hn0
      generalize sb b = s at hn0 ⊢
      mstep
      brn hn0
      clear hn0
      mstep; mstep; mstep
      have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (i + 1)) := by
        rw [hok, hdrop, Utf8.utf8Ok_ascii b _ hasc]
      by_cases ha1 : a = 4294967295
      · have he1 : Numeric.bool (Numeric.irelop32 IRelOp.ne a 4294967295) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, ha1]
        clear ha1
        brn he1
        clear he1
        mstep
        mstep; mstep; mstep; mstep
        rw [SerdeRead.ofNat_succ i (by omega)]
        mstep; mstep; mstep
        tail927 (i + 1)
      · have hne1 : Numeric.bool (Numeric.irelop32 IRelOp.ne a 4294967295) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32, ha1]
        brt hne1
        clear hne1
        mstep; mstep; mstep; mstep; mstep
        by_cases hal : (a - UInt32.ofNat i &&& 3) = 0
        · brn hal
          clear hal
          mstep
          mstep; mstep; mstep
          by_cases hw : i + 8 ≤ bs.length
          · have hg : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat (len.toNat - 7))) = 0 := by
              simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
            brn hg
            clear hg
            iapply MemCpy.mwpi_loop0 (Cg := Cg)
              (R := 100 * (bs.length - (i + 1)) * cfg.regularOpCost + 124 * cfg.regularOpCost + R)
              (I := invA n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len (UInt32.ofNat (len.toNat - 7)) a s l8 l9 l10
                bs i iprop(n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1071704 ] utf8Width)) _ _ rfl
            isplitr
            · imodintro
              iintro %X %l HI
              iunfold invA at HI
              icases HI with ⟨%j, %l6', %⟨hX, hfr', hji, hj8, hokj⟩, Hc, Hb, Ho⟩
              subst hX
              rw [hfr']
              simp only [fr927]
              clear hfr'
              have hZ8 : 100 * (bs.length - (j + 8 + 1)) * cfg.regularOpCost + 700 * cfg.regularOpCost ≤
                  100 * (bs.length - (j + 1)) * cfg.regularOpCost := by
                rw [← Nat.add_mul]; apply Nat.mul_le_mul_right; omega
              by_cases hjeq : j = i
              · rw [if_pos hjeq, show 100 * (bs.length - (j + 1)) * cfg.regularOpCost + 124 * cfg.regularOpCost + R =
                  124 * cfg.regularOpCost + (100 * (bs.length - (j + 1)) * cfg.regularOpCost + R) by omega]
                generalize hZj : 100 * (bs.length - (j + 1)) * cfg.regularOpCost = Zj at hZ8
                word11
              · rw [if_neg hjeq, show 100 * (bs.length - (j + 1)) * cfg.regularOpCost + 210 * cfg.regularOpCost + R =
                  210 * cfg.regularOpCost + (100 * (bs.length - (j + 1)) * cfg.regularOpCost + R) by omega]
                generalize hZj : 100 * (bs.length - (j + 1)) * cfg.regularOpCost = Zj at hZ8
                word11
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            inext
            iintro Hc
            iapply invA_intro n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len _ a s l8 l9 l10 bs i _ i _ le_rfl
              hw hok
            iframe Hb Ho
            rw [if_pos rfl]
            iframe Hc
          · have hg : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat (len.toNat - 7))) ≠ 0 := by
              simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
            brt hg
            clear hg
            have hok' := hok
            have hji : i ≤ i := le_rfl
            after10x i
        · brt hal
          mstep; mstep; mstep; mstep
          rw [SerdeRead.ofNat_succ i (by omega)]
          mstep; mstep; mstep
          tail927 (i + 1)
    · have hn1 := sb_neg b
      rw [if_neg hasc] at hn1
      have T31 := t_b31 b
      have T254 := t_b254 b
      have T15 := t_b15 b
      generalize sb b = s at hn1 T31 T254 T15 ⊢
      have hT : Hide (_ ∧ _ ∧ _) := And.intro T31 (And.intro T254 T15)
      clear T31 T254 T15
      mstep
      brt (by rw [hn1]; decide)
      clear hn1
      icases Ho with ⟨Ho, Ht⟩
      mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep; mstep; mstep
      have hb8 := b.toNat_lt
      ihave Ht := MemCpy.memBytes_pick n 1071704 b.toNat utf8Width (by rw [utf8Width_length]; exact b.toNat_lt) $$ Ht
      icases Ht with ⟨T1, Tk, T2⟩
      mstep [Tk] with (simp [UInt32.toNat_add]; omega)
      rw [SerdeKey.load8, width_at]
      ihave Ht := MemCpy.memBytes_unpick n 1071704 b.toNat (utf8Width.take b.toNat) _ (utf8Width.drop (b.toNat + 1)) (by simp [utf8Width_length]; omega) $$ [T1 Tk T2]
      · iframe T1 Tk T2
      rw [show List.take b.toNat utf8Width ++ utf8Width[b.toNat]'(by rw [utf8Width_length]; exact b.toNat_lt) :: List.drop (b.toNat + 1) utf8Width = utf8Width by simp]
      by_cases hc0 : b.toNat < 0xC2 ∨ 0xF5 ≤ b.toNat
      · rw [wcls_0 _ (by omega) hc0]
        mstep; mstep; mstep
        rw [show ([0, 1, 2] : List Nat)[(UInt32.ofNat 0 + 4294967294).toNat]?.getD 8 = 8 by decide]
        mctrl_norm; repeat mpay
        have hbad : Utf8.utf8Ok bs = false := by rw [hok, hdrop]; exact ok_bad0 b _ (by omega) hc0
        icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
        mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep [O4] with (simp [hob]; omega)
        mstep; mstep
        mstep [O0]
        mstep
        (try simp only [Post.mloop]); mctrl_norm; repeat mpay
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        isplitr
        · ipureintro; trivial
        iframe Hb Ht
        iapply res927_err n out p len bs hbad _
        iframe O0 O4
      by_cases hc2 : b.toNat < 0xE0
      · rw [wcls_2 _ (by omega) hc2]
        mstep; mstep; mstep
        rw [show ([0, 1, 2] : List Nat)[(UInt32.ofNat 2 + 4294967294).toNat]?.getD 8 = 0 by decide]
        mctrl_norm; repeat mpay
        mstep; mstep; mstep
        rw [ofNat_add1 i (by omega)]
        mstep; mstep; mstep
        rw [ltu_ofNat _ _ (by omega)]
        by_cases h1 : i + 1 < bs.length
        · rw [if_pos (by omega)]
          brt (by decide)
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          ldb (i + 1) x hx
          have hd1 : bs.drop (i + 1) = x :: bs.drop (i + 2) := by rw [List.drop_eq_getElem_cons h1, hx]
          mstep; mstep; mstep; mstep
          rw [t_ncont]
          by_cases hcx : Utf8.cont x
          · rw [if_pos hcx]
            brn rfl
            mstep; mstep; mstep; mstep
            rw [ofNat_add1 (i + 1) (by omega)]
            mstep; mstep
            have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (i + 2)) := by
              rw [hok, hdrop, hd1, ok_two b x _ (by omega) hc2, hcx, Bool.true_and]
            have hZ2 : Z = 100 * cfg.regularOpCost + 100 * (bs.length - (i + 2)) * cfg.regularOpCost := by
              rw [← hZ, show bs.length - (i + 1) = (bs.length - (i + 2)) + 1 by omega, Nat.mul_add, Nat.add_mul]; omega
            mstep; mstep; mstep
            rw [show i + 1 + 1 = i + 2 by omega]
            rejoin
            tail927 (i + 2)
          · rw [if_neg hcx]
            brt (by decide)
            have hbad : Utf8.utf8Ok bs = false := by
              rw [hok, hdrop, hd1, ok_two b x _ (by omega) hc2]; simp [hcx]
            err927
        · rw [if_neg (by omega)]
          brn rfl
          mstep; mstep; mstep; mstep; mstep
          have hbad : Utf8.utf8Ok bs = false := by
            rw [hok, hdrop, List.drop_eq_nil_of_le (by omega)]; exact ok_end b (by omega)
          err927
      by_cases hc3 : b.toNat < 0xF0
      · rw [wcls_3 _ (by omega) hc3]
        mstep; mstep; mstep
        rw [show ([0, 1, 2] : List Nat)[(UInt32.ofNat 3 + 4294967294).toNat]?.getD 8 = 1 by decide]
        mctrl_norm; repeat mpay
        mstep; mstep; mstep
        mstep; mstep; mstep
        rw [ofNat_add1 i (by omega)]
        mstep; mstep; mstep
        rw [ltu_ofNat _ _ (by omega)]
        by_cases h1 : i + 1 < bs.length
        · rw [if_pos (by omega)]
          brt (by decide)
          mstep; mstep; mstep
          ldb (i + 1) x hx
          have hd1 : bs.drop (i + 1) = x :: bs.drop (i + 2) := by rw [List.drop_eq_getElem_cons h1, hx]
          mstep
          mstep; mstep; mstep; mstep
          mstep; mstep; mstep
          have hc3' : 0xE0 ≤ b.toNat := by omega
          by_cases hE0 : b.toNat = 0xE0
          · have hk : ([0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967072).toNat]?.getD 2 = 0 := by
              rw [idx3 b hc3' hc3, if_pos hE0]
            iapply mwpi_br_table_k hk
            isplitr
            · ipureintro; rfl
            clear hk
            mctrl_norm; repeat mpay
            mstep; mstep; mstep; mstep; mstep
            rw [t_e0]
            by_cases hx3 : 0xA0 ≤ x.toNat ∧ x.toNat < 0xC0
            · rw [if_pos hx3]
              brt (by decide)
              have hok3 : Utf8.ok3 b x = true := by simp [Utf8.ok3]; omega
              cont3
            · rw [if_neg hx3]
              brn rfl
              mstep
              have hbad : Utf8.utf8Ok bs = false := by
                rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3]; omega)
              err7
          · by_cases hED : b.toNat = 0xED
            · have hk : ([0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967072).toNat]?.getD 2 = 1 := by
                rw [idx3 b hc3' hc3, if_neg hE0, if_pos hED]
              iapply mwpi_br_table_k hk
              isplitr
              · ipureintro; rfl
              clear hk
              mctrl_norm; repeat mpay
              sgn x
              by_cases hxa : x.toNat < 128
              · rw [if_pos hxa]
                brt (by decide)
                have hbad : Utf8.utf8Ok bs = false := by
                  rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                err7
              · rw [if_neg hxa]
                brn rfl
                mstep; mstep; mstep; mstep; mstep
                rw [t_lt160]
                by_cases hx160 : x.toNat < 160
                · rw [if_pos hx160]
                  brt (by decide)
                  have hok3 : Utf8.ok3 b x = true := by simp [Utf8.ok3, Utf8.cont]; omega
                  cont3
                · rw [if_neg hx160]
                  brn rfl
                  mstep
                  have hbad : Utf8.utf8Ok bs = false := by
                    rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                  err7
            · have hk : ([0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967072).toNat]?.getD 2 = 2 := by
                rw [idx3 b hc3' hc3, if_neg hE0, if_neg hED]
              iapply mwpi_br_table_k hk
              isplitr
              · ipureintro; rfl
              clear hk
              mctrl_norm; repeat mpay
              mstep
              obtain ⟨T31, -, -⟩ : _ ∧ _ ∧ _ := id hT
              mstep; mstep; mstep; mstep; mstep; mstep; mstep
              rw [T31]
              clear T31
              by_cases hmid : 0xE1 ≤ b.toNat ∧ b.toNat ≤ 0xEC
              · rw [if_pos hmid]
                brn rfl
                sgn x
                by_cases hxa : x.toNat < 128
                · rw [if_pos hxa]
                  brt (by decide)
                  have hbad : Utf8.utf8Ok bs = false := by
                    rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                  err7
                · rw [if_neg hxa]
                  brn rfl
                  mstep; mstep; mstep; mstep; mstep
                  rw [t_lt192]
                  by_cases hx192 : x.toNat < 192
                  · rw [if_pos hx192]
                    brt (by decide)
                    have hok3 : Utf8.ok3 b x = true := by simp [Utf8.ok3, Utf8.cont]; omega
                    cont3
                  · rw [if_neg hx192]
                    brn rfl
                    mstep
                    have hbad : Utf8.utf8Ok bs = false := by
                      rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                    err7
              · rw [if_neg hmid]
                brt (by decide)
                mstep; mstep; mstep; mstep; mstep
                rw [t_gt191]
                by_cases hx191 : 191 < x.toNat
                · rw [if_pos hx191]
                  brt (by decide)
                  have hbad : Utf8.utf8Ok bs = false := by
                    rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                  err7
                · rw [if_neg hx191]
                  brn rfl
                  obtain ⟨-, T254, -⟩ : _ ∧ _ ∧ _ := id hT
                  mstep; mstep; mstep; mstep; mstep
                  rw [T254]
                  clear T254
                  rw [if_pos (by omega)]
                  brn rfl
                  sgn x
                  by_cases hxa : x.toNat < 128
                  · rw [if_pos hxa]
                    brt (by decide)
                    have hbad : Utf8.utf8Ok bs = false := by
                      rw [hok, hdrop, hd1]; exact ok_three_bad b x _ hc3' hc3 (by simp [Utf8.ok3, Utf8.cont]; omega)
                    err7
                  · rw [if_neg hxa]
                    brn rfl
                    mstep
                    have hok3 : Utf8.ok3 b x = true := by simp [Utf8.ok3, Utf8.cont]; omega
                    cont3
        · rw [if_neg (by omega)]
          brn rfl
          mstep; mstep; mstep
          have hbad : Utf8.utf8Ok bs = false := by
            rw [hok, hdrop, List.drop_eq_nil_of_le (by omega)]; exact ok_end b (by omega)
          err927
      · have hc4 : b.toNat < 0xF5 := by omega
        have hc4' : 0xF0 ≤ b.toNat := by omega
        rw [wcls_4 _ hc4' hc4]
        mstep; mstep; mstep
        rw [show ([0, 1, 2] : List Nat)[(UInt32.ofNat 4 + 4294967294).toNat]?.getD 8 = 2 by decide]
        mctrl_norm; repeat mpay
        mstep; mstep; mstep
        mstep; mstep; mstep
        rw [ofNat_add1 i (by omega)]
        mstep; mstep; mstep
        rw [ltu_ofNat _ _ (by omega)]
        by_cases h1 : i + 1 < bs.length
        · rw [if_pos (by omega)]
          brt (by decide)
          mstep; mstep; mstep
          ldb (i + 1) x hx
          have hd1 : bs.drop (i + 1) = x :: bs.drop (i + 2) := by rw [List.drop_eq_getElem_cons h1, hx]
          mstep
          mstep; mstep; mstep; mstep
          mstep; mstep; mstep
          by_cases hF0 : b.toNat = 0xF0
          · have hk : ([0, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967056).toNat]?.getD 2 = 0 := by
              rw [idx4 b hc4' hc4, if_pos hF0]
            iapply mwpi_br_table_k hk
            isplitr
            · ipureintro; rfl
            clear hk
            mctrl_norm; repeat mpay
            mstep; mstep; mstep; mstep; mstep; mstep; mstep
            rw [t_f0]
            by_cases hx4 : 0x90 ≤ x.toNat ∧ x.toNat < 0xC0
            · rw [if_pos hx4]
              brn rfl
              mstep
              have hok4 : Utf8.ok4 b x = true := by simp [Utf8.ok4, Utf8.cont]; omega
              cont4
            · rw [if_neg hx4]
              brt (by decide)
              have hbad : Utf8.utf8Ok bs = false := by
                rw [hok, hdrop, hd1]; exact ok_four_bad b x _ hc4' hc4 (by simp [Utf8.ok4, Utf8.cont]; omega)
              err7
          by_cases hF4 : b.toNat = 0xF4
          · have hk : ([0, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967056).toNat]?.getD 2 = 1 := by
              rw [idx4 b hc4' hc4, if_neg hF0, if_pos hF4]
            iapply mwpi_br_table_k hk
            isplitr
            · ipureintro; rfl
            clear hk
            mctrl_norm; repeat mpay
            sgn x
            by_cases hxa : x.toNat < 128
            · rw [if_pos hxa]
              brt (by decide)
              have hbad : Utf8.utf8Ok bs = false := by
                rw [hok, hdrop, hd1]; exact ok_four_bad b x _ hc4' hc4 (by simp [Utf8.ok4, Utf8.cont]; omega)
              err7
            · rw [if_neg hxa]
              brn rfl
              mstep; mstep; mstep; mstep; mstep
              rw [t_ge144]
              by_cases hx144 : 144 ≤ x.toNat
              · rw [if_pos hx144]
                brt (by decide)
                have hbad : Utf8.utf8Ok bs = false := by
                  rw [hok, hdrop, hd1]; exact ok_four_bad b x _ hc4' hc4 (by simp [Utf8.ok4, Utf8.cont]; omega)
                err7
              · rw [if_neg hx144]
                brn rfl
                mstep
                have hok4 : Utf8.ok4 b x = true := by simp [Utf8.ok4, Utf8.cont]; omega
                cont4
          · have hk : ([0, 2, 2, 2, 1] : List Nat)[(b.toUInt32 + 4294967056).toNat]?.getD 2 = 2 := by
              rw [idx4 b hc4' hc4, if_neg hF0, if_neg hF4]
            iapply mwpi_br_table_k hk
            isplitr
            · ipureintro; rfl
            clear hk
            mctrl_norm; repeat mpay
            mstep; mstep; mstep; mstep; mstep
            rw [t_gt191]
            by_cases hx191 : 191 < x.toNat
            · rw [if_pos hx191]
              brt (by decide)
              have hbad : Utf8.utf8Ok bs = false := by
                rw [hok, hdrop, hd1]; exact ok_four_bad b x _ hc4' hc4 (by simp [Utf8.ok4, Utf8.cont]; omega)
              err7
            · rw [if_neg hx191]
              brn rfl
              obtain ⟨-, -, T15⟩ : _ ∧ _ ∧ _ := id hT
              mstep; mstep; mstep; mstep; mstep; mstep; mstep
              rw [T15]
              clear T15
              rw [if_pos (by omega)]
              brn rfl
              sgn x
              by_cases hxa : x.toNat < 128
              · rw [if_pos hxa]
                brt (by decide)
                have hbad : Utf8.utf8Ok bs = false := by
                  rw [hok, hdrop, hd1]; exact ok_four_bad b x _ hc4' hc4 (by simp [Utf8.ok4, Utf8.cont]; omega)
                err7
              · rw [if_neg hxa]
                brn rfl
                mstep
                have hok4 : Utf8.ok4 b x = true := by simp [Utf8.ok4, Utf8.cont]; omega
                cont4
        · rw [if_neg (by omega)]
          brn rfl
          mstep; mstep; mstep
          have hbad : Utf8.utf8Ok bs = false := by
            rw [hok, hdrop, List.drop_eq_nil_of_le (by omega)]; exact ok_end b (by omega)
          err927
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ 0 _ _ _ _ _ (by omega) (by simp)
  iframe Hb Ho
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro
  rw [Nat.sub_zero, hbs, ← hM]; omega


end L927

end WNear.Binary.FromUtf8Gen
