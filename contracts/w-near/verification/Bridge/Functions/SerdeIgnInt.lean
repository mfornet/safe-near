import Bridge.Functions.SerdeIgnNum

/-!
# `ignore_integer` (83) on accepted numbers (M6)

`ignore_value` (81) skips a number with `ignore_integer` (83), at its first digit (after eating a
`-` itself):

```wat
;; 83 ignore_integer(de) -> i32        (a 16-byte frame for an error code)
b := next_char_or_null(de)              ;; 88
b = '0' → peek_or_null (329) a digit → InvalidNumber (322)
b ∉ '1'..'9' → InvalidNumber (325)
else loop: peek_or_null (329) a digit → eat_char (333)
peek_or_null (329):  'e' | 'E' → ignore_exponent (87);  '.' → ignore_decimal (86);  else 0
```

* `intR_split`, `afterInt_cases`: the model's `intR` read as 83 reads it, the integer part up to
  `intEnd bs i`, then a fraction, an exponent or nothing.
* `f83_acc`: at a digit, a number `SerdeNumModel.intR` reads: `0`, the reader at its end, at
  `cost83 bs i rest`: `197` for the integer part's fixed cost, `127` per digit, then 86's or 87's
  cost (and the call's) when a `.` or an `e`/`E` follows (`tail83`). The cost depends on the path: a
  flat bound with 86's fixed part would make every one-digit number pay for a fraction.
-/

namespace WNear.Binary.SerdeIgnInt

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.SerdeRead (rd optByte byteOrNull)
open WNear.Binary.SerdeIgnNum (numCode bon_ok bon_gt9 digits_at cost86 cost87 f86_acc f87_acc f88_spec)
open NearInterface.Json (isDigit)
open WNear.SerdeNumModel

/-- Where the integer part of a number at `i` ends: past its first digit and the digits after it. -/
def intEnd (bs : List UInt8) (i : Nat) : Nat := i + 1 + ((bs.drop (i + 1)).takeWhile isDigit).length

/-- What follows the integer part: 86 at a `.`, 87 at an `e`/`E`, with the call's own cost. -/
def tail83 (bs : List UInt8) (j : Nat) (rest : List UInt8) : Nat :=
  if bs[j]? = some 0x2E then 20 + cost86 (bs.length - rest.length - j)
  else if bs[j]? = some 0x65 ∨ bs[j]? = some 0x45 then 20 + cost87 (bs.length - rest.length - j) else 0

/-- 83's cost at `i`, the number ending at `rest`. -/
def cost83 (bs : List UInt8) (i : Nat) (rest : List UInt8) : Nat :=
  197 + 127 * (intEnd bs i - i) + tail83 bs (intEnd bs i) rest

/-! ## The model, as 83 reads it -/

theorem drop_cons {bs : List UInt8} {i : Nat} {b : UInt8} (hi : i < bs.length) (hb : bs[i]? = some b) :
    bs.drop i = b :: bs.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi]
  rw [List.getElem?_eq_getElem hi] at hb
  rw [Option.some.inj hb]

/-- `intR` at `i`: a digit, then `afterInt` after the integer part; one digit when it is `0`. -/
theorem intR_split {bs rest : List UInt8} {i : Nat} {d0 : UInt8} (hi : i < bs.length) (hd0 : bs[i]? = some d0)
    (hx : intR (bs.drop i) = some rest) :
    isDigit d0 = true ∧ afterInt (bs.drop (intEnd bs i)) = some rest ∧ (d0 = 0x30 → intEnd bs i = i + 1) := by
  rw [drop_cons hi hd0] at hx
  simp only [intR] at hx
  obtain ⟨-, -, -, hdrop⟩ := digits_at bs (i + 1) (by omega)
  by_cases h0 : d0 = 0x30
  · subst h0
    simp only [ite_true] at hx
    have hne : intEnd bs i = i + 1 := by
      unfold intEnd
      revert hx
      cases bs.drop (i + 1) with
      | nil => simp
      | cons e t =>
        intro hx
        simp only at hx
        by_cases he : isDigit e = true
        · simp [he] at hx
        · simp [List.takeWhile_cons, he]
    refine ⟨by decide, ?_, fun _ => hne⟩
    rw [hne]
    revert hx
    cases bs.drop (i + 1) with
    | nil => intro hx; simp only [Option.some.injEq] at hx; subst hx; rfl
    | cons e t =>
      intro hx
      simp only at hx
      by_cases he : isDigit e = true
      · simp [he] at hx
      · simpa [he] using hx
  · rw [if_neg h0] at hx
    by_cases hd : isDigit d0 = true
    · rw [if_pos hd] at hx
      refine ⟨hd, ?_, fun h => absurd h h0⟩
      unfold intEnd
      rw [hdrop]; exact hx
    · rw [if_neg hd] at hx; simp at hx

/-- After the integer part: a fraction, an exponent, or the number ends. -/
theorem afterInt_cases {bs rest : List UInt8} {j : Nat} (h : afterInt (bs.drop j) = some rest) :
    (j < bs.length ∧ bs[j]? = some 0x2E ∧ fracR (bs.drop (j + 1)) = some rest) ∨
    (j < bs.length ∧ (bs[j]? = some 0x65 ∨ bs[j]? = some 0x45) ∧ expR (bs.drop (j + 1)) = some rest) ∨
    (bs[j]? ≠ some 0x2E ∧ bs[j]? ≠ some 0x65 ∧ bs[j]? ≠ some 0x45 ∧ rest = bs.drop j) := by
  by_cases hjl : j < bs.length
  · obtain ⟨b, hb⟩ : ∃ b, bs[j]? = some b := ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [drop_cons hjl hb] at h
    by_cases hdot : b = 0x2E
    · subst hdot
      exact Or.inl ⟨hjl, hb, h⟩
    · have ha : afterInt (b :: bs.drop (j + 1)) = afterExp (b :: bs.drop (j + 1)) := by
        unfold afterInt
        split
        · rename_i x heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hdot
        · rfl
      rw [ha] at h
      simp only [afterExp] at h
      by_cases he : b = 0x65 ∨ b = 0x45
      · rw [if_pos he] at h
        refine Or.inr (Or.inl ⟨hjl, ?_, h⟩)
        rcases he with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
      · rw [if_neg he] at h
        simp only [Option.some.injEq] at h
        refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)
        · rw [hb]; simpa using hdot
        · rw [hb]; intro e; exact he (Or.inl (Option.some.inj e))
        · rw [hb]; intro e; exact he (Or.inr (Option.some.inj e))
        · rw [← h, drop_cons hjl hb]
  · rw [List.drop_eq_nil_of_le (by omega)] at h
    simp only [afterInt, afterExp, Option.some.injEq] at h
    have hn : bs[j]? = none := List.getElem?_eq_none (by omega)
    refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)
    · rw [hn]; simp
    · rw [hn]; simp
    · rw [hn]; simp
    · rw [← h, List.drop_eq_nil_of_le (by omega)]

/-! ## The byte tests -/

/-- 83's `0` test on the byte 88 read. -/
theorem bz_eq (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq ((byteOrNull o >>> (8 % 64)).toUInt32 &&& 255) 48) =
      if o = some 0x30 then 1 else 0 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- 83's `1..9` test on the byte 88 read. -/
theorem bnz (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((byteOrNull o >>> (8 % 64)).toUInt32 + 4294967247 &&& 255) 8) =
      if isDigit (o.getD 0) && o.getD 0 != 0x30 then 0 else 1 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The tail's `e` test. -/
theorem be_eq (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq ((byteOrNull o).toUInt32 >>> (8 % 32) &&& 255) 101) =
      if o = some 0x65 then 1 else 0 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The tail's `E` test. -/
theorem bE_eq (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq ((byteOrNull o).toUInt32 >>> (8 % 32) &&& 255) 69) =
      if o = some 0x45 then 1 else 0 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The tail's `.` test. -/
theorem bdot_ne (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.ne ((byteOrNull o).toUInt32 >>> (8 % 32) &&& 255) 46) =
      if o = some 0x2E then 0 else 1 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem ne0 {c : UInt32} (h : c = 1) : c ≠ 0 := by rw [h]; decide

section L83

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 83's frame. -/
def fr83 (inst : Nat) (mi : ModuleInst) (de l1 : UInt32) (l2 : UInt64) (l3 l4 : UInt32) : Frame :=
  ⟨#[.i32 de, .i32 l1, .i64 l2, .i32 l3, .i32 l4], inst, mi⟩

/-- 83's digit loop: the reader at `k ≤ e`, `D` per digit left. -/
def inv83 (n inst : Nat) (mi : ModuleInst) (Cg c₀ D E R : Nat) (de l1 ptr : UInt32) (l3 : UInt32) (bs : List UInt8)
    (s e : Nat) (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l2 : UInt64), ⌜X = [] ∧ g = fr83 inst mi de l1 l2 l3 0 ∧ s ≤ k ∧ k ≤ e⌝ ∗
    credits Cg (D * (e - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs k ∗ P)

theorem inv83_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ D E R : Nat) (de l1 ptr l3 : UInt32) (bs : List UInt8)
    (s e : Nat) (P : IProp GF) (k : Nat) (l2 : UInt64) (h1 : s ≤ k) (h2 : k ≤ e) :
    credits Cg (D * (e - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs k ∗ P ⊢
      inv83 n inst mi Cg c₀ D E R de l1 ptr l3 bs s e P [] ⟨#[.i32 de, .i32 l1, .i64 l2, .i32 l3, .i32 0], inst, mi⟩ := by
  iintro ⟨Hc, Hrd, HP⟩
  iunfold inv83
  iexists k
  iexists l2
  iframe Hc Hrd HP
  ipureintro; exact ⟨rfl, rfl, h1, h2⟩

set_option hygiene false in
/-- 83 after its integer part, at `j` (the reader there, `Hrd`): peek, then 87, 86 or `0`. -/
local macro "tail83m" : tactic => `(tactic| (
  mstep; mstep
  mcall (SerdeRead.f329_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (hm.funcs 332 (by decide))
    (by omega) Cg de ptr bs j (by omega) hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (30 * cfg.regularOpCost + (XT + R))
  generalize hobj : byteOrNull bs[j]? = obj
  have hokj : Numeric.bool (obj &&& 1 == 0) = 1 := by rw [← hobj]; exact bon_ok _
  mstep; mstep; mstep; mstep
  mstep_taken with exact ne0 hokj
  mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rcases afterInt_cases hai with ⟨hjl, hbj, hfr⟩ | ⟨hjl, hbj, hex⟩ | ⟨hb1, hb2, hb3, hrest⟩
  · -- `.`: 86
    have he1 : Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 101) = 0 := by
      rw [← hobj, be_eq, hbj]; decide
    have he2 : Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 69) = 0 := by
      rw [← hobj, bE_eq, hbj]; decide
    have he3 : Numeric.bool (Numeric.irelop32 IRelOp.ne (obj.toUInt32 >>> (8 % 32) &&& 255) 46) = 0 := by
      rw [← hobj, bdot_ne, hbj]; decide
    mstep_not_taken with exact he1
    mstep; mstep; mstep
    mstep_not_taken with exact he2
    mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with exact he3
    mstep
    have s86 := f86_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
      (sp - 16) de ptr bs rest j hlen hptr hde hjl hfr
    rw [← hXT, ← hT]
    unfold tail83
    rw [if_pos hbj]
    generalize hM : 129 * (bs.length - rest.length - j) * cfg.regularOpCost = M
    rw [show cost86 (bs.length - rest.length - j) * cfg.regularOpCost = 465 * cfg.regularOpCost + M by
      unfold cost86; rw [← hM]; simp only [Nat.add_mul]] at s86
    rw [show (20 + cost86 (bs.length - rest.length - j)) * cfg.regularOpCost + R =
      485 * cfg.regularOpCost + (M + R) by unfold cost86; rw [← hM]; simp only [Nat.add_mul]; omega]
    ihave #S86 := s86 $$ Hk
    clear s86
    mcall S86 using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mstep; mstep
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep; mstep; mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hg Hrd
    ipureintro; simp [htype]
  · -- `e` or `E`: 87
    have hnd : bs[j]? ≠ some 0x2E := by rcases hbj with h | h <;> rw [h] <;> decide
    have he3 : Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 101) = 1 ∨
        (Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 101) = 0 ∧
          Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 69) = 1) := by
      rw [← hobj, be_eq, bE_eq]; rcases hbj with h | h <;> rw [h] <;> decide
    have s87 := f87_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
      (sp - 16) de ptr bs rest j hlen hptr hde hjl hex
    rw [← hXT, ← hT]
    unfold tail83
    rw [if_neg hnd, if_pos hbj]
    generalize hM : 127 * (bs.length - rest.length - j) * cfg.regularOpCost = M
    rw [show cost87 (bs.length - rest.length - j) * cfg.regularOpCost = 300 * cfg.regularOpCost + M by
      unfold cost87; rw [← hM]; simp only [Nat.add_mul]] at s87
    rw [show (20 + cost87 (bs.length - rest.length - j)) * cfg.regularOpCost + R =
      320 * cfg.regularOpCost + (M + R) by unfold cost87; rw [← hM]; simp only [Nat.add_mul]; omega]
    ihave #S87 := s87 $$ Hk
    clear s87
    rcases he3 with he3 | ⟨he3, he4⟩
    · mstep_taken with exact ne0 he3
      mstep
      mcall S87 using [Hg Hrd]
      · iframe Hg Hrd
      icases HQ with ⟨%hrs, Hg, Hrd⟩
      subst hrs
      mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 16 + 16 = sp by simp]
      repeat mstep
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg Hrd
      ipureintro; simp [htype]
    · mstep_not_taken with exact he3
      mstep; mstep; mstep
      mstep_taken with exact ne0 he4
      mstep
      mcall S87 using [Hg Hrd]
      · iframe Hg Hrd
      icases HQ with ⟨%hrs, Hg, Hrd⟩
      subst hrs
      mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 16 + 16 = sp by simp]
      repeat mstep
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg Hrd
      ipureintro; simp [htype]
  · -- the number ends: 0
    have he1 : Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 101) = 0 := by
      rw [← hobj, be_eq, if_neg hb2]
    have he2 : Numeric.bool (Numeric.irelop32 IRelOp.eq (obj.toUInt32 >>> (8 % 32) &&& 255) 69) = 0 := by
      rw [← hobj, bE_eq, if_neg hb3]
    have he3 : Numeric.bool (Numeric.irelop32 IRelOp.ne (obj.toUInt32 >>> (8 % 32) &&& 255) 46) = 1 := by
      rw [← hobj, bdot_ne, if_neg hb1]
    have hT0 : T = 0 := by
      rw [← hT]; unfold tail83
      rw [if_neg hb1, if_neg (by rintro (h | h) <;> contradiction)]
    have hpos : bs.length - rest.length = j := by rw [hrest]; simp; omega
    mstep_not_taken with exact he1
    mstep; mstep; mstep
    mstep_not_taken with exact he2
    mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact ne0 he3
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep; mstep; mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hg
    isplitr
    · ipureintro; simp [htype]
    rw [hpos]
    iexact Hrd))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`ignore_integer(de)`** (83) at a digit: a number `intR` reads, `0`, the reader at its end. -/
theorem f83_acc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : Interface.IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs rest : List UInt8) (i : Nat)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hi : i < bs.length) (hx : intR (bs.drop i) = some rest) :
    numCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f83 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i))
        (fun _ => cost83 bs i rest * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs (bs.length - rest.length))) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold numCode at Hk'
  icases Hk' with ⟨#F324, #F332, #F333, #F329, #F88, #F87, #F86, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha333 := hm.funcs 333 (by decide)
  have ha329 := hm.funcs 329 (by decide)
  have ha88 := hm.funcs 88 (by decide)
  have ha86 := hm.funcs 86 (by decide)
  have ha87 := hm.funcs 87 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  obtain ⟨d0, hd0⟩ : ∃ d0, bs[i]? = some d0 := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨hdd, hai, hz⟩ := intR_split hi hd0 hx
  obtain ⟨hjn, hdig, hstop, -⟩ := digits_at bs (i + 1) (by omega)
  have hjE : intEnd bs i = i + 1 + ((bs.drop (i + 1)).takeWhile isDigit).length := rfl
  generalize hnd : ((bs.drop (i + 1)).takeWhile isDigit).length = nd at hjn hdig hstop hjE
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hrd⟩
  subst hargs
  simp only [f83, cost83]
  generalize hj : intEnd bs i = j at hai hz hjE ⊢
  generalize hT : tail83 bs j rest = T
  rw [show (197 + 127 * (j - i) + T) * cfg.regularOpCost + R =
    324 * cfg.regularOpCost + (127 * (j - (i + 1)) * cfg.regularOpCost + (T * cfg.regularOpCost + R)) by
      rw [show j - i = (j - (i + 1)) + 1 by omega]; simp only [Nat.add_mul, Nat.mul_add]; omega]
  generalize hXT : T * cfg.regularOpCost = XT
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall (f88_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 324) (hm.funcs 324 (by decide))
    (by omega) Cg de ptr bs i hi.le hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hd0, show min (i + 1) bs.length = i + 1 by omega]
  have hzv := bz_eq (some d0)
  have hnzv := bnz (some d0)
  generalize hob0 : byteOrNull (some d0) = ob0 at hzv hnzv ⊢
  have hok0 : Numeric.bool (ob0 &&& 1 == 0) = 1 := by rw [← hob0]; exact bon_ok _
  mstep; mstep; mstep; mstep
  mstep_taken with exact ne0 hok0
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  by_cases h0 : d0 = 0x30
  · -- `0`: one peek, which must not be a digit, then the tail at `i + 1`
    have hj1 : j = i + 1 := hz h0
    subst hj1
    have hnd0 : nd = 0 := by omega
    subst hnd0
    rw [if_pos (by rw [h0])] at hzv
    mstep_taken with exact ne0 hzv
    mcredits (216 * cfg.regularOpCost + (XT + R))
    mstep; mstep
    mcall (SerdeRead.f329_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (hm.funcs 332 (by decide))
      (by omega) Cg de ptr bs (i + 1) (by omega) hlen hptr hde) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    generalize hob1 : byteOrNull bs[i + 1]? = ob1
    have hok1 : Numeric.bool (ob1 &&& 1 == 0) = 1 := by rw [← hob1]; exact bon_ok _
    have hg1 : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((ob1.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 1 := by
      rw [← hob1, bon_gt9]; simp only [Nat.add_zero] at hstop; simp [hstop]
    mstep; mstep; mstep; mstep
    mstep_taken with exact ne0 hok1
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact ne0 hg1
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    generalize hjj : i + 1 = j at hai hT ⊢
    tail83m
  · -- `1..9`: the digit loop, then the tail at `j`
    rw [if_neg (fun e => h0 (Option.some.inj e))] at hzv
    have hnzv' : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((ob0 >>> (8 % 64)).toUInt32 + 4294967247 &&& 255) 8) = 0 := by
      rw [hnzv]; simp [hdd, h0]
    mstep_not_taken with exact hzv
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with exact hnzv'
    mcredits (cfg.regularOpCost + (127 * (j - (i + 1)) * cfg.regularOpCost + 207 * cfg.regularOpCost + (XT + R)))
    iapply mwpi_cons
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 127 * (j - (i + 1)) * cfg.regularOpCost + 207 * cfg.regularOpCost + (XT + R))
      (I := inv83 n inst mi Cg cfg.regularOpCost 127 207 (XT + R) de (sp - 16) ptr (ob0 >>> (8 % 64)).toUInt32 bs
        (i + 1) j iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv83 at HI
      icases HI with ⟨%k, %l2, %⟨hX, hfr, hk1, hk2⟩, Hc, Hrd, Hg⟩
      subst hX
      rw [hfr]
      simp only [fr83]
      clear hfr
      generalize hZ0 : 127 * (j - k) * cfg.regularOpCost = Z0
      mstep; mstep
      mcall (SerdeRead.f329_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (hm.funcs 332 (by decide))
        (by omega) Cg de ptr bs k (by omega) hlen hptr hde) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      mcredits (127 * cfg.regularOpCost + (Z0 + (XT + R)))
      rw [← hZ0]
      generalize hobk : byteOrNull bs[k]? = obk
      have hokk : Numeric.bool (obk &&& 1 == 0) = 1 := by rw [← hobk]; exact bon_ok _
      mstep; mstep; mstep; mstep
      mstep_taken with exact ne0 hokk
      by_cases hke : k < j
      · obtain ⟨xk, hxk, hdk⟩ := hdig k (by omega) (by omega)
        rw [hxk] at hobk
        have hgk : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((obk.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 0 := by
          rw [← hobk, bon_gt9]; simp [hdk]
        rw [show 127 * (j - k) * cfg.regularOpCost =
          127 * cfg.regularOpCost + 127 * (j - (k + 1)) * cfg.regularOpCost by
            rw [show j - k = (j - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
        generalize hZ : 127 * (j - (k + 1)) * cfg.regularOpCost = Z
        clear hobk
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep_not_taken with exact hgk
        mstep
        mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs k (by omega) hlen hde)
          using [Hrd]
        · iframe Hrd
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        mstep
        simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iapply inv83_intro n inst mi Cg cfg.regularOpCost 127 207 (XT + R) de (sp - 16) ptr _ bs (i + 1) j _ (k + 1) _
          (by omega) (by omega)
        iframe Hrd Hg
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      · have hk : k = j := by omega
        subst hk
        have hgk : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((obk.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 1 := by
          rw [← hobk, bon_gt9, hjE]; simp [hstop]
        rw [show 127 * (k - k) * cfg.regularOpCost = 0 by simp, Nat.zero_add]
        clear hobk
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep_taken with exact ne0 hgk
        (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
        generalize hjj : k = j at hai hT ⊢
        tail83m
    · iframe Hc
      inext
      iintro Hc
      iapply inv83_intro n inst mi Cg cfg.regularOpCost 127 207 (XT + R) de (sp - 16) ptr _ bs (i + 1) j _ (i + 1) _
        (by omega) (by omega)
      iframe Hrd Hg
      iexact Hc

end L83

end WNear.Binary.SerdeIgnInt
