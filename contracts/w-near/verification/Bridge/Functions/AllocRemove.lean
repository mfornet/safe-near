import Bridge.Functions.AllocNewCell

/-!
# `Neighbors::remove` (575), in the metered logic

```wat
(func 575 (param c) (local w n)
  block                                   ;; the next neighbour's `prev` := c.prev
    c.word0 → w;  w & !3 → n;  br_if n == 0
    (if w & 2 then 0 else n) → n;  br_if n == 0
    n.word1 := (n.word1 & 3) | (c.word1 & !3)
  end
  block                                   ;; the previous neighbour's `next` := c.next
    c.word1 → w;  w & !3 → p;  br_if p == 0
    p.word0 := (p.word0 & 3) | (c.word0 & !3);  c.word1 → w
  end
  c.word1 := w & 3;  c.word0 := c.word0 & 3)
```

`f575_spec` takes the two header words of `c` and, when the code touches
them, the `prev` word of the next neighbour (`nextOf w0 ≠ 0`) and the `next`
word of the previous one (`w1 & !3 ≠ 0`), as points-to under `ptsIf`. The
cost is bounded by `61 regular_op_cost`s (the longest path, both neighbours
present; activation excluded).

The file also has the `u32` bit facts the allocator's proofs need
(`band_mask4`, `bor_low`, …), each reducing a mask to `/`, `%` and `+`.
-/

namespace WNear.Binary.AllocRemove

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.AllocLeaves WNear.Binary.AllocNewCell

/-! ## Bit masks as arithmetic -/

theorem nat_and_mask4 (n : Nat) (h : n < 2 ^ 32) : n &&& 4294967292 = n / 4 * 4 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, show n / 4 * 4 = (n >>> 2) <<< 2 by simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow],
    show (4294967292 : Nat) = (2 ^ 30 - 1) <<< 2 by decide, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : 2 ≤ i
  · by_cases h2 : i < 32
    · simp [hi, show i - 2 < 30 by omega, show 2 + (i - 2) = i by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this, hi, show ¬ (i - 2 < 30) by omega, show 2 + (i - 2) = i by omega]
  · simp [hi]

theorem nat_and_mask2 (n : Nat) (h : n < 2 ^ 32) : n &&& 4294967294 = n / 2 * 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, show n / 2 * 2 = (n >>> 1) <<< 1 by simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow],
    show (4294967294 : Nat) = (2 ^ 31 - 1) <<< 1 by decide, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : 1 ≤ i
  · by_cases h2 : i < 32
    · simp [hi, show i - 1 < 31 by omega, show 1 + (i - 1) = i by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this, hi, show ¬ (i - 1 < 31) by omega, show 1 + (i - 1) = i by omega]
  · simp [hi]

theorem nat_and_low (n m : Nat) (hm : m < 4) : n &&& m = n % 4 &&& m := by
  have e1 : (n &&& m) % 2 ^ 2 = n % 2 ^ 2 &&& m % 2 ^ 2 := Nat.and_mod_two_pow
  have e2 : (n &&& m) < 2 ^ 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  rw [Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt (a := m) (by omega)] at e1
  exact e1

theorem nat_or_low (n m : Nat) (hm : m < 4) : n ||| m = n / 4 * 4 + (n % 4 ||| m) := by
  have e1 : (n ||| m) % 2 ^ 2 = n % 2 ^ 2 ||| m % 2 ^ 2 := Nat.or_mod_two_pow
  have e2 : (n ||| m) >>> 2 = n >>> 2 ||| m >>> 2 := Nat.shiftRight_or_distrib
  rw [Nat.mod_eq_of_lt (a := m) (by omega)] at e1
  simp only [Nat.shiftRight_eq_div_pow] at e2
  rw [Nat.div_eq_of_lt (a := m) (by omega), Nat.or_zero] at e2
  have := Nat.div_add_mod (n ||| m) 4
  simp only [show (2 : Nat) ^ 2 = 4 from rfl] at e1 e2
  omega

theorem nat_or_disj (a b : Nat) (ha : a < 4) (hb : b % 4 = 0) : a ||| b = a + b := by
  rw [Nat.or_comm, nat_or_low b a ha]
  have : b % 4 ||| a = a := by rw [hb, Nat.zero_or]
  omega

theorem low4_cases (r : Nat) (h : r < 4) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega

theorem u32_and_mask4 (x : UInt32) : (x &&& 4294967292).toNat = x.toNat / 4 * 4 := by
  rw [UInt32.toNat_and]; exact nat_and_mask4 _ x.toNat_lt

theorem u32_and_mask2 (x : UInt32) : (x &&& 4294967294).toNat = x.toNat / 2 * 2 := by
  rw [UInt32.toNat_and]; exact nat_and_mask2 _ x.toNat_lt

theorem u32_and_3 (x : UInt32) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 2

theorem u32_and_1 (x : UInt32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem u32_and_2 (x : UInt32) : (x &&& 2).toNat = x.toNat % 4 / 2 * 2 := by
  rw [UInt32.toNat_and, show (2 : UInt32).toNat = 2 from rfl, nat_and_low _ _ (by decide)]
  rcases low4_cases _ (Nat.mod_lt x.toNat (by decide : 4 > 0)) with h | h | h | h <;> rw [h] <;> rfl

theorem u32_or_2 (x : UInt32) : (x ||| 2).toNat = x.toNat / 4 * 4 + x.toNat % 2 + 2 := by
  rw [UInt32.toNat_or, show (2 : UInt32).toNat = 2 from rfl, nat_or_low _ _ (by decide)]
  rcases low4_cases _ (Nat.mod_lt x.toNat (by decide : 4 > 0)) with h | h | h | h <;> rw [h] <;> simp only [Nat.reduceOr] <;> omega

theorem u32_or_disj (a b : UInt32) (ha : a.toNat < 4) (hb : b.toNat % 4 = 0) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_or]; exact nat_or_disj _ _ ha hb

/-! ## The spec -/

set_option hygiene false in
/-- Step as far as possible, with the resources `H0`, `H1`, `HN`, `HP`. -/
macro "mrun" : tactic =>
  `(tactic| repeat (first | mstep | mstep [H0] | mstep [H1] | mstep [HN] | mstep [HP]))

set_option hygiene false in
/-- `select`, its condition decided by the hypotheses. -/
macro "mselect" : tactic =>
  `(tactic| (iapply mwpi_cons; iapply mwpi_select_ite; isplitl [Hc]; iexact Hc; isplitr; ipureintro; exact ⟨rfl, by omega⟩; inext; iintro Hc; simp only [*, ↓reduceIte]; mctrl_norm))

/-- The next neighbour `remove` sees in a header word 0: `w0 & !3`, or none
(0) when `NEXT_CELL_IS_INVALID` is set. -/
def nextOf (w0 : UInt32) : UInt32 := if w0 &&& 2 = 0 then w0 &&& 4294967292 else 0

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A word owned only when `b` holds. -/
def ptsIf (b : Prop) [Decidable b] (n a : Nat) (w : UInt32) : IProp GF :=
  if b then iprop(n ↦[wms][ a ] bytes32 w) else iprop(emp)

set_option maxHeartbeats 4000000 in
/-- `Neighbors::remove` (575) on the cell `c` with header words `w0`, `w1`:
the next neighbour's `prev` (its word 1, `v1`) gets `c.prev`, the previous
neighbour's `next` (its word 0, `v0`) gets `c.next`, each keeping its own
two flag bits, and `c`'s words keep only their flag bits. -/
theorem f575_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (c w0 w1 v0 v1 : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f575 Cg
        (fun args => iprop(⌜args = [.i32 c]⌝ ∗ n ↦[wms][ c.toNat ] bytes32 w0 ∗
          n ↦[wms][ c.toNat + 4 ] bytes32 w1 ∗
          ptsIf (nextOf w0 ≠ 0) n ((nextOf w0).toNat + 4) v1 ∗
          ptsIf ((w1 &&& 4294967292) ≠ 0) n (w1 &&& 4294967292).toNat v0))
        (fun _ => 61 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[wms][ c.toNat ] bytes32 (w0 &&& 3) ∗
          n ↦[wms][ c.toNat + 4 ] bytes32 (w1 &&& 3) ∗
          ptsIf (nextOf w0 ≠ 0) n ((nextOf w0).toNat + 4) ((v1 &&& 3) ||| (w1 &&& 4294967292)) ∗
          ptsIf ((w1 &&& 4294967292) ≠ 0) n (w1 &&& 4294967292).toNat
            ((v0 &&& 3) ||| (w0 &&& 4294967292)))) := by
  have hcases : (w0 &&& 4294967292 = 0 ∧ nextOf w0 = 0) ∨
      (w0 &&& 4294967292 ≠ 0 ∧ w0 &&& 2 ≠ 0 ∧ nextOf w0 = 0) ∨
      (w0 &&& 4294967292 ≠ 0 ∧ w0 &&& 2 = 0 ∧ nextOf w0 = w0 &&& 4294967292) := by
    unfold nextOf
    by_cases hA : w0 &&& 4294967292 = 0 <;> by_cases hT : w0 &&& 2 = 0 <;> simp_all
  by_cases hP : w1 &&& 4294967292 = 0
  all_goals rcases hcases with ⟨hA, hN⟩ | ⟨hA, hT, hN⟩ | ⟨hA, hT, hN⟩
  all_goals
    simp only [hN, hP, ne_eq, not_true_eq_false, not_false_eq_true, ptsIf, ↓reduceIte, hA]
    iapply MFunSpec_intro
    imodintro
    iintro %args %R ⟨%hargs, H0, H1, HN, HP⟩ Hc
    subst hargs
    simp only [f575]
    mrun
    try mselect
    mrun
    mcredits R
    try simp only [hP, hA]
    iframe Hc H0 H1 HN HP

end Spec

end WNear.Binary.AllocRemove
