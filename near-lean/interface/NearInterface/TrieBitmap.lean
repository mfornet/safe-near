import NearInterface.TrieBranch
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Bitmap correctness for canonical branch groups

Each digit is processed once, in ascending order. The mask is a sum of
distinct powers of two, so addition introduces no carries into other bits.
The generic proofs do not enumerate the possible u16 bitmaps.
-/
namespace Near.TrieBitmap
open TrieAccounting TrieBranch

/-- Mask of active digits in the processed prefix `[0,n)`. -/
def maskOf (active : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).map fun digit => if active digit then 2 ^ digit else 0).sum

theorem maskOf_zero (active : Nat → Bool) : maskOf active 0 = 0 := rfl

theorem maskOf_succ (active : Nat → Bool) (n : Nat) :
    maskOf active (n + 1) = maskOf active n + if active n then 2 ^ n else 0 := by
  simp [maskOf, List.range_succ]

/-- No processed prefix fills its next bit. -/
theorem maskOf_lt (active : Nat → Bool) (n : Nat) : maskOf active n < 2 ^ n := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    rw [maskOf_succ]
    cases hp : active n <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] <;> omega

/-- Exact bit membership, including indices beyond the processed prefix. -/
theorem maskOf_testBit (active : Nat → Bool) (n digit : Nat) :
    (maskOf active n).testBit digit = (decide (digit < n) && active digit) := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    by_cases hl : digit < n
    · cases hp : active n
      · simpa [maskOf_succ, hp, hl, Nat.lt_succ_of_lt hl] using ih
      · rw [maskOf_succ, hp]
        simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hl, ih]
        simp [hl, Nat.lt_succ_of_lt hl]
    · by_cases he : digit = n
      · subst digit
        have hb := Nat.testBit_lt_two_pow (maskOf_lt active n)
        cases hp : active n
        · simp [maskOf_succ, hp, hb]
        · simp only [maskOf_succ, hp, ↓reduceIte]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, hb]
          simp
      · have hi : n + 1 ≤ digit := by omega
        have hpow : 2 ^ (n + 1) ≤ 2 ^ digit := Nat.pow_le_pow_right (by decide) hi
        have hb := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (maskOf_lt active (n + 1)) hpow)
        simpa [show ¬ digit < n + 1 by omega] using hb

/-- The runtime's division/remainder bit test agrees with group selection. -/
theorem maskOf_bit_iff (active : Nat → Bool) (n digit : Nat) :
    maskOf active n / 2 ^ digit % 2 = 1 ↔ digit < n ∧ active digit = true := by
  have hb := maskOf_testBit active n digit
  rw [Nat.testBit_eq_decide_div_mod_eq] at hb
  have he := congrArg (fun b => b = true) hb
  simpa using he

/-- Filtering the processed prefix by its mask returns exactly active digits. -/
theorem maskOf_filter (active : Nat → Bool) (n : Nat) :
    (List.range n).filter (fun digit => maskOf active n / 2 ^ digit % 2 == 1) =
      (List.range n).filter active := by
  apply List.filter_congr
  intro digit hd
  have hn : digit < n := List.mem_range.mp hd
  have h := maskOf_bit_iff active n digit
  cases hp : active digit <;> simp_all

/-- The generic parser's children coincide with the constructor's selected
child groups, in exactly the range scan's order. -/
theorem selectedChildren_maskOf (active : Nat → Bool) (n : Nat) (hash : Nat → Hash) :
    selectedChildren (maskOf active n) hash (List.range n) =
      ((List.range n).filter active).map (fun digit => (digit, hash digit)) := by
  rw [selectedChildren, maskOf_filter]

theorem childPayload_maskOf (active : Nat → Bool) (n : Nat) (hash : Nat → Hash) :
    childPayload (maskOf active n) hash (List.range n) =
      ((List.range n).filter active).flatMap hash := by
  rw [childPayload, maskOf_filter]

/-- Actual constructor grouping on first nibble; no path validity premise is
needed merely to identify which of the sixteen groups it selects. -/
def groupActive (entries : List (List Nat × Bytes)) (digit : Nat) : Bool :=
  !(entries.filter (fun entry => entry.1.head? == some digit)).isEmpty

theorem branch_group_children (entries : List (List Nat × Bytes)) (hash : Nat → Hash) :
    selectedChildren (maskOf (groupActive entries) 16) hash (List.range 16) =
      ((List.range 16).filter (groupActive entries)).map (fun digit => (digit, hash digit)) :=
  selectedChildren_maskOf _ _ _

theorem branch_group_mask_width (entries : List (List Nat × Bytes)) :
    maskOf (groupActive entries) 16 < 2 ^ 16 := maskOf_lt _ _

/-- The generated mask and concatenated active roots decode together, without
an independently assumed correspondence between bitmap bits and payload. -/
theorem decodeNode_active_branch (active : Nat → Bool) (hash : Nat → Hash) (usage : Nat)
    (hwidth : ∀ digit ∈ List.range 16, active digit = true → (hash digit).length = 32)
    (husage : usage < 2 ^ 64) :
    decodeNode ([1] ++ TrieSerialization.littleEndian 2 (maskOf active 16) ++
      ((List.range 16).filter active).flatMap hash ++ TrieSerialization.littleEndian 8 usage) =
      .ok (.branch none (((List.range 16).filter active).map fun digit => (digit, hash digit))) := by
  have h := decodeNode_branch (maskOf active 16) hash usage (maskOf_lt active 16)
    (fun digit hd hb => hwidth digit hd ((maskOf_bit_iff active 16 digit).mp hb).2) husage
  simpa only [childPayload_maskOf, selectedChildren_maskOf] using h

/-- The same generated bitmap correspondence for branches with values. -/
theorem decodeNode_active_branch_value (value : Bytes) (active : Nat → Bool)
    (hash : Nat → Hash) (usage : Nat) (hvalue : value.length < 2 ^ 32)
    (hwidth : ∀ digit ∈ List.range 16, active digit = true → (hash digit).length = 32)
    (husage : usage < 2 ^ 64) :
    decodeNode ([2] ++ TrieSerialization.valueRefBytes value ++
      TrieSerialization.littleEndian 2 (maskOf active 16) ++
      ((List.range 16).filter active).flatMap hash ++ TrieSerialization.littleEndian 8 usage) =
      .ok (.branch (some { length := value.length, hash := Sha256.hash value })
        (((List.range 16).filter active).map fun digit => (digit, hash digit))) := by
  have h := decodeNode_branch_value value (maskOf active 16) hash usage hvalue (maskOf_lt active 16)
    (fun digit hd hb => hwidth digit hd ((maskOf_bit_iff active 16 digit).mp hb).2) husage
  simpa only [childPayload_maskOf, selectedChildren_maskOf] using h

end Near.TrieBitmap
