import WasmLogic.Examples.Stack.Code
import WasmLogic.Adequacy

/-!
# The stack specifications of Iris-Wasm, ported

Each lemma here is the Iris-Wasm lemma of the same name
(`theories/iris/examples/stack/function/*.v`, `stack_common.v`), stated over
the same code and proved with WasmLogic's rules. `README.md` in this
directory lists every difference from the Rocq statements.

Iris-Wasm states `{{{{ P }}}} es {{{{ w, Q }}}}`: for every postcondition `Φ`,
`P` and `∀ w, Q -∗ Φ w` give the weakest precondition of `es` with an empty
operand stack. `Triple` is the same with the frame as an index (Iris-Wasm's
`↪[frame] f`, see `Frag.lean`): `Q` receives the final operands and frame.
-/

namespace WasmLogic.Examples.Stack

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

/-- `two14`, `two16`, `ffff0000` of `stack_common.v`. -/
abbrev two14 : Nat := 16384
abbrev two16 : Nat := 65536
abbrev ffff0000 : Nat := 4294901760

/-- `value_of_uint v`. -/
abbrev u32 (v : Nat) : Value := .i32 (UInt32.ofNat v)

section Defs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

/-- Iris-Wasm's `{{{{ P }}}} es {{{{ w, Q }}}}`, in frame `f`. -/
def Triple (lim : ExecLimits) (d : Nat) (f : Frame) (P : IProp GF) (es : List Instr)
    (Q : List Value → Frame → IProp GF) : Prop :=
  ∀ Φ : Post H GF, P ∗ (∀ vs g, Q vs g -∗ Φ.normal vs g) ⊢ wpi lim d f [] es Φ

/-- `isStack v l n`: a stack at address `v` of memory `n` holding `l`, top
first. The cell at `v` holds the address of the top element; elements sit
below it, four bytes each; the rest of the page is free. -/
def isStack (v : Nat) (l : List UInt32) (n : Nat) : IProp GF :=
  iprop(⌜two16 ∣ v⌝ ∗ ⌜v ≤ ffff0000⌝ ∗ ⌜l.length < two14⌝ ∗
    n ↦[i32][ v ] UInt32.ofNat (v + l.length * 4) ∗
    ([∗list] i ↦ w ∈ l, n ↦[i32][ v + l.length * 4 - 4 * i ] w) ∗
    ∃ bs, ⌜bs.length = two16 - 4 - l.length * 4⌝ ∗ n ↦[wms][ v + l.length * 4 + 4 ] bs)

end Defs

section Specs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits} {d : Nat}

/-- Compose two fragments: the first ends with no operands, in the same frame. -/
theorem triple_seq {f : Frame} {P R : IProp GF} {A B : List Instr}
    {Q : List Value → Frame → IProp GF}
    (hA : Triple (H := H) (GF := GF) lim d f P A (fun vs g => iprop(⌜vs = [] ∧ g = f⌝ ∗ R)))
    (hB : Triple (H := H) (GF := GF) lim d f R B Q) : Triple (H := H) (GF := GF) lim d f P (A ++ B) Q := by
  intro Φ
  iintro ⟨HP, HΦ⟩
  iapply wpi_seq
  iapply hA (Post.seq lim d B Φ)
  isplitl [HP]
  · iexact HP
  iintro %vs %g ⟨%⟨rfl, rfl⟩, HR⟩
  simp only [Post.seq_normal]
  iapply hB Φ
  isplitl [HR]
  · iexact HR
  · iexact HΦ

theorem ofNat_toNat_of_lt {v : Nat} (h : v < 2 ^ 32) : (UInt32.ofNat v).toNat = v := by
  simp [Nat.mod_eq_of_lt h]

/-- `is_stack_valid`: `validate_stack x` passes on a stack's address. -/
theorem is_stack_valid (v : Nat) (s : List UInt32) (n : Nat) (f : Frame) (x : Nat) :
    Triple (H := H) (GF := GF) lim d f iprop(⌜f.locals[x]? = some (u32 v)⌝ ∗ isStack v s n) (validate_stack x)
      (fun vs g => iprop(⌜vs = [] ∧ g = f⌝ ∗ isStack v s n)) := by
  intro Φ
  iintro ⟨⟨%hx, Hs⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hs⟩
  have hv : v < 2 ^ 32 := by simp only [ffff0000] at hle; omega
  have hrem : UInt32.ofNat v % 65536 = 0 := by
    apply UInt32.toNat_inj.mp
    simp [UInt32.toNat_mod, ofNat_toNat_of_lt hv, Nat.mod_eq_zero_of_dvd hdiv]
  simp only [validate_stack]
  wp_step 0 wpi_local_get x (u32 v) hx
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 65536
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .rem_u (UInt32.ofNat v) 65536 (UInt32.ofNat v % 65536) (by
    simp [Numeric.ibinop32])
  inext; simp only [Post.seq_normal]
  rw [hrem]
  wp_step 1 wpi_if0_false .empty [.unreachable] [] [] rfl
  inext
  iapply wpi_nil
  simp only [Post.block_normal, Post.seq_normal, List.append_nil]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; simp
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hle
    isplitr
    · ipureintro; exact hlen
    iexact Hs

theorem ofNat_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (UInt32.ofNat a == UInt32.ofNat b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : UInt32.ofNat a ≠ UInt32.ofNat b := fun e => h (by
      have := congrArg UInt32.toNat e
      rwa [ofNat_toNat_of_lt ha, ofNat_toNat_of_lt hb] at this)
    simp [h, this]

/-- The pure facts of a stack, in the forms proofs use. -/
theorem stack_bounds {v len : Nat} (hdiv : two16 ∣ v) (hle : v ≤ ffff0000) (hlen : len < two14) :
    v + len * 4 + 4 + (two16 - 4 - len * 4) ≤ 2 ^ 32 ∧ v < 2 ^ 32 ∧ v + len * 4 < 2 ^ 32 := by
  simp only [two16, ffff0000, two14] at *
  omega

/-- `is_stack_bound_valid`: `validate_stack_bound x` passes on a stack. -/
theorem is_stack_bound_valid (v : Nat) (s : List UInt32) (n : Nat) (f : Frame) (x : Nat) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[x]? = some (u32 v)⌝ ∗ isStack v s n)
      (validate_stack_bound x) (fun vs g => iprop(⌜vs = [] ∧ g = f⌝ ∗ isStack v s n)) := by
  intro Φ
  iintro ⟨⟨%hn, %hx, Hs⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, Hfree⟩
  obtain ⟨_, hv, _⟩ := stack_bounds hdiv hle hlen
  simp only [validate_stack_bound]
  wp_step 0 wpi_local_get x (u32 v) hx
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 1 wpi_drop _
  inext; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; simp
  isplitr
  · ipureintro; exact hdiv
  isplitr
  · ipureintro; exact hle
  isplitr
  · ipureintro; exact hlen
  isplitl [Hp]
  · iexact Hp
  isplitl [Hl]
  · iexact Hl
  · iexact Hfree

/-- `spec_is_empty_op`. -/
theorem spec_is_empty_op (f : Frame) (n v : Nat) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n)
      is_empty_op
      (fun vs g => iprop(∃ k : Nat, ⌜vs = [u32 k]⌝ ∗ isStack v s n ∗
        ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝ ∗ ⌜g = f⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, Hs⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, Hfree⟩
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  simp only [is_empty_op]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_relop .eq (UInt32.ofNat v) (UInt32.ofNat (v + s.length * 4))
  inext; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  iexists (if s = [] then 1 else 0)
  isplitr
  · ipureintro
    simp only [Numeric.irelop32, Numeric.bool, ofNat_beq hv hp, List.nil_append]
    by_cases hs : s = []
    · simp [hs]
    · have : s.length ≠ 0 := by simpa using hs
      simp [hs]; omega
  isplitl [Hp Hl Hfree]
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hle
    isplitr
    · ipureintro; exact hlen
    isplitl [Hp]
    · iexact Hp
    isplitl [Hl]
    · iexact Hl
    · iexact Hfree
  isplitr
  · ipureintro
    by_cases hs : s = [] <;> simp [hs]
  · ipureintro; rfl

/-- How every stack function starts: `validate_stack 0` and
`validate_stack_bound 0` pass, then the operation runs. This is how each
`spec_f` of Iris-Wasm follows from `spec_f_op`. -/
theorem validated (f : Frame) (n v : Nat) (s : List UInt32) (P : IProp GF) (op : List Instr)
    (Q : List Value → Frame → IProp GF)
    (hop : Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n ∗ P) op Q) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n ∗ P)
      (validate_stack 0 ++ validate_stack_bound 0 ++ op) Q := by
  intro Φ
  iintro ⟨⟨%hn, %h0, Hs, HP⟩, HΦ⟩
  iapply wpi_seq
  iapply wpi_seq
  iapply (is_stack_valid (H := H) (lim := lim) (d := d) v s n f 0)
    (Post.seq lim d (validate_stack_bound 0) (Post.seq lim d op Φ))
  isplitl [Hs]
  · isplitr
    · ipureintro; exact h0
    · iexact Hs
  iintro %vs %g ⟨%⟨rfl, hg⟩, Hs⟩
  simp only [Post.seq_normal]
  rw [hg]
  iapply (is_stack_bound_valid (H := H) (lim := lim) (d := d) v s n f 0) (Post.seq lim d op Φ)
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    · iexact Hs
  iintro %vs %g ⟨%⟨rfl, hg⟩, Hs⟩
  simp only [Post.seq_normal]
  rw [hg]
  iapply hop Φ
  isplitl [Hs HP]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    isplitl [Hs]
    · iexact Hs
    · iexact HP
  · iexact HΦ

theorem triple_emp {f : Frame} {P : IProp GF} {es : List Instr} {Q : List Value → Frame → IProp GF}
    (h : Triple (H := H) (GF := GF) lim d f P es Q) :
    Triple (H := H) (GF := GF) lim d f iprop(P ∗ emp) es Q := by
  intro Φ
  iintro ⟨⟨HP, -⟩, HΦ⟩
  iapply h Φ
  isplitl [HP]
  · iexact HP
  · iexact HΦ

/-- A full stack function from its operation, for preconditions without extra resources. -/
theorem validated0 (f : Frame) (n v : Nat) (s : List UInt32) (op : List Instr)
    (Q : List Value → Frame → IProp GF)
    (hop : Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n) op Q) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n)
      (validate_stack 0 ++ validate_stack_bound 0 ++ op) Q := by
  intro Φ
  iintro ⟨⟨%hn, %h0, Hs⟩, HΦ⟩
  iapply validated (H := H) (GF := GF) (lim := lim) (d := d) f n v s iprop(emp) op Q (by
    intro Φ
    iintro ⟨⟨%hn, %h0, Hs, -⟩, HΦ⟩
    iapply hop Φ
    isplitl [Hs]
    · isplitr
      · ipureintro; exact hn
      isplitr
      · ipureintro; exact h0
      · iexact Hs
    · iexact HΦ) Φ
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    isplitl [Hs]
    · iexact Hs
    · iempintro
  · iexact HΦ

/-- `spec_is_empty`. -/
theorem spec_is_empty (f : Frame) (n v : Nat) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n)
      is_empty
      (fun vs g => iprop(∃ k : Nat, ⌜vs = [u32 k]⌝ ∗ isStack v s n ∗
        ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝ ∗ ⌜g = f⌝)) :=
  validated0 f n v s is_empty_op _ (spec_is_empty_op f n v s)

/-- `spec_is_full_op`. -/
theorem spec_is_full_op (f : Frame) (n v : Nat) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n)
      is_full_op
      (fun vs g => iprop(∃ k : Nat, ⌜vs = [u32 k]⌝ ∗ isStack v s n ∗
        ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝ ∗ ⌜g = f⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, Hs⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, Hfree⟩
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  have hmod : UInt32.ofNat (v + s.length * 4) % 65536 = UInt32.ofNat (s.length * 4) := by
    apply UInt32.toNat_inj.mp
    simp only [two16, two14] at hdiv hlen
    simp [UInt32.toNat_mod, ofNat_toNat_of_lt hp, ofNat_toNat_of_lt (show s.length * 4 < 2 ^ 32 by omega)]
    omega
  have heq : (UInt32.ofNat (s.length * 4) == 65532) = decide (s.length = two14 - 1) := by
    have := ofNat_beq (a := s.length * 4) (b := 65532) (by simp only [two14] at hlen; omega) (by omega)
    simp only [show (UInt32.ofNat 65532) = 65532 from rfl] at this
    rw [this]; simp only [two14]; congr 1; apply propext; omega
  simp only [is_full_op]
  wp_step 0 wpi_i32_const 1
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 0
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 65536
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .rem_u (UInt32.ofNat (v + s.length * 4)) 65536
    (UInt32.ofNat (v + s.length * 4) % 65536) rfl
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 65532
  inext; simp only [Post.seq_normal]
  rw [hmod]
  wp_step 2 wpi_i32_relop .eq (UInt32.ofNat (s.length * 4)) 65532
  inext; simp only [Post.seq_normal]
  simp only [Numeric.irelop32, heq]
  by_cases hfull : s.length = two14 - 1
  · have hb : Numeric.bool (decide (s.length = two14 - 1)) = 1 := by simp [Numeric.bool, hfull]
    rw [hb]
    wp_norm
    wp_step 3 wpi_select_true none (.i32 1) (.i32 0) 1 (by decide)
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    iapply HΦ
    iexists 1
    isplitr
    · ipureintro; rfl
    isplitl [Hp Hl Hfree]
    · isplitr
      · ipureintro; exact hdiv
      isplitr
      · ipureintro; exact hle
      isplitr
      · ipureintro; exact hlen
      isplitl [Hp]
      · iexact Hp
      isplitl [Hl]
      · iexact Hl
      · iexact Hfree
    isplitr
    · ipureintro; exact .inl ⟨rfl, hfull⟩
    · ipureintro; rfl
  · have hb : Numeric.bool (decide (s.length = two14 - 1)) = 0 := by
      simp only [Numeric.bool, hfull, decide_false]; rfl
    rw [hb]
    wp_norm
    wp_step 3 wpi_select_false none (.i32 1) (.i32 0)
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    iapply HΦ
    iexists 0
    isplitr
    · ipureintro; rfl
    isplitl [Hp Hl Hfree]
    · isplitr
      · ipureintro; exact hdiv
      isplitr
      · ipureintro; exact hle
      isplitr
      · ipureintro; exact hlen
      isplitl [Hp]
      · iexact Hp
      isplitl [Hl]
      · iexact Hl
      · iexact Hfree
    isplitr
    · ipureintro; exact .inr ⟨rfl, by omega⟩
    · ipureintro; rfl

/-- `spec_is_full`. -/
theorem spec_is_full (f : Frame) (n v : Nat) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗ isStack v s n)
      is_full
      (fun vs g => iprop(∃ k : Nat, ⌜vs = [u32 k]⌝ ∗ isStack v s n ∗
        ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝ ∗ ⌜g = f⌝)) :=
  validated0 f n v s is_full_op _ (spec_is_full_op f n v s)

/-- `spec_stack_length_op`. -/
theorem spec_stack_length_op (f : Frame) (n v : Nat) (s : List UInt32) (len : Nat) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜s.length = len⌝ ∗ isStack v s n)
      length_stack_op
      (fun vs g => iprop(⌜vs = [u32 len]⌝ ∗ isStack v s n ∗ ⌜g = f⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %hsl, Hs⟩, HΦ⟩
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, Hfree⟩
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  have hsub : UInt32.ofNat (v + s.length * 4) - UInt32.ofNat v = UInt32.ofNat (s.length * 4) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le, ofNat_toNat_of_lt hv, ofNat_toNat_of_lt hp]; omega),
      ofNat_toNat_of_lt hv, ofNat_toNat_of_lt hp, ofNat_toNat_of_lt (by omega)]
    omega
  have hdiv4 : UInt32.ofNat (s.length * 4) / 4 = UInt32.ofNat len := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_div, ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by simp only [two14] at hlen; omega)]
    simp; omega
  simp only [length_stack_op]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .sub (UInt32.ofNat (v + s.length * 4)) (UInt32.ofNat v)
    (UInt32.ofNat (v + s.length * 4) - UInt32.ofNat v) rfl
  inext; simp only [Post.seq_normal]
  rw [hsub]
  wp_step 0 wpi_i32_const 4
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .div_u (UInt32.ofNat (s.length * 4)) 4 (UInt32.ofNat (s.length * 4) / 4) rfl
  inext; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; rw [hdiv4]; rfl
  isplitl [Hp Hl Hfree]
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hle
    isplitr
    · ipureintro; exact hlen
    isplitl [Hp]
    · iexact Hp
    isplitl [Hl]
    · iexact Hl
    · iexact Hfree
  · ipureintro; rfl

/-- `spec_stack_length`. -/
theorem spec_stack_length (f : Frame) (n v : Nat) (s : List UInt32) (len : Nat) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜s.length = len⌝ ∗ isStack v s n)
      length_stack
      (fun vs g => iprop(⌜vs = [u32 len]⌝ ∗ isStack v s n ∗ ⌜g = f⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %hl, Hs⟩, HΦ⟩
  unfold length_stack
  iapply validated (H := H) (GF := GF) (lim := lim) (d := d) f n v s iprop(⌜s.length = len⌝)
    length_stack_op (fun vs g => iprop(⌜vs = [u32 len]⌝ ∗ isStack v s n ∗ ⌜g = f⌝)) (by
      intro Φ
      iintro ⟨⟨%hn, %h0, Hs, %hl⟩, HΦ⟩
      iapply spec_stack_length_op f n v s len Φ
      isplitl [Hs]
      · isplitr
        · ipureintro; exact hn
        isplitr
        · ipureintro; exact h0
        isplitr
        · ipureintro; exact hl
        · iexact Hs
      · iexact HΦ) Φ
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    isplitl [Hs]
    · iexact Hs
    · ipureintro; exact hl
  · iexact HΦ

/-- The elements of a stack stay where they are when one more is pushed:
the `i`-th of `s` is the `i+1`-th of `a :: s`. -/
theorem stack_elems_succ (n v len : Nat) (s : List UInt32) :
    ([∗list] i ↦ w ∈ s, n ↦[i32][ v + len * 4 - 4 * i ] w) ⊣⊢
      ([∗list] i ↦ w ∈ s, n ↦[i32][ v + (len + 1) * 4 - 4 * (i + 1) ] w : IProp GF) := by
  have h : ∀ i, v + (len + 1) * 4 - 4 * (i + 1) = v + len * 4 - 4 * i := fun i => by omega
  simp only [h]
  exact .rfl

/-- `spec_push_op`. -/
theorem spec_push_op (f : Frame) (n v : Nat) (a : UInt32) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜f.locals[1]? = some (.i32 a)⌝ ∗ ⌜f.locals.size ≥ 3⌝ ∗ ⌜s.length < two14 - 1⌝ ∗
        isStack v s n)
      push_op
      (fun vs g => iprop(⌜vs = []⌝ ∗ isStack v (a :: s) n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %h1, %hsz, %hnf, Hs⟩, HΦ⟩
  simp only [push_op]
  iapply wpi_seq
  iapply spec_is_full_op f n v s (Post.seq lim d _ Φ)
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    · iexact Hs
  iintro %vs %g ⟨%k, %hvs, Hs, %hk, %hg⟩
  subst hvs hg
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [Post.seq_normal]
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, ⟨%bs, %hbs, Hfree⟩⟩
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  have hp4 : v + s.length * 4 + 4 < 2 ^ 32 := by simp only [two14, ffff0000] at *; omega
  have hbs4 : 4 ≤ bs.length := by simp only [two16, two14] at *; omega
  -- if: not full, so no trap
  rw [show (u32 0) = Value.i32 0 from rfl]
  wp_step 1 wpi_if0_false .empty [.unreachable] [] [] rfl
  inext
  iapply wpi_nil
  simp only [Post.block_normal, Post.seq_normal, List.append_nil]
  -- the new top address
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 4
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .add (UInt32.ofNat (v + s.length * 4)) 4
    (UInt32.ofNat (v + s.length * 4 + 4)) (by simp [Numeric.ibinop32, UInt32.ofNat_add])
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_local_tee 2 (.i32 (UInt32.ofNat (v + s.length * 4 + 4)))
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 1 (.i32 a) (by
    simp [Frame.withLocals, h1])
  inext; simp only [Post.seq_normal]
  -- store the element in the first free word
  have hsplit : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  rw [hsplit]
  icases (memBytes_append _ _ _ _).1 $$ Hfree with ⟨Hw, Hfree⟩
  wp_step 2 wpi_store_i32 a0 (UInt32.ofNat (v + s.length * 4 + 4)) n (v + s.length * 4 + 4) a
    (bs.take 4) (by simpa [Frame.withLocals] using hn) (by rw [ofNat_toNat_of_lt hp4]; rfl)
    (by simp; omega)
  isplitl [Hw]
  · iexact Hw
  inext; iintro Hw; simp only [Post.seq_normal]
  -- update the top address
  wp_step 0 wpi_local_get 0 (u32 v) (by
    simpa [Frame.withLocals, Array.getElem?_setIfInBounds] using h0)
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 2 (.i32 (UInt32.ofNat (v + s.length * 4 + 4))) (by
    simp [Frame.withLocals, Array.getElem?_setIfInBounds]; omega)
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_store_i32 a0 (UInt32.ofNat v) n v (UInt32.ofNat (v + s.length * 4 + 4))
    (bytes32 (UInt32.ofNat (v + s.length * 4))) (by simpa [Frame.withLocals] using hn)
    (by simp [ofNat_toNat_of_lt hv]) (by simp)
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; rfl
  isplitl [Hp Hw Hl Hfree]
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hle
    isplitr
    · ipureintro; simp only [two14] at hnf ⊢; omega
    isplitl [Hp]
    · rw [show v + (s.length + 1) * 4 = v + s.length * 4 + 4 by omega]
      iexact Hp
    isplitl [Hw Hl]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hw]
      · rw [show v + (s.length + 1) * 4 - 4 * 0 = v + s.length * 4 + 4 by omega]
        iexact Hw
      · iapply (stack_elems_succ n v s.length s).1 $$ Hl
    · iexists bs.drop 4
      isplitr
      · ipureintro; simp only [List.length_drop, two16] at hbs ⊢; omega
      · simp only [List.length_take, Nat.min_eq_left hbs4]
        rw [show v + (s.length + 1) * 4 + 4 = v + s.length * 4 + 4 + 4 by omega]
        iexact Hfree
  · ipureintro; exact ⟨rfl, rfl⟩

/-- `spec_push`. -/
theorem spec_push (f : Frame) (n v : Nat) (a : UInt32) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜f.locals[1]? = some (.i32 a)⌝ ∗ ⌜f.locals.size ≥ 3⌝ ∗ ⌜s.length < two14 - 1⌝ ∗
        isStack v s n)
      push
      (fun vs g => iprop(⌜vs = []⌝ ∗ isStack v (a :: s) n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %h1, %hsz, %hnf, Hs⟩, HΦ⟩
  unfold push
  iapply validated (H := H) (GF := GF) (lim := lim) (d := d) f n v s
    iprop(⌜f.locals[1]? = some (.i32 a)⌝ ∗ ⌜f.locals.size ≥ 3⌝ ∗ ⌜s.length < two14 - 1⌝) push_op
    (fun vs g => iprop(⌜vs = []⌝ ∗ isStack v (a :: s) n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) (by
      intro Φ
      iintro ⟨⟨%hn, %h0, Hs, %h1, %hsz, %hnf⟩, HΦ⟩
      iapply spec_push_op f n v a s Φ
      isplitl [Hs]
      · isplitr
        · ipureintro; exact hn
        isplitr
        · ipureintro; exact h0
        isplitr
        · ipureintro; exact h1
        isplitr
        · ipureintro; exact hsz
        isplitr
        · ipureintro; exact hnf
        · iexact Hs
      · iexact HΦ) Φ
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    isplitl [Hs]
    · iexact Hs
    isplitr
    · ipureintro; exact h1
    isplitr
    · ipureintro; exact hsz
    · ipureintro; exact hnf
  · iexact HΦ

/-- `spec_pop_op`. -/
theorem spec_pop_op (f : Frame) (n v : Nat) (a : UInt32) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜f.locals.size ≥ 2⌝ ∗ isStack v (a :: s) n)
      pop_op
      (fun vs g => iprop(⌜vs = [.i32 a]⌝ ∗ isStack v s n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %hsz, Hs⟩, HΦ⟩
  simp only [pop_op]
  iapply wpi_seq
  iapply spec_is_empty_op f n v (a :: s) (Post.seq lim d _ Φ)
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    · iexact Hs
  iintro %vs %g ⟨%k, %hvs, Hs, %hk, %hg⟩
  subst hvs hg
  have hk0 : k = 0 := by simp at hk; exact hk
  subst hk0
  simp only [Post.seq_normal]
  unfold isStack
  icases Hs with ⟨%hdiv, %hle, %hlen, Hp, Hl, ⟨%bs, %hbs, Hfree⟩⟩
  simp only [List.length_cons] at hlen hbs ⊢
  obtain ⟨_, hv, hp⟩ := stack_bounds hdiv hle hlen
  have hq : v + s.length * 4 < 2 ^ 32 := by omega
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Ha, Hl⟩
  rw [show (u32 0) = Value.i32 0 from rfl]
  wp_step 1 wpi_if0_false .empty [.unreachable] [] [] rfl
  inext
  iapply wpi_nil
  simp only [Post.block_normal, Post.seq_normal, List.append_nil]
  wp_step 0 wpi_local_get 0 (u32 v) h0
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat v) n v _ hn (by simp [ofNat_toNat_of_lt hv])
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  wp_step 1 wpi_local_tee 1 (.i32 (UInt32.ofNat (v + (s.length + 1) * 4)))
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_load_i32 a0 (UInt32.ofNat (v + (s.length + 1) * 4)) n
    (v + (s.length + 1) * 4 - 4 * 0) a (by simpa [Frame.withLocals] using hn)
    (by rw [ofNat_toNat_of_lt hp]; rfl)
  isplitl [Ha]
  · iexact Ha
  inext; iintro Ha; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (u32 v) (by
    simpa [Frame.withLocals, Array.getElem?_setIfInBounds] using h0)
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 1 (.i32 (UInt32.ofNat (v + (s.length + 1) * 4))) (by
    simp [Frame.withLocals, Array.getElem?_setIfInBounds]; omega)
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 4
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .sub (UInt32.ofNat (v + (s.length + 1) * 4)) 4
    (UInt32.ofNat (v + s.length * 4)) (by
      simp only [Numeric.ibinop32, Except.ok.injEq]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le, ofNat_toNat_of_lt hp]; simp; omega),
        ofNat_toNat_of_lt hp, ofNat_toNat_of_lt hq]
      simp; omega)
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_store_i32 a0 (UInt32.ofNat v) n v (UInt32.ofNat (v + s.length * 4))
    (bytes32 (UInt32.ofNat (v + (s.length + 1) * 4))) (by simpa [Frame.withLocals] using hn)
    (by simp [ofNat_toNat_of_lt hv]) (by simp)
  isplitl [Hp]
  · iexact Hp
  inext; iintro Hp; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitr
  · ipureintro; rfl
  isplitl [Hp Ha Hl Hfree]
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hle
    isplitr
    · ipureintro; omega
    isplitl [Hp]
    · iexact Hp
    isplitl [Hl]
    · iapply (stack_elems_succ n v s.length s).2 $$ Hl
    · iexists bytes32 a ++ bs
      isplitr
      · ipureintro; simp only [List.length_append, bytes32_length, two16, two14] at hbs hlen ⊢; omega
      · iapply (memBytes_append _ _ _ _).2
        isplitl [Ha]
        · rw [show v + s.length * 4 + 4 = v + (s.length + 1) * 4 - 4 * 0 by omega]
          iexact Ha
        · simp only [bytes32_length]
          rw [show v + s.length * 4 + 4 + 4 = v + (s.length + 1) * 4 + 4 by omega]
          iexact Hfree
  · ipureintro; exact ⟨rfl, rfl⟩

/-- `spec_pop`. -/
theorem spec_pop (f : Frame) (n v : Nat) (a : UInt32) (s : List UInt32) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals[0]? = some (u32 v)⌝ ∗
        ⌜f.locals.size ≥ 2⌝ ∗ isStack v (a :: s) n)
      pop
      (fun vs g => iprop(⌜vs = [.i32 a]⌝ ∗ isStack v s n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %h0, %hsz, Hs⟩, HΦ⟩
  unfold pop
  iapply validated (H := H) (GF := GF) (lim := lim) (d := d) f n v (a :: s)
    iprop(⌜f.locals.size ≥ 2⌝) pop_op
    (fun vs g => iprop(⌜vs = [.i32 a]⌝ ∗ isStack v s n ∗ ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) (by
      intro Φ
      iintro ⟨⟨%hn, %h0, Hs, %hsz⟩, HΦ⟩
      iapply spec_pop_op f n v a s Φ
      isplitl [Hs]
      · isplitr
        · ipureintro; exact hn
        isplitr
        · ipureintro; exact h0
        isplitr
        · ipureintro; exact hsz
        · iexact Hs
      · iexact HΦ) Φ
  isplitl [Hs]
  · isplitr
    · ipureintro; exact hn
    isplitr
    · ipureintro; exact h0
    isplitl [Hs]
    · iexact Hs
    · ipureintro; exact hsz
  · iexact HΦ

theorem page_split :
    List.replicate ((1 : UInt32).toNat * pageSize) (0 : UInt8) =
      List.replicate 4 0 ++ List.replicate (two16 - 4) 0 := by
  rw [List.replicate_append_replicate, show (1 : UInt32).toNat * pageSize = 4 + (two16 - 4) from rfl]

/-- `spec_new_stack`: `memory.grow 1` either fails, and `new_stack`
returns `-1`, or gives a fresh page at the old memory length `len`, which
becomes an empty stack. -/
theorem spec_new_stack (f : Frame) (n len : Nat) :
    Triple (H := H) (GF := GF) lim d f
      iprop(⌜f.mi.memAddrs[0]? = some n⌝ ∗ ⌜f.locals.size ≥ 1⌝ ∗ ⌜pageSize ∣ len⌝ ∗
        n ↦[wmlength] len)
      new_stack
      (fun vs g => iprop(
        ((⌜vs = [.i32 0xFFFFFFFF]⌝ ∗ n ↦[wmlength] len) ∨
          (⌜vs = [u32 len]⌝ ∗ isStack len [] n ∗ n ↦[wmlength] (len + pageSize))) ∗
        ⌜g.inst = f.inst ∧ g.mi = f.mi⌝)) := by
  intro Φ
  iintro ⟨⟨%hn, %hsz, %hdiv, Hlen⟩, HΦ⟩
  simp only [new_stack]
  wp_step 0 wpi_i32_const 1
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_memory_grow_either n len 1 hn
  isplitl [Hlen]
  · iexact Hlen
  inext
  isplit
  · iintro %hle ⟨Hlen, Hbytes⟩
    simp only [Post.seq_normal]
    have hp : len / pageSize ≤ 65535 := by simp [maxPages] at hle; omega
    have hlen : len = len / pageSize * pageSize := (Nat.div_mul_cancel hdiv).symm
    have hl32 : len < 2 ^ 32 := by simp only [pageSize] at hp hlen; omega
    wp_step 1 wpi_local_tee 0 (.i32 (UInt32.ofNat (len / pageSize)))
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq (UInt32.ofNat (len / pageSize)) 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    have hb : Numeric.bool (Numeric.irelop32 .eq (UInt32.ofNat (len / pageSize)) 0xFFFFFFFF) = 0 := by
      have : (0xFFFFFFFF : UInt32) = UInt32.ofNat 4294967295 := rfl
      simp only [Numeric.irelop32, Numeric.bool, this, ofNat_beq (by omega : len / pageSize < 2 ^ 32)
        (by decide : 4294967295 < 2 ^ 32)]
      simp; omega
    rw [hb]
    wp_step 1 wpi_if0_false (.val (.num .i32)) _ _ [] rfl
    inext
    wp_step 0 wpi_local_get 0 (.i32 (UInt32.ofNat (len / pageSize))) (by
      simp [Frame.withLocals, Array.getElem?_setIfInBounds]; intro h; simp [h] at hsz)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 65536
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .mul (UInt32.ofNat (len / pageSize)) 65536 (UInt32.ofNat len) (by
      simp only [Numeric.ibinop32, Except.ok.injEq]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_mul, ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt hl32]
      simp only [pageSize] at hlen ⊢
      simp; omega)
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_local_tee 0 (.i32 (UInt32.ofNat len))
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 0 (.i32 (UInt32.ofNat len)) (by
      simp [Frame.withLocals, Array.getElem?_setIfInBounds]; intro h; simp [h] at hsz)
    inext; simp only [Post.seq_normal]
    rw [page_split]
    icases (memBytes_append _ _ _ _).1 $$ Hbytes with ⟨Hw, Hfree⟩
    wp_step 2 wpi_store_i32 a0 (UInt32.ofNat len) n len (UInt32.ofNat len) (List.replicate 4 0)
      (by simpa [Frame.withLocals] using hn) (by simp [ofNat_toNat_of_lt hl32]) (by simp)
    isplitl [Hw]
    · iexact Hw
    inext; iintro Hw; simp only [Post.seq_normal]
    wp_step 0 wpi_local_get 0 (.i32 (UInt32.ofNat len)) (by
      simp [Frame.withLocals, Array.getElem?_setIfInBounds]; intro h; simp [h] at hsz)
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.block_normal, Post.seq_normal, List.nil_append]
    iapply wpi_nil
    iapply HΦ
    isplitl [Hw Hfree Hlen]
    · iright
      isplitr
      · ipureintro; rfl
      isplitl [Hw Hfree]
      · unfold isStack
        simp only [List.length_nil, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
        isplitr
        · ipureintro; simpa [two16, pageSize] using hdiv
        isplitr
        · ipureintro; simp only [ffff0000, pageSize] at hp hlen ⊢; omega
        isplitr
        · ipureintro; decide
        isplitl [Hw]
        · iexact Hw
        isplitr
        · iapply BigSepL.bigSepL_nil.2; iempintro
        · iexists List.replicate (two16 - 4) 0
          isplitr
          · ipureintro; simp
          · simp only [List.length_replicate]
            iexact Hfree
      · simp only [UInt32.toNat_one, Nat.one_mul]
        iexact Hlen
    · ipureintro; exact ⟨rfl, rfl⟩
  · iintro Hlen
    simp only [Post.seq_normal]
    wp_step 1 wpi_local_tee 0 (.i32 0xFFFFFFFF)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq 0xFFFFFFFF 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    have hb : Numeric.bool (Numeric.irelop32 .eq 0xFFFFFFFF 0xFFFFFFFF) = 1 := by decide
    rw [hb]
    wp_step 1 wpi_if0_true (.val (.num .i32)) _ _ [] 1 (by decide) rfl
    inext
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.block_normal, Post.seq_normal, List.nil_append]
    iapply wpi_nil
    iapply HΦ
    isplitl [Hlen]
    · ileft
      isplitr
      · ipureintro; rfl
      · iexact Hlen
    · ipureintro; exact ⟨rfl, rfl⟩

end Specs

end WasmLogic.Examples.Stack
