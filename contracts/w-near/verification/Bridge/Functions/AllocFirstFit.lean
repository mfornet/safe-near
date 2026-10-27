import Binary.Code.Part11
import Bridge.Functions.AllocNewCell
import Bridge.Functions.MemCpy
import Bridge.Functions.Borrow
import Mathlib.Tactic.IntervalCases

/-!
# `alloc_first_fit` (580), in the metered logic (milestone M4)

```
alloc_first_fit(words, align, slot, policy, vtable) -> *u8     (580; 0 on failure)
  l1 := *slot
  loop @3                                   -- the walk
    l1 == 0 → return 0
    loop @7                                 -- the merge loop
      nf := l1.next_free
      nf & CAN_MERGE:                       -- merge l1 into its previous neighbour p
        l1.next_free := nf & !1;  p := l1.prev (free, by clause (4));  remove(l1) (575)
        l1 was last → p.word0 |= NEXT_CELL_IS_INVALID;  *slot := p;  p.size() (576);  l1 := p
        continue @7
      size(l1) (576) < 4 words → *slot := l1.next_free (raw); l1 := it; continue @3    -- unlink
      A := (next - 4 words) & -align;  l1 + 8 + 8 + 4 * min_cell_size (16, by call_indirect) > A →
        (l1 + 8) aligned → *slot := nf & !3; l1.word0 |= ALLOCATED; return l1 + 8   -- whole
        else *slot := nf; l1 := nf; continue @3                                      -- unlink
      N := A - 8 (574: next - N ≥ 8);  N.next_free := 0;  N.word0 := next;  N.word1 := l1
      next.prev := N (if l1 not last);  l1.word0 := N (+ last bit moved to N)
      N.word0 |= ALLOCATED; return A                                                  -- split
```

## What is proved

* `f580_empty` (21 `regular_op_cost`s): on an empty list, 580 returns 0.
* `f580_one` (≤ 300): on a list of one free cell `c` without `CAN_MERGE` and with
  `next_free = 0` (`oneRes`), any word count `1 ≤ w < 2^28` and power-of-two `align ≤ 2^20`:
  `post1`, one of
  - *unlinked* (`0`): `¬ fits ∨ (¬ canSplit ∧ ¬ aligned)`, the slot emptied, `c` unchanged;
  - *whole* (`c + 8`): `fits ∧ ¬ canSplit ∧ aligned`, the slot emptied, `c.word0 | ALLOCATED`;
  - *split* (`A = aN`): `fits ∧ canSplit`, the slot still `c`, `c.word0 = A - 8`,
    the new cell `A - 8` with header `(c.word0 | ALLOCATED, c)`, `nx - A` data bytes at `A`,
    and the next neighbour's `prev` (if `c` is not last) `A - 8`.
  This is exactly the list a fresh chunk leaves (577) and the one every allocation leaves
  while nothing is freed (after a split the list is the front remainder, `next_free = 0`;
  after whole/unlink it is empty), so with `f580_empty` it covers every walk of a method
  that does not free. Both loops are entered with `mwpi_loop0`: the outer one with a
  two-state invariant (the cell listed, or the slot emptied after an unlink, which then
  exits); the merge loop with a pinned invariant (`mwpi_loop_pin`, no merge happens).
* `split_spec`: the split, on its own (see the pitfalls below).

Costs exclude 580's activation (paid by the caller) and include the calls to 572, 576, 574
and (through `call_indirect`, table entry and vtable word owned in `vt`) 578, with their
activations. The split path costs about 285, the others less; 300 is the bound.

## The general walk: loop invariants (design; not proved here)

With `H` the heap model at entry, `ℓ = H.freeList`, the walk keeps, at the head of loop @3:

* `slot ↦ l1`, `l1 = ℓ'.headD 0` for a suffix `ℓ'` of `ℓ` **after merges**, i.e. a model
  `H'` with `H'.freeList = ℓ'`, `H'.cells` = `H.cells` with the merged cells removed and
  their predecessors grown, `WfFix H' live (ℓ'.length)` minus nothing: the walked-past
  prefix is *leaked* (free cells not listed), which `wf` allows (clause 6);
* `[∗list] c ∈ H'.cells, cellRes n live c` and the rest of `heapInv`'s resources except the
  head word (581 holds the head in a stack slot during the walk);
* credits `A₁ · 2 · ℓ'.length + A₀'` for the steps left (each outer iteration pops a cell,
  each merge removes one: at most `2F` iterations).

and at the head of loop @7 the same with `l1 = ℓ'.head` (nonzero, listed, free). The merge
step needs clause (4) (the next listed cell is `l1.prev`, free) to make `p := l1.prev` the
new head, and `remove` (575) rewires `l1.next.prev`, which is another cell's header: the
invariant must own *all* headers (it does, `cellRes`). The unlink step needs the raw
`next_free` to be the next list cell: see the gap below.

## Invariant findings (AllocInv's `HeapModel.wf`)

1. **`next_free` bit 1** (clause 3). 580 unlinks a cell with `*slot := c.next_free` *raw*
   (only `CAN_MERGE`, bit 0, is known clear there), and the next iteration dereferences it;
   clause (3) only says `c.nextFree / 4 * 4 = next`, so a `next_free` with bit 1 set would
   send the walk to `next + 2`. Needed: `c.nextFree % 4 < 2` (dealloc only ever writes a
   cell address, or `cell | CAN_MERGE`, so it holds).
2. **Minimum cell size** (clause 1, `c.addr + 24 ≤ c.next`, kept in `AllocDealloc.Geo`).
   The split creates an *allocated* cell whose data is `next - A ≥ 4 · words`, which is less
   than 16 bytes for `words < 4` (e.g. a 1-byte `Vec<u8>`: `words = 1`, a 4-byte cell), so
   `c.addr + 24 ≤ c.next` fails for it (and for the free cell it becomes once deallocated).
   The bound 580/582 need is `c.addr + 12 ≤ c.next` (a free cell's `next_free` word); the
   split itself guarantees ≥ 64 data bytes only for the *remainder* (`canSplit`).
3. **Clause 5** (also found by the dealloc agent, `AllocDealloc.Lives`): the `↔` forces every
   `(c + 8, s)` with `s ≤ size` into `live`, so `(p, size) :: live` is never a valid post.
4. **`next % 4 = 0`** (also found by the dealloc agent): needed here too (`w0_mask`).
5. **The failure branch is not only "memory.grow failed".** After a successful grow the
   second walk on the fresh cell can still unlink it and return 0: the fresh cell has
   `pages · 65536 - 8 ≥ max(4w, 8(align + 64))` data bytes, but when `4w` dominates and the
   slack is small, `A < c + 80` (no split) and the cell is taken whole only if `c + 8` is
   `align`-aligned, i.e. (`c` page-aligned) `align ≤ 8`. So for `align ≥ 16` and
   `4w + 8` just under a page multiple, wee_alloc 0.4.5 returns 0 *with the memory grown*.
   AllocInv's `p = 0 ∗ heapInv n live 0` still holds (the fresh cell is leaked), but the
   unreachability argument for refinement must use `align ≤ 8` (true of wNEAR's
   allocations) or the slack.

## Pitfalls met (for the next proofs)

* A symbolic `A + 4294967288` (`A - 8`) in a local, or an `icases` on a points-to whose
  list is `bs.take (… (A + 4294967288).toNat …)`, makes the *kernel* run out of stack
  (`(kernel) deep recursion`): rewrite it to `UInt32.ofNat (A.toNat - 8)` right after the
  `i32.add`, and keep the split-off lists abstract (`split_data`).
* Hypotheses about `UInt32` arithmetic (`(x - y).toNat = …`, `x + k = N`) in the context
  make `mstep`'s side conditions (`simp (disch := omega)`) hit the recursion limit; wrap
  them in the structure `Hold` (a `def` is not enough) and take them out with `.get`.
* `bv_decide` would close the header bit lemmas at once but leaves native axioms
  (`ofReduceBool`); they are proved by `testBit` (`u32_ext`, `tb_*`) instead.
* `mstep` cannot branch on a `br_if`/`br` out of a `loop` body (no `Post.mloop` simp lemmas):
  `Post.mloop_*` below, and `iapply mwpi_br_if_taken'` / `mwpi_br` with a `simp only`.
-/

namespace WNear.Binary.AllocFirstFit

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves
set_option maxRecDepth 20000
variable {GF : BundledGFunctors} [WasmGS NearState GF]

section MLoop
variable {cfg : WasmConfig} {Cg : Nat}
@[simp] theorem Post.mloop_normal (p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) (vs : List Value) (g : Frame) :
    (Post.mloop cfg Cg p vs₀ I Φ).normal vs g = pay Cg 0 (Φ.normal (vs₀ ++ vs) g) := rfl
@[simp] theorem Post.mloop_br_zero (p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) (X : List Value) (g : Frame) :
    (Post.mloop cfg Cg p vs₀ I Φ).br 0 X g =
      iprop(⌜p ≤ X.length⌝ ∗ pay Cg (2 * cfg.regularOpCost) (I (X.drop (X.length - p)) g)) := rfl
@[simp] theorem Post.mloop_br_succ (p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) (n : Nat) (X : List Value) (g : Frame) :
    (Post.mloop cfg Cg p vs₀ I Φ).br (n + 1) X g = Φ.br n (vs₀ ++ X) g := rfl
@[simp] theorem Post.mloop_ret (p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) (X : List Value) (g : Frame) :
    (Post.mloop cfg Cg p vs₀ I Φ).ret X g = Φ.ret (vs₀ ++ X) g := rfl
@[simp] theorem Post.mloop_trap (p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) : (Post.mloop cfg Cg p vs₀ I Φ).trap = Φ.trap := rfl
end MLoop

/-- Normalise loop postconditions, then the usual. -/
macro "mloop_norm" : tactic =>
  `(tactic| (simp only [Post.mloop_normal, Post.mloop_br_zero, Post.mloop_br_succ, Post.mloop_ret,
      Post.mloop_trap, List.nil_append, List.append_nil]; mctrl_norm; repeat mpay))

/-- A `br_if` not taken, its condition `h` (a term), by hand. -/
macro "mnot_taken " h:term : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [$hc:ident]; · iexact $hc:ident
             isplitr; · ipureintro; exact ⟨rfl, by omega, $h⟩
             inext; iintro $hc:ident; mctrl_norm))

theorem mwpi_loop_pin {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame}
    {Φ : Post NearState GF} {Cg R : Nat} (bt : BlockType) (body : List Instr) (P : IProp GF)
    (hp : (Exec.blockType f.mi bt).params = []) :
    □ (P -∗ mwpi cfg lim d f [] body
          (Post.mloop cfg Cg 0 [] (fun X g => iprop(⌜X = [] ∧ g = f⌝ ∗ P)) Φ)) ∗
      credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ P)
      ⊢ mwpi cfg lim d f [] [.loop bt body] Φ := by
  iintro ⟨#Hb, Hc, HP⟩
  iapply WNear.Binary.MemCpy.mwpi_loop0 bt body (fun X g => iprop(⌜X = [] ∧ g = f⌝ ∗ P)) hp
  isplitr
  · imodintro
    iintro %X %l ⟨%⟨hX, hg⟩, HP⟩
    subst hX
    rw [hg]
    iapply Hb $$ HP
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iapply HP $$ Hc

theorem f580_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (w al slot pd pv : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          n ↦[wms][ slot.toNat ] bytes32 0))
        (fun _ => 21 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[wms][ slot.toNat ] bytes32 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hs⟩ Hc
  subst hargs
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  rw [show 5 * cfg.regularOpCost + R = cfg.regularOpCost + (4 * cfg.regularOpCost + R) by omega]
  iapply mwpi_cons
  iapply mwpi_loop_pin (Cg := Cg) .empty _ iprop(credits Cg (4 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] 0) rfl
  isplitr
  · imodintro
    iintro ⟨Hc, Hs⟩
    mstep; mstep
    mstep_taken
    mloop_norm
    mstep
    rw [htype]
    iframe Hc Hs
    ipureintro; rfl
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iframe Hc Hs


theorem tb_hi (c i : Nat) (hc : c < 2 ^ 32) (h32 : 32 ≤ i) : c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) h32))

theorem tb_small (c i : Nat) (hc : c < 4) (h2 : 2 ≤ i) : c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (show c < 2 ^ 2 by omega) (Nat.pow_le_pow_right (by omega) h2))

theorem tb_low (x i : Nat) (h : x % 4 = 0) (hi : i < 2) : x.testBit i = false := by
  have e := Nat.testBit_mod_two_pow x 2 i
  rw [show x % 2 ^ 2 = 0 by simpa using h] at e
  simp [hi] at e
  exact e

theorem tb_mid (c i : Nat) (hc : c = 4294967292 ∨ c = 4294967293) (h1 : 2 ≤ i) (h2 : i < 32) :
    c.testBit i = true := by
  rcases hc with rfl | rfl <;> interval_cases i <;> decide

theorem u32_ext (a b : UInt32) (h : ∀ i, i < 32 → a.toNat.testBit i = b.toNat.testBit i) : a = b := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq; intro i
  rcases Nat.lt_or_ge i 32 with hi | hi
  · exact h i hi
  · rw [tb_hi _ i a.toNat_lt hi, tb_hi _ i b.toNat_lt hi]

theorem w0_mask_t (nx : UInt32) (h : nx.toNat % 4 = 0) : (nx ||| 2) &&& 4294967292 = nx := by
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi1
  · rw [tb_low _ 0 h (by omega)]; try decide
  · rw [tb_low _ 1 h (by omega)]; try decide
  · rw [tb_small 2 i (by omega) hi1, tb_mid 4294967292 i (by omega) hi1 hi]; simp

theorem w0_mask_f (nx : UInt32) (h : nx.toNat % 4 = 0) : nx &&& 4294967292 = nx := by
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.testBit_and]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi1
  · rw [tb_low _ 0 h (by omega)]; try decide
  · rw [tb_low _ 1 h (by omega)]; try decide
  · rw [tb_mid 4294967292 i (by omega) hi1 hi]; simp

theorem toNat_mod4' (x : UInt32) (h : x &&& 3 = 0) : x.toNat % 4 = 0 := by
  have e := congrArg UInt32.toNat h
  rw [UInt32.toNat_and, show (3 : UInt32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
  simpa using e

theorem or2_and2 (N : UInt32) : (N ||| 2) &&& 2 = 2 := by
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 1 ∨ i ≠ 1 by omega) with rfl | h1
  · cases N.toNat.testBit 1 <;> decide
  · have : (2 : Nat).testBit i = false := by
      rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]; simp; omega
    rw [this]; simp

theorem and2_zero (N : UInt32) (hN : N &&& 3 = 0) : N &&& 2 = 0 := by
  have h := toNat_mod4' N hN
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.reduceToNat, Nat.testBit_and]
  rcases (show i < 2 ∨ 2 ≤ i by omega) with h1 | h1
  · rw [tb_low _ i h h1]; simp
  · rw [tb_small 2 i (by omega) h1]; simp

theorem or2_clear (N : UInt32) (hN : N &&& 3 = 0) : (N ||| 2) &&& 4294967293 = N := by
  have h := toNat_mod4' N hN
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi1
  · rw [tb_low _ 0 h (by omega)]; try decide
  · rw [tb_low _ 1 h (by omega)]; try decide
  · rw [tb_small 2 i (by omega) hi1, tb_mid 4294967293 i (by omega) hi1 hi]; simp

theorem v_false (nx N : UInt32) (h : nx &&& 3 = 0) : nx &&& 3 ||| N = N := by
  rw [h]; apply u32_ext; intro i hi
  simp only [UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_or]
  simp

theorem v_true (nx N : UInt32) (h : nx &&& 3 = 0) (hN : N &&& 3 = 0) :
    (nx ||| 2) &&& 3 ||| N = N ||| 2 := by
  have h1 := toNat_mod4' nx h
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi1
  · rw [tb_low _ 0 h1 (by omega)]; cases N.toNat.testBit 0 <;> decide
  · rw [tb_low _ 1 h1 (by omega)]; cases N.toNat.testBit 1 <;> decide
  · rw [tb_small 2 i (by omega) hi1, tb_small 3 i (by omega) hi1]; simp

theorem zero_and_or (c : UInt32) : UInt32.ofNat 0 &&& 3 ||| c = c := by
  apply u32_ext; intro i hi
  simp only [UInt32.toNat_and, UInt32.toNat_or, UInt32.reduceToNat, Nat.testBit_and, Nat.testBit_or,
    UInt32.toNat_ofNat']
  simp

theorem flag_zero' (al : UInt32) (h : al ≠ 0) : ¬ (al < al + 4294967295) := by
  have h0 : al.toNat ≠ 0 := fun e => h (UInt32.toNat_inj.mp (by simpa using e))
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; have := al.toNat_lt; simp; omega

theorem and_neg_toNat' (x al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20) :
    (x &&& (0 - al)).toNat = x.toNat - x.toNat % al.toNat := by
  have hpk : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by omega) hk
  have h0 : (0 - al).toNat = 2 ^ 32 - 2 ^ k := by
    rw [UInt32.toNat_sub]; simp [hal]
  have h1 : (0 - al).toNat = 2 ^ k * (2 ^ (32 - k) - 1) := by
    rw [h0, Nat.mul_sub, Nat.mul_one, <- Nat.pow_add, show k + (32 - k) = 32 by omega]
  have h2 : x.toNat - x.toNat % 2 ^ k = 2 ^ k * (x.toNat / 2 ^ k) := by
    have := Nat.mod_add_div x.toNat (2 ^ k); omega
  rw [hal, h2, UInt32.toNat_and, h1]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  rcases Nat.lt_or_ge i k with h | h
  · simp [show ¬ i ≥ k by omega]
  · rw [show i - k + k = i by omega]
    rcases Nat.lt_or_ge i 32 with h3 | h3
    · simp [h, show i - k < 32 - k by omega]
    · rw [tb_hi _ i x.toNat_lt h3]; simp

/-- Word 0 of a free cell whose next neighbour (or chunk end) is `nx`. -/
def w0 (nx : UInt32) (lst : Bool) : UInt32 := if lst then nx ||| 2 else nx

theorem w0_mask (nx : UInt32) (lst : Bool) (h : nx &&& 3 = 0) : w0 nx lst &&& 4294967292 = nx := by
  cases lst
  · exact w0_mask_f nx (toNat_mod4' nx h)
  · exact w0_mask_t nx (toNat_mod4' nx h)

/-- 580's frame with the parameters `w al slot pd pv`, `l5 = 0`, the derived
locals of a nonzero `al`, and the loop's locals `l1, l9 … l13`. -/
def fr (inst : Nat) (mi : ModuleInst) (w al slot pd pv l1 l9 l10 l11 l12 l13 : UInt32) : Frame :=
  ⟨#[.i32 w, .i32 l1, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al), .i32 (al + 4294967295),
    .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩

theorem flag_zero (al : UInt32) (h : al ≠ 0) :
    Numeric.bool (Numeric.irelop32 IRelOp.gt_u (al + 4294967295) al) = 0 := by
  simp only [Numeric.bool, Numeric.irelop32]
  have := flag_zero' al h
  simp [this]

theorem lt_true (x y : UInt32) (h : x.toNat < y.toNat) :
    Numeric.bool (Numeric.irelop32 .lt_u x y) ≠ 0 := by
  simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, h]

theorem lt_false (x y : UInt32) (h : y.toNat ≤ x.toNat) :
    Numeric.bool (Numeric.irelop32 .lt_u x y) = 0 := by
  have : ¬ x < y := by rw [UInt32.lt_iff_toNat_lt]; omega
  simp [Numeric.bool, Numeric.irelop32, this]

theorem gt_true (x y : UInt32) (h : y.toNat < x.toNat) :
    Numeric.bool (Numeric.irelop32 .gt_u x y) ≠ 0 := by
  simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, h]

theorem gt_false (x y : UInt32) (h : x.toNat ≤ y.toNat) :
    Numeric.bool (Numeric.irelop32 .gt_u x y) = 0 := by
  have : ¬ y < x := by rw [UInt32.lt_iff_toNat_lt]; omega
  simp [Numeric.bool, Numeric.irelop32, this]

theorem and_low_toNat (x al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20) :
    (x &&& (al + 4294967295)).toNat = x.toNat % al.toNat := by
  have h1 : (al + 4294967295).toNat = 2 ^ k - 1 := by
    rw [UInt32.toNat_add, hal]; simp
    have := Nat.one_le_two_pow (n := k)
    have : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by omega) hk
    omega
  rw [UInt32.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, hal]

theorem and_neg_toNat (x al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20) :
    (x &&& (0 - al)).toNat = x.toNat - x.toNat % al.toNat :=
  and_neg_toNat' x al k hal hk

theorem eqz_and_true (x al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (h : x.toNat % al.toNat = 0) :
    Numeric.bool ((al + 4294967295) &&& x == 0) ≠ 0 := by
  have : (al + 4294967295) &&& x = 0 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.and_comm, and_low_toNat x al k hal hk, h]; rfl
  simp [this, Numeric.bool]

theorem eqz_and_false (x al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (h : x.toNat % al.toNat ≠ 0) :
    Numeric.bool ((al + 4294967295) &&& x == 0) = 0 := by
  have : (al + 4294967295) &&& x ≠ 0 := by
    intro e
    have := congrArg UInt32.toNat e
    rw [UInt32.and_comm, and_low_toNat x al k hal hk] at this
    exact h (by simpa using this)
  simp [this, Numeric.bool]


/-! ## The walk over a list of at most one cell -/

/-- The data bytes of the cell `c` whose next neighbour is `nx`. -/
def szN (c nx : UInt32) : Nat := nx.toNat - c.toNat - 8

/-- Where a split puts the new cell's data: `(nx - 4 w) & -al`. -/
def aN (nx w al : UInt32) : Nat := (nx.toNat - 4 * w.toNat) - (nx.toNat - 4 * w.toNat) % al.toNat

/-- The three outcomes' conditions. -/
def fits (w c nx : UInt32) : Prop := 4 * w.toNat ≤ szN c nx
def canSplit (w al c nx : UInt32) : Prop := c.toNat + 80 ≤ aN nx w al
def aligned (al c : UInt32) : Prop := (c.toNat + 8) % al.toNat = 0

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The next neighbour's `prev` word, owned when the cell is not the last of its chunk. -/
def nextW (n : Nat) (nx v : UInt32) (lst : Bool) : IProp GF :=
  if lst then iprop(emp) else iprop(n ↦[i32][ nx.toNat + 4 ] v)

theorem nextW_false {GF : BundledGFunctors} [WasmGS NearState GF] (n : Nat) (nx v : UInt32) :
    nextW (GF := GF) n nx v false = iprop(n ↦[i32][ nx.toNat + 4 ] v) := rfl

theorem nextW_true {GF : BundledGFunctors} [WasmGS NearState GF] (n : Nat) (nx v : UInt32) :
    nextW (GF := GF) n nx v true = iprop(emp) := rfl

/-- The policy's vtable slot `min_cell_size` and its table entry. -/
def vt (n : Nat) (pv idx : UInt32) (ta a578 : Nat) : IProp GF :=
  iprop(n ↦[i32][ pv.toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578)

/-- The free cell `c` (header word 0, `next_free = 0`, data), `nextW`, `vt`; the slot holds `s`. -/
def oneRes (n : Nat) (slot s c nx npv : UInt32) (lst : Bool) (bs : List UInt8) (pv idx : UInt32)
    (ta a578 : Nat) : IProp GF :=
  iprop(n ↦[i32][ slot.toNat ] s ∗ n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
    n ↦[wms][ c.toNat + 12 ] bs ∗ nextW n nx npv lst ∗ vt n pv idx ta a578)

/-- 580's result on a list of one free cell `c` with `next_free = 0`: the cell
too small or (not splittable and misaligned) and unlinked (`0`, the slot
emptied); taken whole (`c + 8`, allocated, unlinked); or split, the new
allocated cell `r - 8` at the aligned tail, `c` shrunk and still listed. -/
def post1 (n : Nat) (w al slot c nx npv : UInt32) (lst : Bool) (bs : List UInt8) (pv idx : UInt32)
    (ta a578 : Nat) (_args rs : List Value) : IProp GF :=
  iprop(∃ r : UInt32, ⌜rs = [.i32 r]⌝ ∗ vt n pv idx ta a578 ∗
    ((⌜r = 0 ∧ (¬ fits w c nx ∨ (¬ canSplit w al c nx ∧ ¬ aligned al c))⌝ ∗
        n ↦[i32][ slot.toNat ] 0 ∗ n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
        n ↦[wms][ c.toNat + 12 ] bs ∗ nextW n nx npv lst) ∨
     (⌜r = c + 8 ∧ fits w c nx ∧ ¬ canSplit w al c nx ∧ aligned al c⌝ ∗
        n ↦[i32][ slot.toNat ] 0 ∗ n ↦[i32][ c.toNat ] (w0 nx lst ||| 1) ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
        n ↦[wms][ c.toNat + 12 ] bs ∗ nextW n nx npv lst) ∨
     (⌜r.toNat = aN nx w al ∧ fits w c nx ∧ canSplit w al c nx⌝ ∗
        n ↦[i32][ slot.toNat ] c ∗ n ↦[i32][ c.toNat ] (r - 8) ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
        n ↦[wms][ c.toNat + 12 ] bs.take (r.toNat - 8 - c.toNat - 12) ∗
        n ↦[i32][ r.toNat - 8 ] (w0 nx lst ||| 1) ∗ n ↦[i32][ r.toNat - 4 ] c ∗
        (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - r.toNat⌝ ∗ n ↦[wms][ r.toNat ] bs') ∗
        nextW n nx (npv &&& 3 ||| (r - 8)) lst)))

end Res

/-- A fact kept out of `omega`'s sight (it slows `mstep`'s side conditions down). -/
structure Hold (p : Prop) : Prop where
  get : p

theorem eqz_false (x : UInt32) (h : x ≠ 0) : Numeric.bool (x == 0) = 0 := by
  simp [Numeric.bool, h]

theorem eqz_true (x : UInt32) (h : x = 0) : Numeric.bool (x == 0) ≠ 0 := by
  simp [Numeric.bool, h]

theorem i64_zero_lo : (storeBytes (.i64 0) 8).take 4 = bytes32 0 := by decide
theorem i64_zero_hi : (storeBytes (.i64 0) 8).drop 4 = bytes32 0 := by decide

theorem w0_and2 (nx : UInt32) (lst : Bool) (h : nx &&& 3 = 0) :
    w0 nx lst &&& 2 = if lst then 2 else 0 := by
  cases lst
  · exact and2_zero nx h
  · exact or2_and2 nx

theorem zero_and2 : UInt32.ofNat 0 &&& 4294967294 = 0 := by decide

theorem aN_mod4 (nx w al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hnx : nx.toNat % 4 = 0) :
    aN nx w al % 4 = 0 := by
  unfold aN
  rw [hal]
  have hx : (nx.toNat - 4 * w.toNat) % 4 = 0 := by omega
  generalize nx.toNat - 4 * w.toNat = x at *
  rcases k with _ | _ | k
  · simp [Nat.mod_one]; omega
  · simp only [Nat.zero_add, Nat.pow_one]; omega
  · have : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_add, Nat.mul_comm]
    rw [this]
    have h1 : x % (4 * 2 ^ k) % 4 = x % 4 := Nat.mod_mod_of_dvd x ⟨2 ^ k, rfl⟩
    omega

theorem toNat_mod4 (x : UInt32) (h : x &&& 3 = 0) : x.toNat % 4 = 0 := by
  have e := congrArg UInt32.toNat h
  rw [UInt32.toNat_and, show (3 : UInt32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
  simpa using e

theorem and3_of_mod4 (x : UInt32) (h : x.toNat % 4 = 0) : x &&& 3 = 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]; simp
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

section Split

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A free cell's data split around the new cell's header at `N`. -/
theorem split_data (n c N : Nat) (bs : List UInt8) (h1 : c + 12 ≤ N) (h2 : N + 12 ≤ c + 12 + bs.length) :
    n ↦[wms][ c + 12 ] bs ⊢ (∃ b0 b8 b4 br : List UInt8, ⌜b0 = bs.take (N - c - 12) ∧ b8.length = 8 ∧
        b4.length = 4 ∧ br.length + N + 12 = c + 12 + bs.length⌝ ∗ n ↦[wms][ c + 12 ] b0 ∗
        n ↦[wms][ N ] b8 ∗ n ↦[wms][ N + 8 ] b4 ∗ n ↦[wms][ N + 12 ] br : IProp GF) := by
  iintro H
  icases WNear.Binary.U128From.memBytes_split n (c + 12) (N - c - 12) bs (by omega) $$ H with ⟨H1, H2⟩
  rw [show c + 12 + (N - c - 12) = N by omega]
  icases WNear.Binary.U128From.memBytes_split n N 8 (bs.drop (N - c - 12)) (by simp; omega) $$ H2 with ⟨H2, H3⟩
  icases WNear.Binary.U128From.memBytes_split n (N + 8) 4 ((bs.drop (N - c - 12)).drop 8) (by simp; omega) $$ H3 with ⟨H3, H4⟩
  iexists _, _, _, _
  rw [show N + 8 + 4 = N + 12 by omega]
  iframe H1 H2 H3 H4
  ipureintro
  refine ⟨rfl, ?_⟩
  simp; omega

end Split

/-- The split of 580: from the new cell's address on, up to the branch to the
end of the walk (`br 12`). Its own theorem so that `f580_one`'s proof term
stays shallow enough for the kernel. -/
abbrev splitCode : List Instr :=
  [Instr.local_get 10, Instr.i32_const 4294967288, Instr.i32_binop IBinOp.add, Instr.local_tee 9, Instr.local_get 10,
      Instr.i32_relop IRelOp.gt_u, Instr.br_if 4, Instr.local_get 11, Instr.local_get 9, Instr.i32_binop IBinOp.sub,
      Instr.local_tee 2, Instr.local_get 11, Instr.i32_relop IRelOp.gt_u, Instr.br_if 5, Instr.local_get 2,
      Instr.call 574, Instr.local_get 9, Instr.i32_const 0, Instr.store NumType.i32 none { align := 2, offset := 8 },
      Instr.local_get 9, Instr.i64_const 0, Instr.store NumType.i64 none { align := 2, offset := 0 }, Instr.local_get 9,
      Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 4294967292,
      Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 0 },
      Instr.block BlockType.empty
        [Instr.local_get 1, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.local_tee 2,
          Instr.i32_const 4294967292, Instr.i32_binop IBinOp.and, Instr.local_tee 10, Instr.i32_eqz, Instr.br_if 0,
          Instr.i32_const 0, Instr.local_get 10, Instr.local_get 2, Instr.i32_const 2, Instr.i32_binop IBinOp.and,
          Instr.select none, Instr.local_tee 2, Instr.i32_eqz, Instr.br_if 0, Instr.local_get 2, Instr.local_get 2,
          Instr.load NumType.i32 none { align := 2, offset := 4 }, Instr.i32_const 3, Instr.i32_binop IBinOp.and,
          Instr.local_get 9, Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 4 }],
      Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 4 }, Instr.i32_const 3,
      Instr.i32_binop IBinOp.and, Instr.local_get 1, Instr.i32_binop IBinOp.or,
      Instr.store NumType.i32 none { align := 2, offset := 4 }, Instr.local_get 1, Instr.local_get 1,
      Instr.load NumType.i32 none { align := 2, offset := 8 }, Instr.i32_const 4294967294, Instr.i32_binop IBinOp.and,
      Instr.store NumType.i32 none { align := 2, offset := 8 }, Instr.local_get 1, Instr.local_get 1,
      Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 3, Instr.i32_binop IBinOp.and,
      Instr.local_get 9, Instr.i32_binop IBinOp.or, Instr.local_tee 2,
      Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.local_get 2, Instr.i32_const 2,
      Instr.i32_binop IBinOp.and, Instr.i32_eqz, Instr.br_if 12, Instr.local_get 1, Instr.local_get 2,
      Instr.i32_const 4294967293, Instr.i32_binop IBinOp.and, Instr.store NumType.i32 none { align := 2, offset := 0 },
      Instr.local_get 9, Instr.local_get 9, Instr.load NumType.i32 none { align := 2, offset := 0 }, Instr.i32_const 2,
      Instr.i32_binop IBinOp.or, Instr.store NumType.i32 none { align := 2, offset := 0 }, Instr.br 12]

section SplitSpec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What the split leaves, the new cell `N = A - 8` (its word 0 still without
`ALLOCATED`). -/
def splitRes (n : Nat) (c nx npv A : UInt32) (lst : Bool) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ c.toNat ] (UInt32.ofNat (A.toNat - 8)) ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
    (∃ b0 : List UInt8, ⌜b0 = bs.take ((UInt32.ofNat (A.toNat - 8)).toNat - c.toNat - 12)⌝ ∗ n ↦[wms][ c.toNat + 12 ] b0) ∗
    n ↦[i32][ (UInt32.ofNat (A.toNat - 8)).toNat ] w0 nx lst ∗ n ↦[i32][ (UInt32.ofNat (A.toNat - 8)).toNat + 4 ] c ∗
    (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') ∗
    nextW n nx (npv &&& 3 ||| (UInt32.ofNat (A.toNat - 8))) lst)

set_option maxHeartbeats 4000000 in
theorem split_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (inst : Nat) (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (a574 : Nat)
    (h574 : mi.funcAddrs[574]? = some a574) (ty574 : FuncType)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot pd pv c nx npv A : UInt32) (lst : Bool) (bs : List UInt8)
    (hw1 : 1 ≤ w.toNat) (hc0 : 1 ≤ c.toNat) (hnx4 : nx &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32)
    (hbs : bs.length + 12 + c.toNat = nx.toNat)
    (hA4 : A.toNat % 4 = 0) (hA80 : c.toNat + 80 ≤ A.toNat) (hAw : A.toNat + 4 * w.toNat ≤ nx.toNat) :
    a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ inst ↪[inst] mi ∗
      credits Cg (100 * cfg.regularOpCost + R) ∗
      n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗ n ↦[wms][ c.toNat + 12 ] bs ∗
      nextW n nx npv lst ∗
      (∀ l2 : UInt32, credits Cg R -∗ splitRes n c nx npv A lst bs -∗
        Φ.br 12 [] ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
          .i32 (al + 4294967295), .i32 0, .i32 (UInt32.ofNat (A.toNat - 8)), .i32 nx, .i32 nx, .i32 (nx - w <<< 2),
          .i32 (c + 8 + 8 + 64)], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 0, .i32 (0 - al),
          .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 A, .i32 nx, .i32 (nx - w <<< 2),
          .i32 (c + 8 + 8 + 64)], inst, mi⟩ [] splitCode Φ := by
  iintro ⟨#H574, #Hi, Hc, H0, H8, Hd, Hn, HΦ⟩
  have hm : Hold (w0 nx lst &&& 4294967292 = nx) := ⟨w0_mask nx lst hnx4⟩
  have eN : (UInt32.ofNat (A.toNat - 8)).toNat = A.toNat - 8 := by
    have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hsub : Hold (A + 4294967288 = UInt32.ofNat (A.toNat - 8)) := ⟨by
    apply UInt32.toNat_inj.mp; rw [eN, UInt32.toNat_add]; simp; omega⟩
  have hb4 := Hold.mk (gt_false (UInt32.ofNat (A.toNat - 8)) A (by omega))
  have eS : (nx - (UInt32.ofNat (A.toNat - 8))).toNat = nx.toNat - (A.toNat - 8) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega), eN]
  have hb5 := Hold.mk (gt_false (nx - (UInt32.ofNat (A.toNat - 8))) nx (by omega))
  have hN3 : Hold ((UInt32.ofNat (A.toNat - 8)) &&& 3 = 0) := ⟨and3_of_mod4 _ (by omega)⟩
  have h574' : 8 ≤ (nx - (UInt32.ofNat (A.toNat - 8))).toNat := by omega
  have hs1 : c.toNat + 12 ≤ (UInt32.ofNat (A.toNat - 8)).toNat := by omega
  have hs2 : (UInt32.ofNat (A.toNat - 8)).toNat + 12 ≤ c.toNat + 12 + bs.length := by omega
  have hNA : (UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat := by omega
  have hnx0 : Hold (nx ≠ 0) := ⟨by intro h; subst h; simp at hcnx⟩
  have hF : Hold ((UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat ∧ (UInt32.ofNat (A.toNat - 8)).toNat + 12 ≤ nx.toNat) := ⟨⟨hNA, by omega⟩⟩
  clear eN eS hNA hA4 hA80 hAw
  icases split_data n c.toNat (UInt32.ofNat (A.toNat - 8)).toNat bs hs1 hs2 $$ Hd with
    ⟨%b0, %b8, %b4, %br, %⟨hb0, hb8, hb4', hbr⟩, Hd, HN8, HN4, HNr⟩
  ihave Hd : (∃ b0 : List UInt8, ⌜b0 = bs.take ((UInt32.ofNat (A.toNat - 8)).toNat - c.toNat - 12)⌝ ∗
      n ↦[wms][ c.toNat + 12 ] b0) $$ [Hd]
  · iexists b0; iframe Hd; ipureintro; exact hb0
  clear hb0
  have hH : Hold (br.length + (UInt32.ofNat (A.toNat - 8)).toNat + 12 = c.toNat + 12 + bs.length ∧ 8 ≤ (nx - (UInt32.ofNat (A.toNat - 8))).toNat) := ⟨⟨hbr, h574'⟩⟩
  clear hs1 hs2 hbr h574'
  simp only [splitCode]
  mstep; mstep; mstep
  rw [show A + 4294967288 = UInt32.ofNat (A.toNat - 8) from hsub.get]
  mstep; mstep; mstep
  mnot_taken hb4.get
  mstep; mstep; mstep; mstep; mstep; mstep
  mnot_taken hb5.get
  clear hb4 hb5
  mstep
  mcall (f574_spec cfg lim (d + 1) ty574 hr574 inst mi Cg (nx - (UInt32.ofNat (A.toNat - 8))) hH.get.2)
    with (simp [activationGas, entryLocals, f574, hp574]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs

  mstep; mstep; mstep [HN4]
  mstep; mstep; mstep [HN8]
  icases WNear.Binary.U128From.memBytes_split n (UInt32.ofNat (A.toNat - 8)).toNat 4 _ (by decide) $$ HN8 with ⟨HNa, HNb⟩
  rw [i64_zero_lo, i64_zero_hi]
  mstep; mstep; mstep [H0]; mstep; mstep
  rw [show w0 nx lst &&& 4294967292 = nx from hm.get]
  mstep [HNa]
  mstep; mstep; mstep [H0]; mstep; mstep; mstep
  rw [show w0 nx lst &&& 4294967292 = nx from hm.get]
  mstep; mstep
  mstep_not_taken with (exact eqz_false nx hnx0.get)
  mstep; mstep; mstep; mstep; mstep
  rw [w0_and2 nx lst hnx4]
  iapply mwpi_cons
  iapply WNear.Binary.AllocNewCell.mwpi_select_ite
  isplitl [Hc]; · iexact Hc
  isplitr; · ipureintro; exact ⟨rfl, by omega⟩
  inext; iintro Hc
  ihave HN4r : (∃ bs' : List UInt8, ⌜bs'.length = nx.toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') $$ [HN4 HNr]
  · iexists bytes32 0 ++ br
    obtain ⟨h1, h2⟩ := hF.get
    obtain ⟨h3, h4⟩ := hH.get
    isplitr
    · ipureintro; simp [bytes32]; omega
    iapply WNear.Binary.AllocNewCell.memBytes_addr (show (UInt32.ofNat (A.toNat - 8)).toNat + 8 = A.toNat by omega)
    iapply WNear.Binary.U128From.memBytes_join n ((UInt32.ofNat (A.toNat - 8)).toNat + 8) 4 _ _ (by simp [bytes32])
    rw [show (UInt32.ofNat (A.toNat - 8)).toNat + 8 + 4 = (UInt32.ofNat (A.toNat - 8)).toNat + 12 by omega]
    iframe HN4 HNr
  clear hF hH hb8 hb4'
  cases lst
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    mctrl_norm
    rw [nextW_false]
    mstep; mstep
    mstep_not_taken with (exact eqz_false nx hnx0.get)
    mstep; mstep; mstep [Hn]; mstep; mstep; mstep; mstep; mstep [Hn]
    mstep; mstep; mstep [HNb]; mstep; mstep; mstep; mstep
    rw [zero_and_or]
    mstep [HNb]
    mstep; mstep; mstep [H8]; mstep; mstep
    rw [zero_and2]
    mstep [H8]
    rw [show w0 nx false = nx from rfl]
    mstep; mstep; mstep [H0]; mstep; mstep; mstep; mstep; mstep
    rw [v_false nx (UInt32.ofNat (A.toNat - 8)) hnx4]
    mstep [H0]
    mstep; mstep; mstep
    rw [and2_zero (UInt32.ofNat (A.toNat - 8)) (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep
    iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, eqz_true 0 rfl⟩
    simp only [List.reverse_nil, Post.mseq_br]
    mcredits R
    iapply HΦ $$ %_ Hc
    iunfold splitRes
    rw [nextW_false, show w0 nx false = nx from rfl]
    iframe H0 H8 Hd HNa HNb HN4r Hn
  · simp only [ite_true, show (2 : UInt32) ≠ 0 by decide, ite_false]
    mctrl_norm
    mstep; mstep
    mstep_taken with (exact eqz_true _ rfl)
    mstep; mstep; mstep [HNb]; mstep; mstep; mstep; mstep
    rw [zero_and_or]
    mstep [HNb]
    mstep; mstep; mstep [H8]; mstep; mstep
    rw [zero_and2]
    mstep [H8]
    rw [show w0 nx true = nx ||| 2 from rfl]
    mstep; mstep; mstep [H0]; mstep; mstep; mstep; mstep; mstep
    rw [v_true nx (UInt32.ofNat (A.toNat - 8)) hnx4 (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep [H0]
    mstep; mstep; mstep
    rw [or2_and2]
    mstep
    mstep_not_taken with (exact eqz_false 2 (by decide))
    mstep; mstep; mstep; mstep
    rw [or2_clear (UInt32.ofNat (A.toNat - 8)) (show (UInt32.ofNat (A.toNat - 8)) &&& 3 = 0 from hN3.get)]
    mstep [H0]
    mstep; mstep; mstep [HNa]; mstep; mstep; mstep [HNa]
    iapply mwpi_br
    mcredits R
    iapply HΦ $$ %_ Hc
    iunfold splitRes
    rw [nextW_true, nextW_true, show w0 nx true = nx ||| 2 from rfl]
    iframe H0 H8 Hd HNa HNb HN4r

end SplitSpec

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- `alloc_first_fit` (580) on a free list of one cell `c` without `CAN_MERGE`
and with `next_free = 0` (the list a fresh chunk leaves, and the one every
allocation leaves while nothing is freed). -/
theorem f580_one (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a572 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (w al slot pd pv idx c nx npv : UInt32) (lst : Bool) (bs : List UInt8) (k : Nat)
    (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (hc0 : 1 ≤ c.toNat) (hc4 : c &&& 3 = 0) (hnx4 : nx &&& 3 = 0)
    (hcnx : c.toNat + 12 ≤ nx.toNat) (hnx : nx.toNat + 65536 ≤ 2 ^ 32)
    (hbs : bs.length + 12 + c.toNat = nx.toNat) :
    a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗
      a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ a578 ↪[wf] FuncInst.wasm mi.types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 w, .i32 al, .i32 slot, .i32 pd, .i32 pv]⌝ ∗
          oneRes n slot c c nx npv lst bs pv idx ta a578))
        (fun _ => 300 * cfg.regularOpCost)
        (post1 n w al slot c nx npv lst bs pv idx ta a578) := by
  iintro ⟨#H572, #H576, #H574, #H578, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HR⟩ Hc
  subst hargs
  iunfold oneRes at HR
  icases HR with ⟨Hs, H0, H8, Hd, Hn, Hvt⟩
  iunfold vt at Hvt
  icases Hvt with ⟨Hv, Ht⟩
  simp only [f580]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep [Hs]
  mstep
  mstep
  mstep
  have hal0 : al ≠ 0 := by intro h; subst h; simp at hal; have := Nat.one_le_two_pow (n := k); omega
  rw [flag_zero al hal0]
  have hcne : c ≠ 0 := by intro h; subst h; simp at hc0
  rw [show 284 * cfg.regularOpCost + R = cfg.regularOpCost + (283 * cfg.regularOpCost + R) by omega]
  iapply mwpi_cons
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := 283 * cfg.regularOpCost + R) .empty _
    (fun X g => iprop(⌜X = []⌝ ∗
      ((⌜g = fr inst mi w al slot pd pv c 0 0 0 0 0⌝ ∗ credits Cg (283 * cfg.regularOpCost + R) ∗
          oneRes n slot c c nx npv lst bs pv idx ta a578) ∨
       (∃ l9 l10 l11 l12 l13 : UInt32, ⌜g = fr inst mi w al slot pd pv 0 l9 l10 l11 l12 l13 ∧
          (¬ fits w c nx ∨ (¬ canSplit w al c nx ∧ ¬ aligned al c))⌝ ∗
          credits Cg (100 * cfg.regularOpCost + R) ∗ oneRes n slot 0 c nx npv lst bs pv idx ta a578))))
    rfl
  isplitr
  · imodintro
    iintro %X %l ⟨%hX, HI⟩
    subst hX
    icases HI with (⟨%hg, Hc, HR⟩ | ⟨%l9, %l10, %l11, %l12, %l13, %⟨hg, hfail⟩, Hc, HR⟩)
    · rw [hg]; simp only [fr]
      iunfold oneRes at HR
      icases HR with ⟨Hs, H0, H8, Hd, Hn, Hvt⟩
      iunfold vt at Hvt
      icases Hvt with ⟨Hv, Ht⟩
      mstep; mstep
      mstep_not_taken
      mstep; mstep; mstep
      rw [show 280 * cfg.regularOpCost + R = cfg.regularOpCost + (279 * cfg.regularOpCost + R) by omega]
      iapply mwpi_loop_pin (Cg := Cg) (R := 279 * cfg.regularOpCost + R) .empty _
        iprop(credits Cg (279 * cfg.regularOpCost + R) ∗
          n ↦[i32][ slot.toNat ] c ∗ n ↦[i32][ c.toNat ] w0 nx lst ∗ n ↦[i32][ c.toNat + 8 ] 0 ∗
          n ↦[wms][ c.toNat + 12 ] bs ∗ nextW n nx npv lst ∗ n ↦[i32][ pv.toNat + 16 ] idx ∗
          ta ↦[wt][ idx.toNat ] Ref.func a578) rfl
      isplitr
      swap
      · isplitl [Hc]; · iexact Hc
        inext; iintro Hc; iframe Hc Hs H0 H8 Hd Hn Hv Ht
      imodintro
      iintro ⟨Hc, Hs, H0, H8, Hd, Hn, Hv, Ht⟩
      mstep; mstep; mstep [H8]; mstep; mstep; mstep
      mstep_not_taken
      mstep; mstep; mstep; mstep; mstep
      mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg w (by omega))
        with (simp [activationGas, entryLocals, f572, hp572]; omega)
      · ipureintro; trivial
      icases HQ with %hrs
      subst hrs
      mstep; mstep
      have hm := w0_mask nx lst hnx4
      mcall (f576_spec cfg lim (d + 1) ty576 hr576 inst mi n hn Cg c (w0 nx lst) (by omega)
          (by rw [hm]; omega)) using [H0]
        with (simp [activationGas, entryLocals, f576, hp576]; omega)
      · iframe H0
      icases HQ with ⟨%hrs, H0⟩
      subst hrs
      rw [hm]
      mstep
      mstep
      have e1 := sub8_toNat nx c (by omega)
      have e2 := WNear.Binary.AllocNewCell.shl2_toNat w (by omega)
      by_cases hfit : fits w c nx
      swap
      · iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, lt_true _ _ (by unfold fits szN at hfit; rw [e1, e2]; omega)⟩
        simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, List.nil_append]
        clear e1 e2
        mpay
        mstep; mstep; mstep [H8]; mstep; mstep [Hs]
        iapply mwpi_br
        simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
        iapply pure_pay_intro'
        isplitl [Hc]; · iexact Hc
        isplitr; · ipureintro; exact ⟨by simp, by omega⟩
        inext; iintro Hc
        isplitr; · ipureintro; rfl
        iright
        iexists c + 8, w <<< 2, 0, 0, 0
        isplitr; · ipureintro; exact ⟨rfl, Or.inl hfit⟩
        mcredits (100 * cfg.regularOpCost + R)
        iunfold oneRes
        iunfold vt
        iframe Hc Hs H0 H8 Hd Hn Hv Ht
      have hnf := lt_false (nx - c + 4294967288) (w <<< 2) (by unfold fits szN at hfit; rw [e1, e2]; omega)
      have hfit' : 4 * w.toNat ≤ nx.toNat - c.toNat - 8 := hfit
      have e3 : (nx - w <<< 2).toNat = nx.toNat - 4 * w.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, e2]; omega), e2]; omega
      have hgt := gt_false (nx - w <<< 2) nx (by rw [e3]; omega)
      clear e1 e2 hfit'
      mstep_not_taken with (exact hnf)
      clear hnf
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep; mstep [H0]; mstep; mstep
      rw [hm]
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with (exact hgt)
      clear hgt
      mstep
      mstep_not_taken
      mstep; mstep; mstep; mstep [Hv]
      iapply mwpi_cons
      iapply (Borrow.mwpi_call_indirect' (ty := 13) (t := 0) (ta := ta) (idx := idx) (a := a578)
        (type := mi.types[13]!) (inst := inst) (mi := mi) (code := f578) [.i32 pd, .i32 w])
      isplitr
      · iapply (f578_spec cfg lim (d + 1) mi.types[13]! hrt578 inst mi Cg pd w)
      isplitr; · iexact H578
      isplitr; · iexact Hi
      isplitl [Ht]; · iexact Ht
      isplitr; · ipureintro; exact ⟨rfl, hta, rfl, by simp [hty578], hd⟩
      isplitl [Hc]; · iexact Hc
      isplitr; · ipureintro; mstep_norm_full; omega
      isplitr; · ipureintro; rfl
      inext
      iintro %rs Ht Hc %hrs
      subst hrs
      mctrl_norm
      mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg 16 (by decide))
        with (simp [activationGas, entryLocals, f572, hp572]; omega)
      · ipureintro; trivial
      icases HQ with %hrs
      subst hrs
      rw [show (16 : UInt32) <<< 2 = 64 by decide]
      have e16 : (c + 8 + 8).toNat = c.toNat + 16 := by
        rw [UInt32.toNat_add, UInt32.toNat_add]; simp; omega
      have e80 : (c + 8 + 8 + 64).toNat = c.toNat + 80 := by
        rw [UInt32.toNat_add, e16]; simp; omega
      have e8 : (c + 8).toNat = c.toNat + 8 := by
        rw [UInt32.toNat_add]; simp; omega
      have hb1 := lt_false (c + 8 + 8) (c + 8) (by omega)
      have hb2 := lt_false (c + 8 + 8 + 64) (c + 8 + 8) (by omega)
      have eA : (nx - w <<< 2 &&& 0 - al).toNat = aN nx w al := by
        rw [and_neg_toNat (nx - w <<< 2) al k hal hk, e3]; rfl
      clear e16 e3
      mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with (exact hb1)
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with (exact hb2)
      clear hb1 hb2
      mstep; mstep; mstep; mstep; mstep; mstep
      by_cases hsplit : canSplit w al c nx
      swap
      · have hb := gt_true (c + 8 + 8 + 64) (nx - w <<< 2 &&& 0 - al) (by
          unfold canSplit at hsplit; rw [e80, eA]; omega)
        clear eA e80
        iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, hb⟩
        clear hb
        simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, List.nil_append]
        mpay
        mstep; mstep; mstep; mstep
        by_cases hali : aligned al c
        · have hb := eqz_and_true (c + 8) al k hal hk (by rw [e8]; exact hali)
          clear e8
          iapply mwpi_cons
          iapply mwpi_br_if_taken'
          isplitr
          · ipureintro; exact ⟨rfl, hb⟩
          clear hb
          simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, List.nil_append]
          mpay
          simp only [Post.mloop_normal, List.nil_append]
          mpay
          mstep; mstep; mstep [H8]; mstep; mstep; mstep [Hs]
          mstep; mstep
          mstep; mstep; mstep [H0]; mstep; mstep; mstep [H0]
          mstep; mstep; mstep; mstep
          mstep
          rw [htype]
          mcredits R
          iframe Hc
          iunfold post1
          iexists c + 8
          isplitr; · ipureintro; rfl
          iunfold vt
          iframe Hv Ht
          iright; ileft
          rw [show (UInt32.ofNat 0 &&& 4294967292 : UInt32) = 0 by decide]
          iframe Hs H0 H8 Hd Hn
          ipureintro; exact ⟨rfl, hfit, hsplit, hali⟩
        · have hb := eqz_and_false (c + 8) al k hal hk (by rw [e8]; exact hali)
          clear e8
          mstep_not_taken with (exact hb)
          clear hb
          mstep; mstep; mstep [H8]; mstep; mstep [Hs]
          iapply mwpi_br
          simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
          iapply pure_pay_intro'
          isplitl [Hc]; · iexact Hc
          isplitr; · ipureintro; exact ⟨by simp, by omega⟩
          inext; iintro Hc
          isplitr; · ipureintro; rfl
          iright
          iexists c + 8, nx - w <<< 2 &&& 0 - al, nx, nx - w <<< 2, c + 8 + 8 + 64
          isplitr; · ipureintro; exact ⟨rfl, Or.inr ⟨hsplit, hali⟩⟩
          mcredits (100 * cfg.regularOpCost + R)
          iunfold oneRes
          iunfold vt
          iframe Hc Hs H0 H8 Hd Hn Hv Ht
      have hb := gt_false (c + 8 + 8 + 64) (nx - w <<< 2 &&& 0 - al) (by
        have h := hsplit; unfold canSplit at h; rw [e80, eA]; omega)
      have hAm4 := aN_mod4 nx w al k hal (toNat_mod4 nx hnx4)
      have hfit' : 4 * w.toNat ≤ nx.toNat - c.toNat - 8 := hfit
      have hsplit' : c.toNat + 80 ≤ aN nx w al := hsplit
      have hAle : aN nx w al + 4 * w.toNat ≤ nx.toNat := by
        unfold aN; have := Nat.mod_le (nx.toNat - 4 * w.toNat) al.toNat; omega
      generalize hAd : (nx - w <<< 2 &&& 0 - al) = A at *
      clear e80 hAd
      mstep_not_taken with (exact hb)
      clear hb
      have hF : Hold (A.toNat = aN nx w al ∧ A.toNat % 4 = 0 ∧ c.toNat + 80 ≤ A.toNat ∧
          A.toNat + 4 * w.toNat ≤ nx.toNat) := ⟨⟨eA, by omega, by omega, by omega⟩⟩
      clear eA hAm4 hfit' hsplit' hAle
      iapply split_spec cfg lim d _ inst mi n hn a574 h574 ty574 hp574 hr574 hd Cg
        (40 * cfg.regularOpCost + R) w al slot pd pv c nx npv A lst bs hw1 hc0 hnx4 hcnx hnx hbs
        hF.get.2.1 hF.get.2.2.1 hF.get.2.2.2
      isplitr; · iexact H574
      isplitr; · iexact Hi
      isplitl [Hc]; · mcredits (100 * cfg.regularOpCost + (40 * cfg.regularOpCost + R)); iexact Hc
      iframe H0 H8 Hd Hn
      iintro %l2 Hc HS
      simp only [Post.mblock_br_succ, Post.mseq_br, Post.mloop_br_succ, Post.mblock_br_zero, List.nil_append]
      mpay
      iunfold splitRes at HS
      icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
      mstep; mstep; mstep [HNa]; mstep; mstep; mstep [HNa]
      mstep; mstep; mstep; mstep
      mstep
      obtain ⟨hA1, -, hA80, -⟩ := hF.get
      clear hF
      have eNN : (UInt32.ofNat (A.toNat - 8)).toNat = A.toNat - 8 := by
        have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
      have hA8 : UInt32.ofNat (A.toNat - 8) + 8 = A := by
        apply UInt32.toNat_inj.mp; have := A.toNat_lt; rw [UInt32.toNat_add, eNN]; simp; omega
      have hAm8 : A - 8 = UInt32.ofNat (A.toNat - 8) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega), eNN]; simp
      rw [htype, hA8]
      mcredits R
      iframe Hc
      iunfold post1
      iexists A
      isplitr; · ipureintro; rfl
      iunfold vt
      iframe Hv Ht
      iright; iright
      rw [hAm8]
      icases Hd with ⟨%b0, %hb0, Hd⟩
      rw [eNN] at hb0
      rw [eNN]
      ihave HNb := WNear.Binary.AllocNewCell.memBytes_addr (show A.toNat - 8 + 4 = A.toNat - 4 by omega) $$ HNb
      ihave Hd := WNear.Binary.AllocNewCell.memBytes_eq (show b0 = bs.take (A.toNat - 8 - c.toNat - 12) by
        rw [hb0]; congr 1) $$ Hd
      iframe Hs H0 H8 Hd HNa HNb HN4r Hn
      ipureintro; exact ⟨hA1, hfit, hsplit⟩
    · rw [hg]; simp only [fr]
      mstep; mstep
      mstep_taken
      mloop_norm
      mstep
      rw [htype]
      mcredits R
      iframe Hc
      iunfold post1
      iexists 0
      isplitr; · ipureintro; rfl
      iunfold oneRes at HR
      icases HR with ⟨Hs, H0, H8, Hd, Hn, Hvt⟩
      iframe Hvt
      ileft
      iframe Hs H0 H8 Hd Hn
      ipureintro; exact ⟨rfl, hfail⟩
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  isplitr; · ipureintro; rfl
  ileft
  iunfold oneRes
  iunfold vt
  iframe Hc Hs H0 H8 Hd Hn Hv Ht
  ipureintro; rfl

end WNear.Binary.AllocFirstFit
