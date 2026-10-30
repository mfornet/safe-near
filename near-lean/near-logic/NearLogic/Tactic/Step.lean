import NearLogic.Rules.Pure
import NearLogic.Rules.Memory
import Lean

/-!
# `mstep`: stepping through straight-line metered code

`mstep` runs the first instruction of a goal `… ⊢ mwpi cfg lim d f vs (i :: es) Φ`
in the iris proof mode. It works with the instruction rules of
`NearLogic/Rules/{Pure,Memory}.lean` restated in a *flexible* form
(`mwpi_*'` below) that

* takes `credits Cg K` for any `K`, with the side condition
  `cfg.regularOpCost ≤ K`, and gives `credits Cg (K - cfg.regularOpCost)` back,
  so no amount `R` has to be named or rearranged;
* reads its operands off the reversed stack, `vs.reverse = top :: … :: rest`,
  and pushes its results on `rest.reverse`, so the stack need not be in the
  syntactic shape `vs ++ [a, b]` (a list literal, or any `xs ++ [..]`, works);
* collects the remaining side conditions (local or global lookup, memory
  address, widths) in one pure premise, after the resources, so the
  unknowns in them are fixed by the time they are proved.

## Interface

* `mstep` — a pure instruction (`nop`, `drop`, `i32/i64.const`,
  `local.get/set/tee`, `i32/i64.eqz`, `i32/i64` unop/binop/relop, `cvt`).
* `mstep [Hm]` — an instruction on a resource named `Hm` in the iris
  context: `load`/`store` (`Hm : n ↦[wms][ a + offset ] bs`), `global.get/set`
  (`Hm : g ↦[wg] gi`), `memory.size` (`Hm : n ↦[wmlength] len`).
* `mstep with tac`, `mstep [Hm] with tac` — try `tac` (which must close it)
  first on each side condition.

## Naming convention

The credits live in the iris hypothesis `Hc` (the user introduces it as `Hc`
before the first `mstep`); after each step `Hc : credits Cg (K - cost)`. The
resource `Hm` of a memory step is consumed and reintroduced under the same
name, with its new contents (a store leaves
`Hm : n ↦[wms][ …] storeBytes v w`, `w` the store width). Other hypotheses are
untouched.

After each step the goal is normalised with `mstep_norm` (stacks back to list
literals, `Post.mseq_normal`, load/store widths). On the last instruction of
the fragment (`es = []`) `mwpi_cons` is skipped, so the goal is the
postcondition itself, `Φ.normal vs' f'`.

Each step leaves `credits Cg (K - c)`; `mstep_norm` turns `k * c + R - c` into
`(k - 1) * c + R` (so `8 * c + R` is `R` after eight steps); otherwise the
amount reads `K - c - … - c`, which omega handles, and `mcredits R` turns `Hc`
into `credits Cg R` for any `R` no larger.

Side conditions are closed by `mstep_side`: `trivial`, `assumption`, `rfl`
(also how mvars such as the value of a `local.get` or the result of an
`ibinop32` get fixed), stack normalisation followed by `rfl`, `omega`, and
`simp_all` with the width definitions followed by `omega`, `mlocals`, and
`mstep_norm_full` followed by `omega`. When it fails, `mstep` fails, with the
goal it could not prove; pass `with tac` or step manually with the `mwpi_*'`
rules.

## Full mode (with `NearLogic.Tactic.Control` imported)

`mstep` has two extension points, `mstep_ext` (instructions it has no rule
for) and `mstep_post` (what runs after a step); `NearLogic/Tactic/Control.lean`
fills both. Without it, `mstep` behaves as described above. With it:

* `load`/`store` use `mwpi_load_at'`/`mwpi_store_at'`: the points-to `Hm` is
  taken at its own address `addr` and comes back at it, and the effective
  address is equated to it by `maddr` — so `i32.const 0` with offset `k`
  matches `n ↦[i32][ k ]`, and `(x + k).toNat`, `(x - k).toNat + j` match
  `x.toNat + k'` given a no-overflow hypothesis in context;
* after each step the goal is normalised with `mstep_norm_full` (and the
  block postconditions), and payments are made; see Control.lean;
* control instructions, the empty fragment, and `mcall` are stepped.

## Normal forms and side-condition tactics (usable on their own)

* `mstep_norm_full`: `mstep_norm` and credit folding (`k * c + R - j * c`,
  sums of multiples of `c`, `K - a - b`, literal arithmetic), literal frames
  after `local.set`/`local.tee` (`Frame.withLocals_mk`, `set!_toArray`),
  `entryLocals` of a function constant to a literal array (the
  `reduceFuncLocals` simproc), `activationGas c #[..]` to `m * c`,
  `List.take`/`drop`/`length`/indexing of literals, `loadValue` (unpacked
  `i32`/`i64`), `decodeLE (bytes32 w)`, `storeBytes (.i32 w) 4 = bytes32 w`,
  `Numeric.bool true/false`, `UInt32.toNat` of literals.
* `mlocals`: `f.locals[j]? = some ?v` after `set!`s (literal or symbolic
  arrays, bounds by `omega`) or on `entryLocals`.
* `maddr`: an address equation, by normalising literals, or by `omega` after
  `UInt32.toNat_add`/`_sub`/`_mul` and the bounds `x.toNat < 2 ^ 32`
  (`muint_bounds`).
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Stacks read from the top -/

theorem stack_top1 {vs rest : List Value} {x : Value} (h : vs.reverse = x :: rest) :
    vs = rest.reverse ++ [x] := by
  rw [← List.reverse_reverse vs, h]; simp

theorem stack_top2 {vs rest : List Value} {x y : Value} (h : vs.reverse = y :: x :: rest) :
    vs = rest.reverse ++ [x, y] := by
  rw [← List.reverse_reverse vs, h]; simp

/-! ## Credit amounts `k * c + R` after a step -/

theorem mul_add_sub_self (k c R : Nat) (h : 1 ≤ k) : k * c + R - c = (k - 1) * c + R := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel (n := j) (m := 1), Nat.succ_mul]; omega

theorem mul_sub_self (k c : Nat) (h : 1 ≤ k) : k * c - c = (k - 1) * c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel (n := j) (m := 1), Nat.succ_mul]; omega

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- Credits for a step out of any amount `K` that covers its cost `c`. -/
theorem credits_flex {c : Nat} {S A : Prop} {X W : IProp GF}
    (h : S → A → credits Cg (c + (K - c)) ∗ X ⊢ W) :
    credits Cg K ∗ ⌜S ∧ c ≤ K ∧ A⌝ ∗ X ⊢ W := by
  iintro ⟨Hc, %⟨hS, hK, hA⟩, HX⟩
  iapply h hS hA
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  · iexact HX

/-- `credits` can be weakened to any smaller amount. -/
theorem credits_le {C n m : Nat} : credits (GF := GF) C n ∗ ⌜m ≤ n⌝ ⊢ credits C m := by
  iintro ⟨Hc, %h⟩
  iapply credits_mono h $$ Hc

/-! ### Pure instructions -/

local notation "c₀" => cfg.regularOpCost

theorem mwpi_nop' :
    credits Cg K ∗ ⌜True ∧ c₀ ≤ K ∧ True⌝ ∗ ▷ (credits Cg (K - c₀) -∗ Φ.normal vs f)
      ⊢ mwpi cfg lim d f vs [.nop] Φ :=
  credits_flex fun _ _ => mwpi_nop

theorem mwpi_drop' {rest : List Value} {v : Value} :
    credits Cg K ∗ ⌜vs.reverse = v :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.drop] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_drop v

theorem mwpi_i32_const' {n : UInt32} :
    credits Cg K ∗ ⌜True ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (vs ++ [.i32 n]) f)
      ⊢ mwpi cfg lim d f vs [.i32_const n] Φ :=
  credits_flex fun _ _ => mwpi_i32_const n

theorem mwpi_i64_const' {n : UInt64} :
    credits Cg K ∗ ⌜True ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (vs ++ [.i64 n]) f)
      ⊢ mwpi cfg lim d f vs [.i64_const n] Φ :=
  credits_flex fun _ _ => mwpi_i64_const n

theorem mwpi_local_get' {i : Nat} {v : Value} :
    credits Cg K ∗ ⌜True ∧ c₀ ≤ K ∧ f.locals[i]? = some v⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (vs ++ [v]) f)
      ⊢ mwpi cfg lim d f vs [.local_get i] Φ :=
  credits_flex fun _ h => mwpi_local_get i v h

theorem mwpi_local_set' {i : Nat} {rest : List Value} {v : Value} :
    credits Cg K ∗ ⌜vs.reverse = v :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal rest.reverse (f.withLocals (f.locals.set! i v)))
      ⊢ mwpi cfg lim d f vs [.local_set i] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_local_set i v

theorem mwpi_local_tee' {i : Nat} {rest : List Value} {v : Value} :
    credits Cg K ∗ ⌜vs.reverse = v :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [v]) (f.withLocals (f.locals.set! i v)))
      ⊢ mwpi cfg lim d f vs [.local_tee i] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_local_tee i v

theorem mwpi_i32_eqz' {rest : List Value} {a : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i32 (Numeric.bool (a == 0))]) f)
      ⊢ mwpi cfg lim d f vs [.i32_eqz] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_i32_eqz a

theorem mwpi_i64_eqz' {rest : List Value} {a : UInt64} :
    credits Cg K ∗ ⌜vs.reverse = .i64 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i32 (Numeric.bool (a == 0))]) f)
      ⊢ mwpi cfg lim d f vs [.i64_eqz] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_i64_eqz a

theorem mwpi_i32_unop' {op : IUnOp} {rest : List Value} {a : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i32 (Numeric.iunop32 op a)]) f)
      ⊢ mwpi cfg lim d f vs [.i32_unop op] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_i32_unop op a

theorem mwpi_i64_unop' {op : IUnOp} {rest : List Value} {a : UInt64} :
    credits Cg K ∗ ⌜vs.reverse = .i64 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i64 (Numeric.iunop64 op a)]) f)
      ⊢ mwpi cfg lim d f vs [.i64_unop op] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_i64_unop op a

theorem mwpi_i32_binop' {op : IBinOp} {rest : List Value} {a b r : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 b :: .i32 a :: rest ∧ c₀ ≤ K ∧
        Numeric.ibinop32 op a b = .ok r⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i32 r]) f)
      ⊢ mwpi cfg lim d f vs [.i32_binop op] Φ :=
  credits_flex fun hs h => by rw [stack_top2 hs]; exact mwpi_i32_binop op a b r h

theorem mwpi_i64_binop' {op : IBinOp} {rest : List Value} {a b r : UInt64} :
    credits Cg K ∗ ⌜vs.reverse = .i64 b :: .i64 a :: rest ∧ c₀ ≤ K ∧
        Numeric.ibinop64 op a b = .ok r⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [.i64 r]) f)
      ⊢ mwpi cfg lim d f vs [.i64_binop op] Φ :=
  credits_flex fun hs h => by rw [stack_top2 hs]; exact mwpi_i64_binop op a b r h

theorem mwpi_i32_relop' {op : IRelOp} {rest : List Value} {a b : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 b :: .i32 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗
          Φ.normal (rest.reverse ++ [.i32 (Numeric.bool (Numeric.irelop32 op a b))]) f)
      ⊢ mwpi cfg lim d f vs [.i32_relop op] Φ :=
  credits_flex fun hs _ => by rw [stack_top2 hs]; exact mwpi_i32_relop op a b

theorem mwpi_i64_relop' {op : IRelOp} {rest : List Value} {a b : UInt64} :
    credits Cg K ∗ ⌜vs.reverse = .i64 b :: .i64 a :: rest ∧ c₀ ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - c₀) -∗
          Φ.normal (rest.reverse ++ [.i32 (Numeric.bool (Numeric.irelop64 op a b))]) f)
      ⊢ mwpi cfg lim d f vs [.i64_relop op] Φ :=
  credits_flex fun hs _ => by rw [stack_top2 hs]; exact mwpi_i64_relop op a b

theorem mwpi_cvt' {op : CvtOp} {rest : List Value} {a r : Value} :
    credits Cg K ∗ ⌜vs.reverse = a :: rest ∧ c₀ ≤ K ∧ Numeric.cvt op a = .ok r⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal (rest.reverse ++ [r]) f)
      ⊢ mwpi cfg lim d f vs [.cvt op] Φ :=
  credits_flex fun hs h => by rw [stack_top1 hs]; exact mwpi_cvt op a r h

/-! ### Instructions on a resource

Layout: credits, the stack, the resource, the other side conditions, the
continuation (credits first, then the resource). -/

theorem mwpi_load' {t : NumType} {packed : Option Packed} {arg : MemArg} {rest : List Value}
    {a : UInt32} {n : Nat} {bs : List UInt8} :
    credits Cg K ∗ ⌜vs.reverse = .i32 a :: rest⌝ ∗ n ↦[wms][ a.toNat + arg.offset ] bs ∗
      ⌜c₀ ≤ K ∧ f.mi.memAddrs[0]? = some n ∧ bs.length = loadWidth t packed ∧ bs ≠ []⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ n ↦[wms][ a.toNat + arg.offset ] bs -∗
          Φ.normal (rest.reverse ++ [loadValue t packed (Memory.decodeLE bs)]) f)
      ⊢ mwpi cfg lim d f vs [.load t packed arg] Φ := by
  iintro ⟨Hc, %hs, Hb, %⟨hK, hn, hlen, hne⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_load (R := K - c₀) t packed arg a n bs hn hlen hne
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  isplitl [Hb]
  · iexact Hb
  inext
  iintro Hb Hc
  iapply H $$ Hc Hb

theorem mwpi_store' {t : NumType} {bits : Option Nat} {arg : MemArg} {rest : List Value}
    {a : UInt32} {v : Value} {n : Nat} {old : List UInt8} :
    credits Cg K ∗ ⌜vs.reverse = v :: .i32 a :: rest⌝ ∗ n ↦[wms][ a.toNat + arg.offset ] old ∗
      ⌜c₀ ≤ K ∧ f.mi.memAddrs[0]? = some n ∧ old.length = storeWidth t bits ∧ old ≠ []⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ n ↦[wms][ a.toNat + arg.offset ] storeBytes v (storeWidth t bits) -∗
          Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.store t bits arg] Φ := by
  iintro ⟨Hc, %hs, Hb, %⟨hK, hn, hlen, hne⟩, H⟩
  rw [stack_top2 hs]
  iapply mwpi_store (R := K - c₀) t bits arg a v n old hn hlen hne
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  isplitl [Hb]
  · iexact Hb
  inext
  iintro Hb Hc
  rw [hlen]
  iapply H $$ Hc Hb

theorem mwpi_global_get' {g a : Nat} {gi : GlobalInst} :
    credits Cg K ∗ ⌜True⌝ ∗ a ↦[wg] gi ∗ ⌜c₀ ≤ K ∧ f.mi.globalAddrs[g]? = some a⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ a ↦[wg] gi -∗ Φ.normal (vs ++ [gi.value]) f)
      ⊢ mwpi cfg lim d f vs [.global_get g] Φ := by
  iintro ⟨Hc, -, Hg, %⟨hK, ha⟩, H⟩
  iapply mwpi_global_get (R := K - c₀) g a gi ha
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  isplitl [Hg]
  · iexact Hg
  inext
  iintro Hg Hc
  iapply H $$ Hc Hg

theorem mwpi_global_set' {g a : Nat} {gi : GlobalInst} {rest : List Value} {v : Value} :
    credits Cg K ∗ ⌜vs.reverse = v :: rest⌝ ∗ a ↦[wg] gi ∗
      ⌜c₀ ≤ K ∧ f.mi.globalAddrs[g]? = some a⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ a ↦[wg] { gi with value := v } -∗ Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.global_set g] Φ := by
  iintro ⟨Hc, %hs, Hg, %⟨hK, ha⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_global_set (R := K - c₀) g a gi v ha
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  isplitl [Hg]
  · iexact Hg
  inext
  iintro Hg Hc
  iapply H $$ Hc Hg

theorem mwpi_memory_size' {n len : Nat} :
    credits Cg K ∗ ⌜True⌝ ∗ n ↦[wmlength] len ∗ ⌜c₀ ≤ K ∧ f.mi.memAddrs[0]? = some n⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ n ↦[wmlength] len -∗
          Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f)
      ⊢ mwpi cfg lim d f vs [.memory_size] Φ := by
  iintro ⟨Hc, -, Hl, %⟨hK, hn⟩, H⟩
  iapply mwpi_memory_size (R := K - c₀) n len hn
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  isplitl [Hl]
  · iexact Hl
  inext
  iintro Hl Hc
  iapply H $$ Hc Hl

/-! ### Loads and stores at the points-to's own address

The address of the points-to is free (`addr`), fixed by the resource the
step is given, and the effective address is equated to it in a separate
pure premise, `a.toNat + arg.offset = addr`, proved by `maddr` after the
resource is chosen. So a constant address (`i32.const 0`, offset `k`), a
computed one (`(x + k).toNat`) or `(x - k).toNat + j` all match a points-to
stated as `x.toNat + k`, without unifying UInt32 arithmetic; and the
resource comes back at its own address. -/

theorem mwpi_load_at' {t : NumType} {packed : Option Packed} {arg : MemArg} {rest : List Value}
    {a : UInt32} {n addr : Nat} {bs : List UInt8} :
    credits Cg K ∗ ⌜vs.reverse = .i32 a :: rest⌝ ∗ n ↦[wms][ addr ] bs ∗
      ⌜a.toNat + arg.offset = addr⌝ ∗
      ⌜c₀ ≤ K ∧ f.mi.memAddrs[0]? = some n ∧ bs.length = loadWidth t packed ∧ bs ≠ []⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ n ↦[wms][ addr ] bs -∗
          Φ.normal (rest.reverse ++ [loadValue t packed (Memory.decodeLE bs)]) f)
      ⊢ mwpi cfg lim d f vs [.load t packed arg] Φ := by
  iintro ⟨Hc, %hs, Hb, %ha, %hside, H⟩
  subst ha
  iapply mwpi_load'
  iframe Hc Hb
  isplitr
  · ipureintro; exact hs
  isplitr
  · ipureintro; exact hside
  iexact H

theorem mwpi_store_at' {t : NumType} {bits : Option Nat} {arg : MemArg} {rest : List Value}
    {a : UInt32} {v : Value} {n addr : Nat} {old : List UInt8} :
    credits Cg K ∗ ⌜vs.reverse = v :: .i32 a :: rest⌝ ∗ n ↦[wms][ addr ] old ∗
      ⌜a.toNat + arg.offset = addr⌝ ∗
      ⌜c₀ ≤ K ∧ f.mi.memAddrs[0]? = some n ∧ old.length = storeWidth t bits ∧ old ≠ []⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ n ↦[wms][ addr ] storeBytes v (storeWidth t bits) -∗
          Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.store t bits arg] Φ := by
  iintro ⟨Hc, %hs, Hb, %ha, %hside, H⟩
  subst ha
  iapply mwpi_store'
  iframe Hc Hb
  isplitr
  · ipureintro; exact hs
  isplitr
  · ipureintro; exact hside
  iexact H

end Flex

/-! ## Normal forms

Lemmas `mstep_norm_full` (and the side-condition tactics) rewrite with. -/

/-! ### Credit amounts -/

theorem mul_add_sub_mul (k j c R : Nat) (h : j ≤ k) : k * c + R - j * c = (k - j) * c + R := by
  have : j * c ≤ k * c := Nat.mul_le_mul_right c h
  rw [Nat.sub_mul]; omega

theorem mul_add_mul (a b c : Nat) : a * c + b * c = (a + b) * c := (Nat.add_mul a b c).symm

theorem self_add_mul (b c : Nat) : c + b * c = (1 + b) * c := by rw [Nat.add_mul, Nat.one_mul]

theorem mul_add_self (a c : Nat) : a * c + c = (a + 1) * c := by rw [Nat.add_mul, Nat.one_mul]

theorem self_add_self (c : Nat) : c + c = 2 * c := by omega

/-! ### Locals -/

theorem Frame.withLocals_mk (l l' : Array Value) (i : Nat) (m : ModuleInst) :
    (Frame.mk l i m).withLocals l' = ⟨l', i, m⟩ := rfl

theorem set!_toArray {α : Type _} (l : List α) (i : Nat) (v : α) :
    l.toArray.set! i v = (l.set i v).toArray :=
  List.setIfInBounds_toArray l i v

theorem getElem?_set!_self {α : Type _} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set! i v)[i]? = some v := by
  simp [Array.set!, h]

theorem getElem?_set!_ne {α : Type _} (a : Array α) (i j : Nat) (v : α) (h : i ≠ j) :
    (a.set! i v)[j]? = a[j]? := by
  simp [Array.set!, Array.getElem?_setIfInBounds_ne h]

theorem entryLocals_eq (code : Func) (args : List Value) :
    entryLocals code args = args.toArray ++ (code.locals.map ValType.default).toArray := rfl

open Lean Meta in
/-- `Func.locals c`, for `c` a constant whose definition is a structure
literal, to the list literal in it (so `entryLocals f509 [..]` becomes a
literal array). -/
dsimproc_decl reduceFuncLocals (Func.locals _) := fun e => do
  let_expr Func.locals c ← e | return .continue
  unless c.isConst do return .continue
  let e' ← withTransparency .default <| whnf e
  unless e'.isAppOfArity ``List.cons 3 || e'.isAppOfArity ``List.nil 1 do return .continue
  return .visit e'

/-- The value sizes `activationGas` adds up. -/
def actSize (l : List Value) : Nat :=
  (l.map fun v => match v with
    | .i32 _ | .f32 _ => 4
    | _ => 8).sum

theorem actSize_nil : actSize [] = 0 := rfl
theorem actSize_i32 (x : UInt32) (l : List Value) : actSize (.i32 x :: l) = 4 + actSize l := rfl
theorem actSize_f32 (x : UInt32) (l : List Value) : actSize (.f32 x :: l) = 4 + actSize l := rfl
theorem actSize_i64 (x : UInt64) (l : List Value) : actSize (.i64 x :: l) = 8 + actSize l := rfl
theorem actSize_f64 (x : UInt64) (l : List Value) : actSize (.f64 x :: l) = 8 + actSize l := rfl
theorem actSize_ref (r : Ref) (l : List Value) : actSize (.ref r :: l) = 8 + actSize l := rfl

theorem activationGas_toArray (c : Nat) (l : List Value) :
    activationGas c l.toArray = (64 + actSize l + 7) / 8 * c := rfl

/-! ### Loaded and stored words -/

theorem loadValue_i32_none (r : Nat) : loadValue .i32 none r = .i32 (UInt32.ofNat r) := rfl
theorem loadValue_i64_none (r : Nat) : loadValue .i64 none r = .i64 (UInt64.ofNat r) := rfl

theorem bool_true : Numeric.bool true = 1 := rfl
theorem bool_false : Numeric.bool false = 0 := rfl

/-! ### Addresses -/

open Lean Elab Tactic Meta in
/-- The `x` of every `UInt32.toNat x` in `e`. -/
partial def uint32Atoms (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``UInt32.toNat 1 && !e.hasLooseBVars && !acc.contains e.appArg! then
    acc.push e.appArg! else acc
  match e with
  | .app f a => uint32Atoms a (uint32Atoms f acc)
  | .lam _ t b _ | .forallE _ t b _ => uint32Atoms b (uint32Atoms t acc)
  | .letE _ t v b _ => uint32Atoms b (uint32Atoms v (uint32Atoms t acc))
  | .mdata _ b | .proj _ _ b => uint32Atoms b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- Add `x.toNat < 2 ^ 32` for every `UInt32.toNat x` in the goal and the
hypotheses, for `omega`. -/
elab "muint_bounds" : tactic => withMainContext do
  let mut atoms : Array Lean.Expr := uint32Atoms (← instantiateMVars (← getMainTarget)) #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do atoms := uint32Atoms (← instantiateMVars d.type) atoms
  for x in atoms do
    let h ← mkAppM ``UInt32.toNat_lt #[x]
    let (_, g) ← (← (← getMainGoal).assert `hlt (← inferType h) h).intro1P
    replaceMainGoal [g]

/-! ## The tactic -/

/-- Normalise after a step: stacks to list literals (or `xs ++ [..]`),
`Post.mseq_normal`, load/store widths. -/
macro "mstep_norm" : tactic =>
  `(tactic| (try simp (disch := omega) only [Post.mseq_normal, List.reverse_cons, List.reverse_nil,
    List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append,
    List.singleton_append, List.append_assoc, loadWidth, storeWidth, NumType.byteWidth,
    mul_add_sub_self, mul_sub_self, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.sub_self,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add]))

/-- `mstep_norm` and more, what `mstep` runs once `NearLogic.Tactic.Control`
is imported:

* credits: `k * c + R - j * c` to `(k - j) * c + R`, sums of multiples of
  `c` folded, `K - a - b` to `K - (a + b)`, `K - 0` to `K`;
* locals: frames `⟨l, i, m⟩.withLocals l'` to `⟨l', i, m⟩`, `#[..].set! i v`
  of a literal array to a literal array, `entryLocals code args` of a
  function constant to a literal array, `activationGas c #[..]` to `m * c`;
* stacks: `List.drop`/`List.take`/`List.length` of literal lists;
* words: `loadValue` at `i32`/`i64` (no packing) to a value,
  `decodeLE (bytes32 w)` to `w`, `storeBytes (.i32 w) 4` to `bytes32 w` (so
  a stored word reads `n ↦[i32][ a ] w`), `Numeric.bool true/false`,
  `(k : UInt32).toNat` of a literal, `x + 0`. -/
macro "mstep_norm_full" : tactic =>
  `(tactic| (try simp (disch := omega) only [Post.mseq_normal, List.reverse_cons, List.reverse_nil,
    List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append,
    List.singleton_append, List.append_assoc, loadWidth, storeWidth, NumType.byteWidth,
    mul_add_sub_self, mul_sub_self, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.sub_self,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.sub_zero, Nat.sub_sub,
    mul_add_sub_mul, mul_add_mul, self_add_mul, mul_add_self, self_add_self, ← Nat.mul_assoc,
    Frame.withLocals_mk, Frame.withLocals_withLocals, set!_toArray, List.set_cons_zero,
    List.set_cons_succ, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    entryLocals_eq, reduceFuncLocals, List.map_cons, List.map_nil,
    ValType.default, List.append_toArray, activationGas_toArray, actSize_nil, actSize_i32,
    actSize_f32, actSize_i64, actSize_f64, actSize_ref,
    List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.drop_nil,
    List.take_succ_cons, List.take_zero, List.take_nil,
    loadValue_i32_none, loadValue_i64_none, decodeLE_bytes32, UInt32.ofNat_toNat,
    storeBytes_i32, bool_true, bool_false, UInt32.toNat_zero, UInt32.toNat_ofNat, UInt32.reduceToNat,
    Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv]))

/-- An address equation `a.toNat + off = addr`: syntactically, after
normalising literals, or by `omega` once `UInt32` sums and differences are
`toNat`'d (`(x + k).toNat = (x.toNat + k) % 2 ^ 32`) and every `x.toNat` is
bounded; no overflow is then a hypothesis like `x.toNat + k < 2 ^ 32` (or
`k ≤ x.toNat` for `x - k`) in the context. -/
macro "maddr" : tactic =>
  `(tactic| focus first
    | with_reducible rfl
    | (simp only [Nat.add_zero, Nat.zero_add, UInt32.toNat_zero, UInt32.toNat_ofNat, UInt32.reduceToNat,
        Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]; done)
    | ((try simp only [UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat',
          UInt32.toNat_zero, UInt32.toNat_ofNat, UInt32.reduceToNat, Nat.add_zero, Nat.zero_add] at *)
       muint_bounds
       omega))

/-- The locals side condition of `local.get`, `f.locals[i]? = some ?v`, on
a frame after `local.set`/`local.tee` or on `entryLocals`. -/
macro "mlocals" : tactic =>
  `(tactic| ((simp (disch := omega) only [Frame.withLocals_locals, Frame.withLocals_mk,
      getElem?_set!_self, getElem?_set!_ne, set!_toArray, List.set_cons_zero, List.set_cons_succ,
      List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero, entryLocals_eq,
      reduceFuncLocals, List.map_cons, List.map_nil, ValType.default, List.append_toArray,
      List.cons_append, List.nil_append]) <;> rfl))

/-- Close one side condition of a flexible rule. -/
macro "mstep_side" : tactic =>
  `(tactic| first
    | trivial
    | assumption
    | rfl
    | (simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.singleton_append, List.append_assoc, List.reverse_reverse] <;> rfl)
    | omega
    | (apply List.ne_nil_of_length_pos; simp_all [loadWidth, storeWidth, NumType.byteWidth] <;> omega)
    | (simp_all [loadWidth, storeWidth, NumType.byteWidth] <;> first | rfl | omega)
    | mlocals
    | (mstep_norm_full; omega))

/-- Close the side conditions of a flexible rule, a conjunction. -/
macro "mstep_sides" : tactic =>
  `(tactic| (and_intros <;> mstep_side))

/-- Weaken the credits `Hc` to `credits _ R`, the difference by `omega`. -/
syntax "mcredits " term : tactic

macro_rules
  | `(tactic| mcredits $r) => do
    let hc := Lean.mkIdent `Hc
    `(tactic| (
      ihave $hc:ident : credits _ $r $$ [$hc:ident]
      · iapply credits_le
        isplitl [$hc:ident]
        · iexact $hc:ident
        · ipureintro; omega))

/-- Run the first instruction of the fragment; see the module docstring. -/
syntax (name := mstepStx) "mstep" (" [" ident "]")? (" with " tactic)? : tactic

/-- Extension point: a step for an instruction `mstep` has no rule of its own
for (`NearLogic.Tactic.Control` gives the control instructions). -/
syntax (name := mstepExtStx) "mstep_ext" (" with " tactic)? : tactic

/-- Extension point: what runs after each step in place of `mstep_norm`
(`NearLogic.Tactic.Control` normalises with `mstep_norm_full` and the block
and function postconditions, and pays for leaving a block or the function). -/
syntax (name := mstepPostStx) "mstep_post" (" with " tactic)? : tactic

/-- How a flexible rule takes its resource. -/
inductive MStepRes where
  /-- No resource. -/
  | none
  /-- A resource `Hm`, its address unified. -/
  | res
  /-- A resource `Hm` at a free address, then the address equation (`maddr`). -/
  | addr

open Lean Elab Tactic Meta in
/-- The flexible rule for an instruction, and how it takes its resource;
`full` picks the loads and stores at the resource's own address. -/
def mstepRule (i : Lean.Expr) (full : Bool) : MetaM (Option (Name × MStepRes)) := do
  let some c := i.getAppFn.constName? | return none
  return match c with
  | ``Instr.nop => some (``mwpi_nop', .none)
  | ``Instr.drop => some (``mwpi_drop', .none)
  | ``Instr.i32_const => some (``mwpi_i32_const', .none)
  | ``Instr.i64_const => some (``mwpi_i64_const', .none)
  | ``Instr.local_get => some (``mwpi_local_get', .none)
  | ``Instr.local_set => some (``mwpi_local_set', .none)
  | ``Instr.local_tee => some (``mwpi_local_tee', .none)
  | ``Instr.i32_eqz => some (``mwpi_i32_eqz', .none)
  | ``Instr.i64_eqz => some (``mwpi_i64_eqz', .none)
  | ``Instr.i32_unop => some (``mwpi_i32_unop', .none)
  | ``Instr.i64_unop => some (``mwpi_i64_unop', .none)
  | ``Instr.i32_binop => some (``mwpi_i32_binop', .none)
  | ``Instr.i64_binop => some (``mwpi_i64_binop', .none)
  | ``Instr.i32_relop => some (``mwpi_i32_relop', .none)
  | ``Instr.i64_relop => some (``mwpi_i64_relop', .none)
  | ``Instr.cvt => some (``mwpi_cvt', .none)
  | ``Instr.load => if full then some (``mwpi_load_at', .addr) else some (``mwpi_load', .res)
  | ``Instr.store => if full then some (``mwpi_store_at', .addr) else some (``mwpi_store', .res)
  | ``Instr.global_get => some (``mwpi_global_get', .res)
  | ``Instr.global_set => some (``mwpi_global_set', .res)
  | ``Instr.memory_size => some (``mwpi_memory_size', .res)
  | _ => none

open Lean Elab Tactic Meta in
/-- The first instruction of the fragment in the goal, and whether it is the
last; `none` for the empty fragment. -/
def mstepTarget : TacticM (Option (Lean.Expr × Bool)) := do
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  unless tgt.isAppOfArity ``Iris.ProofMode.Entails' 4 do
    throwError "mstep: not in the iris proof mode"
  let goal := tgt.appArg!.consumeMData
  unless goal.isAppOfArity ``mwpi 9 do
    throwError "mstep: the goal is not `mwpi …`:{indentExpr goal}"
  let es ← whnfR (goal.getArg! 7)
  if es.isAppOfArity ``List.nil 1 then return none
  unless es.isAppOfArity ``List.cons 3 do
    throwError "mstep: the fragment is not a list `i :: es` (unfold the function body first):\
      {indentExpr es}"
  let rest ← whnfR (es.getArg! 2)
  return some (es.getArg! 1, rest.isAppOfArity ``List.nil 1)

open Lean Elab Tactic in
/-- Whether a tactic syntax kind has an implementation (an extension point
filled by an imported file). -/
def mstepHasImpl (kind : Name) : CoreM Bool := do
  let env ← getEnv
  return !(macroAttribute.getEntries env kind).isEmpty ||
    !(tacticElabAttribute.getEntries env kind).isEmpty

open Lean Elab Tactic in
/-- After a step: `mstep_post` if a file gives it, else `mstep_norm`. -/
def mstepAfter (tac? : Option (TSyntax `tactic)) : TacticM Unit := do
  if ← mstepHasImpl ``mstepPostStx then
    evalTactic (← `(tactic| mstep_post $[with $tac?]?))
  else
    evalTactic (← `(tactic| mstep_norm))

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| mstep $[ [$hm?] ]? $[with $tac?]?) => do
    let full ← mstepHasImpl ``mstepPostStx
    let some (i, last) ← mstepTarget
      | -- the empty fragment falls through
        evalTactic (← `(tactic| iapply mwpi_nil))
        mstepAfter tac?
    let some (rule, kind) ← mstepRule i full
      | if ← mstepHasImpl ``mstepExtStx then
          evalTactic (← `(tactic| mstep_ext $[with $tac?]?))
          return
        throwError "mstep: no rule for{indentExpr i}\nstep it manually (control instructions \
          and calls: import NearLogic.Tactic.Control)"
    let ruleId := mkIdent rule
    let hc := mkIdent `Hc
    let side ← match tac? with
      | some t => `(tactic| (and_intros <;> first | ($t; done) | mstep_side))
      | none => `(tactic| mstep_sides)
    unless last do evalTactic (← `(tactic| iapply mwpi_cons))
    evalTactic (← `(tactic| iapply $ruleId:ident))
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    match kind with
    | .none =>
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; $side)))
      evalTactic (← `(tactic| inext))
      evalTactic (← `(tactic| iintro $hc:ident))
    | .res | .addr =>
      let some hm := hm?
        | throwError "mstep: this instruction needs a resource: `mstep [Hm]`"
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; mstep_sides)))
      evalTactic (← `(tactic| isplitl [$hm:ident]))
      evalTactic (← `(tactic| iexact $hm:ident))
      if let .addr := kind then
        let addrTac ← match tac? with
          | some t => `(tactic| first | ($t; done) | maddr)
          | none => `(tactic| maddr)
        evalTactic (← `(tactic| isplitr))
        evalTactic (← `(tactic| focus (ipureintro; $addrTac)))
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; $side)))
      evalTactic (← `(tactic| inext))
      evalTactic (← `(tactic| iintro $hc:ident $hm:ident))
    mstepAfter tac?

/-! ## A test: pure instructions, locals, and the credit bookkeeping -/

section Test

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

example {GF : BundledGFunctors} [WasmGS NearState GF] {cfg : WasmConfig} {lim : ExecLimits}
    {d : Nat} {Φ : Post NearState GF} {Cg R : Nat}
    (f : Frame) (x : UInt32) (h0 : f.locals[0]? = some (.i32 x)) (hs : 1 < f.locals.size) :
    credits Cg (11 * cfg.regularOpCost + R) ∗
      (∀ g, credits Cg R -∗ Φ.normal [.i32 (1 + x + 2)] g)
      ⊢ mwpi cfg lim d f [] [.i32_const 1, .local_get 0, .i32_binop .add, .i32_const 2,
          .i32_binop .add, .local_tee 1, .i32_eqz, .drop, .nop, .local_get 1] Φ := by
  iintro ⟨Hc, HΦ⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcredits R
  iapply HΦ $$ Hc

/-! ### The normal forms and side conditions of the full mode

(`mstep` itself runs in full mode once `NearLogic.Tactic.Control` is
imported; its tests are there.) -/

/-- Credit amounts after a step, a call or a payment. -/
example (c R : Nat) (P : Nat → Prop) (h : P (8 * c + R)) :
    P (31 * c + R - c - (c + 10 * c + 11 * c) - 0 + 0) ∧ P ((10 - 1 - 1) * c + R) := by
  constructor <;> (mstep_norm_full; exact h)

/-- Locals: `local.set` on a literal frame, `local.get` after it, and the
locals of a function entered. -/
example (x v : Value) (inst : Nat) (mi : ModuleInst) (P : Frame → Prop)
    (h : P ⟨#[x, v, .i32 0], inst, mi⟩) :
    P ((Frame.mk #[x, .i32 0, .i32 0] inst mi).withLocals (#[x, .i32 0, .i32 0].set! 1 v)) := by
  mstep_norm_full; exact h

example (x v : Value) (l : Array Value) (inst : Nat) (mi : ModuleInst) (hl : 2 < l.size) :
    (Frame.mk ((l.set! 1 v).set! 2 x) inst mi).locals[1]? = some v := by
  mlocals

private def testCode : Func := { type := 0, locals := [.num .i32, .num .i64], body := [] }

example (a : UInt32) : entryLocals testCode [.i32 a] = #[.i32 a, .i32 0, .i64 0] := by
  mstep_norm_full

example (c : Nat) (a : UInt32) :
    activationGas c (entryLocals testCode [.i32 a]) = 10 * c := by
  mstep_norm_full

example (a : UInt32) (inst : Nat) (mi : ModuleInst) :
    (Frame.mk (entryLocals testCode [.i32 a]) inst mi).locals[2]? = some (.i64 0) := by
  mlocals

/-- Addresses: a constant one, a sum, and a difference, against points-to
stated at `k` or `x.toNat + k`. -/
example (x sp : UInt32) (hx : x.toNat + 16 < 2 ^ 32) (hsp : 16 ≤ sp.toNat) :
    (0 : UInt32).toNat + 1074920 = 1074920 ∧ (x + 8).toNat + 4 = x.toNat + 12 ∧
      (sp - 16 + 8).toNat + 0 = (sp - 16).toNat + 8 ∧ (sp - 16).toNat + 4 = sp.toNat - 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> maddr

/-- Loaded words. -/
example (w : UInt32) :
    loadValue .i32 none (Memory.decodeLE (storeBytes (.i32 w) (storeWidth .i32 none))) = .i32 w := by
  mstep_norm_full

end Test

end NearLogic
