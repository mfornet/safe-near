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
`simp_all` with the width definitions followed by `omega`. When it fails,
`mstep` fails, with the goal it could not prove; pass `with tac` or step
manually with the `mwpi_*'` rules.
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

end Flex

/-! ## The tactic -/

/-- Normalise after a step: stacks to list literals (or `xs ++ [..]`),
`Post.mseq_normal`, load/store widths. -/
macro "mstep_norm" : tactic =>
  `(tactic| (try simp (disch := omega) only [Post.mseq_normal, List.reverse_cons, List.reverse_nil,
    List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append,
    List.singleton_append, List.append_assoc, loadWidth, storeWidth, NumType.byteWidth,
    mul_add_sub_self, mul_sub_self, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.sub_self,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add]))

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
    | (simp_all [loadWidth, storeWidth, NumType.byteWidth] <;> first | rfl | omega))

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

open Lean Elab Tactic Meta in
/-- The flexible rule for an instruction, and whether it takes a resource. -/
private def mstepRule (i : Lean.Expr) : MetaM (Option (Name × Bool)) := do
  let some c := i.getAppFn.constName? | return none
  return match c with
  | ``Instr.nop => some (``mwpi_nop', false)
  | ``Instr.drop => some (``mwpi_drop', false)
  | ``Instr.i32_const => some (``mwpi_i32_const', false)
  | ``Instr.i64_const => some (``mwpi_i64_const', false)
  | ``Instr.local_get => some (``mwpi_local_get', false)
  | ``Instr.local_set => some (``mwpi_local_set', false)
  | ``Instr.local_tee => some (``mwpi_local_tee', false)
  | ``Instr.i32_eqz => some (``mwpi_i32_eqz', false)
  | ``Instr.i64_eqz => some (``mwpi_i64_eqz', false)
  | ``Instr.i32_unop => some (``mwpi_i32_unop', false)
  | ``Instr.i64_unop => some (``mwpi_i64_unop', false)
  | ``Instr.i32_binop => some (``mwpi_i32_binop', false)
  | ``Instr.i64_binop => some (``mwpi_i64_binop', false)
  | ``Instr.i32_relop => some (``mwpi_i32_relop', false)
  | ``Instr.i64_relop => some (``mwpi_i64_relop', false)
  | ``Instr.cvt => some (``mwpi_cvt', false)
  | ``Instr.load => some (``mwpi_load', true)
  | ``Instr.store => some (``mwpi_store', true)
  | ``Instr.global_get => some (``mwpi_global_get', true)
  | ``Instr.global_set => some (``mwpi_global_set', true)
  | ``Instr.memory_size => some (``mwpi_memory_size', true)
  | _ => none

open Lean Elab Tactic Meta in
/-- The first instruction of the fragment in the goal, and whether it is the last. -/
private def mstepTarget : TacticM (Lean.Expr × Bool) := do
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  unless tgt.isAppOfArity ``Iris.ProofMode.Entails' 4 do
    throwError "mstep: not in the iris proof mode"
  let goal := tgt.appArg!.consumeMData
  unless goal.isAppOfArity ``mwpi 9 do
    throwError "mstep: the goal is not `mwpi …`:{indentExpr goal}"
  let es ← whnfR (goal.getArg! 7)
  unless es.isAppOfArity ``List.cons 3 do
    throwError "mstep: the fragment is not a list `i :: es` (unfold the function body first):\
      {indentExpr es}"
  let rest ← whnfR (es.getArg! 2)
  return (es.getArg! 1, rest.isAppOfArity ``List.nil 1)

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| mstep $[ [$hm?] ]? $[with $tac?]?) => do
    let (i, last) ← mstepTarget
    let some (rule, needsRes) ← mstepRule i
      | throwError "mstep: no rule for{indentExpr i}\nstep it manually"
    let ruleId := mkIdent rule
    let hc := mkIdent `Hc
    let side ← match tac? with
      | some t => `(tactic| (and_intros <;> first | ($t; done) | mstep_side))
      | none => `(tactic| mstep_sides)
    unless last do evalTactic (← `(tactic| iapply mwpi_cons))
    evalTactic (← `(tactic| iapply $ruleId:ident))
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    if needsRes then
      let some hm := hm?
        | throwError "mstep: this instruction needs a resource: `mstep [Hm]`"
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; mstep_sides)))
      evalTactic (← `(tactic| isplitl [$hm:ident]))
      evalTactic (← `(tactic| iexact $hm:ident))
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; $side)))
      evalTactic (← `(tactic| inext))
      evalTactic (← `(tactic| iintro $hc:ident $hm:ident))
    else
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; $side)))
      evalTactic (← `(tactic| inext))
      evalTactic (← `(tactic| iintro $hc:ident))
    evalTactic (← `(tactic| mstep_norm))

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

end Test

end NearLogic
