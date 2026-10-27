import Binary.Code.Part08
import Binary.Code.Part09
import Binary.Code.Part12
import NearLogic.Rules.Pure
import NearLogic.Rules.Memory
import NearLogic.Rules.Control
import NearLogic.Rules.CallIndirectSpec
import Lean


/-!
# `RefCell::borrow_mut` (441) and the drop of its guard (442), metered

The callees of `LocalKey::with` (463) that touch a `RefCell`'s borrow flag,
on the path where the cell is free:

* `672` `Cell<isize>::replace(p, v)`: the old word at `p` returned, `v`
  written (7 instructions).
* `492` `BorrowRefMut::new(flag)`: the flag is 0, so it becomes -1 through
  `replace` and `flag` is returned (12 instructions and the call, 29 in all).
* `441` `RefCell::borrow_mut(out, cell, loc)`: `BorrowRefMut::new` succeeds,
  so the `RefMut` `(cell + 4, cell)` (value, flag) is written at `out`
  (21 instructions and the call, 59 in all).
* `442` `drop_in_place<BorrowRefMut>(p)`: the flag word `q` at `p`, its value
  incremented through `replace` (9 instructions and the call, 26 in all).
* `464` `drop_in_place<Option<Box<dyn BlockchainInterface>>>(p)`, for `None`
  (the word at `p` zero): nothing to drop (4 instructions).
* `433` `Result::expect(r)`, for `Ok` (`r = 0`): nothing to do
  (12 instructions).

Also the helpers shared with `KeyGet.lean` and `SetBlockchainInterface.lean`:
`sstep`, a copy of `mstep` (`NearLogic/Tactic/Step.lean`, as of this proof),
and the control helpers of `SetupPanicHook.lean` (`sclean`, `sblock`, …), with
array updates of any size.
-/


namespace WNear.Binary.BorrowMut

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## `sstep`: a local copy of `sstep` (`NearLogic/Tactic/Step.lean`) -/

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
macro "sstep_norm" : tactic =>
  `(tactic| (try simp (disch := omega) only [Post.mseq_normal, List.reverse_cons, List.reverse_nil,
    List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append,
    List.singleton_append, List.append_assoc, loadWidth, storeWidth, NumType.byteWidth,
    mul_add_sub_self, mul_sub_self, Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.sub_self,
    Nat.one_mul, Nat.zero_mul, Nat.zero_add]))

/-- Close one side condition of a flexible rule. -/
macro "sstep_side" : tactic =>
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
macro "sstep_sides" : tactic =>
  `(tactic| (and_intros <;> sstep_side))

/-- Weaken the credits `Hc` to `credits _ R`, the difference by `omega`. -/
syntax "scredits_to " term : tactic

macro_rules
  | `(tactic| scredits_to $r) => do
    let hc := Lean.mkIdent `Hc
    `(tactic| (
      ihave $hc:ident : credits _ $r $$ [$hc:ident]
      · iapply credits_le
        isplitl [$hc:ident]
        · iexact $hc:ident
        · ipureintro; omega))

/-- Run the first instruction of the fragment; see the module docstring. -/
syntax (name := sstepStx) "sstep" (" [" ident "]")? (" with " tactic)? : tactic

open Lean Elab Tactic Meta in
/-- The flexible rule for an instruction, and whether it takes a resource. -/
private def sstepRule (i : Lean.Expr) : MetaM (Option (Name × Bool)) := do
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
private def sstepTarget : TacticM (Lean.Expr × Bool) := do
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  unless tgt.isAppOfArity ``Iris.ProofMode.Entails' 4 do
    throwError "sstep: not in the iris proof mode"
  let goal := tgt.appArg!.consumeMData
  unless goal.isAppOfArity ``mwpi 9 do
    throwError "sstep: the goal is not `mwpi …`:{indentExpr goal}"
  let es ← whnfR (goal.getArg! 7)
  unless es.isAppOfArity ``List.cons 3 do
    throwError "sstep: the fragment is not a list `i :: es` (unfold the function body first):\
      {indentExpr es}"
  let rest ← whnfR (es.getArg! 2)
  return (es.getArg! 1, rest.isAppOfArity ``List.nil 1)

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| sstep $[ [$hm?] ]? $[with $tac?]?) => do
    let (i, last) ← sstepTarget
    let some (rule, needsRes) ← sstepRule i
      | throwError "sstep: no rule for{indentExpr i}\nstep it manually"
    let ruleId := mkIdent rule
    let hc := mkIdent `Hc
    let side ← match tac? with
      | some t => `(tactic| (and_intros <;> first | ($t; done) | sstep_side))
      | none => `(tactic| sstep_sides)
    unless last do evalTactic (← `(tactic| iapply mwpi_cons))
    evalTactic (← `(tactic| iapply $ruleId:ident))
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    if needsRes then
      let some hm := hm?
        | throwError "sstep: this instruction needs a resource: `sstep [Hm]`"
      evalTactic (← `(tactic| isplitr))
      evalTactic (← `(tactic| (ipureintro; sstep_sides)))
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
    evalTactic (← `(tactic| sstep_norm))

/-! ## A test: pure instructions, locals, and the credit bookkeeping -/

/-! ## Control helpers (as in `SetupPanicHook.lean`) -/

theorem loadValue_bytes32 (w : UInt32) :
    loadValue .i32 none (Memory.decodeLE (bytes32 w)) = .i32 w := by
  simp [loadValue, decodeLE_bytes32]

theorem blockType_empty (mi : ModuleInst) :
    Exec.blockType mi .empty = { params := [], results := [] } := rfl

theorem bool_true : Numeric.bool true = 1 := rfl
theorem bool_false : Numeric.bool false = 0 := rfl

section Control

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

theorem mwpi_br_if_true' (n : Nat) {rest : List Value} {c : UInt32} :
    ⌜vs.reverse = .i32 c :: rest ∧ c ≠ 0⌝ ∗ Φ.br n rest.reverse f
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ := by
  iintro ⟨%⟨hs, hc⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_br_if_true n c hc $$ H

theorem mwpi_br_if_false' (n : Nat) {rest : List Value} :
    credits Cg K ∗ ⌜vs.reverse = .i32 0 :: rest ∧ cfg.regularOpCost ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ :=
  credits_flex fun hs _ => by rw [stack_top1 hs]; exact mwpi_br_if_false n

theorem mwpi_block_empty (body : List Instr) :
    credits Cg K ∗ ▷ (credits Cg K -∗ mwpi cfg lim d f [] body (Post.mblock cfg Cg 0 vs Φ))
      ⊢ mwpi cfg lim d f vs [.block .empty body] Φ :=
  mwpi_block0 .empty body vs rfl

theorem pay_intro {k : Nat} {P : IProp GF} :
    credits Cg K ∗ ⌜k ≤ K⌝ ∗ (credits Cg (K - k) -∗ P) ⊢ pay Cg k P := by
  iintro ⟨Hc, %h, HP⟩
  unfold pay
  iexists K - k
  rw [Nat.add_sub_cancel' h]
  iframe Hc
  inext
  iexact HP

/-- `mwpi_call_spec` on a stack holding just the arguments. -/
theorem mwpi_call_spec_args (i a : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst)
    (code : Func) (args : List Value) {Cg R : Nat} (P : List Value → IProp GF)
    (K : List Value → Nat) (Q : List Value → List Value → IProp GF)
    (ha : f.mi.funcAddrs[i]? = some a) (hlen : args.length = type.params.length)
    (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, credits Cg R -∗ Q args rs -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ :=
  mwpi_call_spec (vs₀ := []) i a type inst mi code args P K Q ha hlen hd

/-- `mwpi_call_indirect_spec` on a stack holding just the arguments and the
index, in any syntactic form. -/
theorem mwpi_call_indirect_spec_at (ty t ta : Nat) (idx : UInt32) (a : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (code : Func) (args : List Value) {vs : List Value} {Cg R : Nat}
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : List Value → List Value → IProp GF)
    (hvs : vs = args ++ [.i32 idx])
    (hta : f.mi.tableAddrs[t]? = some ta) (hty : type = f.mi.types[ty]!)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      ta ↦[wt][ idx.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm type inst code ∗
      inst ↪[inst] mi ∗ MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, ta ↦[wt][ idx.toNat ] Ref.func a -∗ credits Cg R -∗ Q args rs -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f vs [.call_indirect ty t] Φ := by
  subst hvs
  exact mwpi_call_indirect_spec_args ty t ta idx a type inst mi code args P K Q hta hty hlen hd

end Control

/-! ## Helpers -/

theorem toArray_set! {α : Type} (l : List α) (i : Nat) (v : α) :
    l.toArray.set! i v = (l.set i v).toArray := by
  simp [Array.set!]

/-- Normalise frames, locals, loaded words and block postconditions. -/
macro "sclean" : tactic =>
  `(tactic| (try simp (disch := omega) only [Frame.withLocals, toArray_set!, List.set_cons_succ,
    List.set_cons_zero, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    loadValue_bytes32, storeBytes_i32, Post.mseq_normal, Post.mseq_br, Post.mseq_ret,
    Post.mblock_normal, Post.mblock_br_zero, Post.mblock_br_succ, Post.mblock_ret,
    blockType_empty, List.length_nil, List.nil_append, List.append_nil, List.drop_zero,
    Nat.sub_zero, List.length_cons, List.drop_length, beq_self_eq_true, bool_true, Nat.add_zero]))

macro "sblock" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_block_empty)
      | iapply mwpi_block_empty
    isplitl [$hc:ident]
    · iexact $hc:ident
    inext
    iintro $hc:ident
    sclean))

macro "sbr_taken" : tactic =>
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_br_if_true')
      | iapply mwpi_br_if_true'
    isplitr
    · ipureintro; exact ⟨rfl, by first | decide | assumption⟩
    sclean))

macro "sbr_not" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    first
      | (iapply mwpi_cons; iapply mwpi_br_if_false')
      | iapply mwpi_br_if_false'
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; exact ⟨rfl, by omega, trivial⟩
    inext
    iintro $hc:ident
    sclean))

/-- Pay for the step leaving a block by a branch (`Post.mblock`'s `br 0`). -/
macro "spay" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    isplitr
    · ipureintro; simp
    iapply pay_intro
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; omega
    iintro $hc:ident
    sclean))

/-- Pay nothing to fall off the end of a block (`Post.mblock`'s `normal`). -/
macro "spay0" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    iapply pay_intro
    isplitl [$hc:ident]
    · iexact $hc:ident
    isplitr
    · ipureintro; omega
    iintro $hc:ident
    sclean))

/-- Weaken the credits `Hc` to the given amount, by `omega`. -/
macro "scredits" : tactic => do
  let hc := Lean.mkIdent `Hc
  `(tactic| (
    iapply credits_le
    isplitl [$hc:ident]
    · iexact $hc:ident
    · ipureintro; omega))

/-! ## `Cell<isize>::replace` (672) -/

section Replace

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def replacePre (n : Nat) (p v old : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p, .i32 v]⌝ ∗ n ↦[i32][ p.toNat ] old)

def replacePost (n : Nat) (p v old : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 old]⌝ ∗ n ↦[i32][ p.toNat ] v)

theorem entryLocals_f672 (a b : UInt32) :
    entryLocals f672 [.i32 a, .i32 b] = #[.i32 a, .i32 b, .i32 0] := rfl

/-- `Cell::replace(p, v)` (672): 7 instructions. -/
theorem f672_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (p v old : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f672 Cg (replacePre n p v old)
      (fun _ => 7 * cfg.regularOpCost) (replacePost n p v old) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold replacePre at HP
  icases HP with ⟨%hargs, Hp⟩
  subst hargs
  rw [entryLocals_f672]
  simp only [f672]
  sstep; sstep [Hp]; sclean; sstep
  sstep; sstep; sstep [Hp]
  sstep; sclean
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  iframe Hc
  iintro Hc
  iunfold replacePost
  iframe Hc Hp
  ipureintro; rfl

end Replace


/-! ## `BorrowRefMut::new` (492), the flag free -/

section BorrowRefMutNew

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def newPre (n : Nat) (flag : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 flag]⌝ ∗ n ↦[i32][ flag.toNat ] 0)

/-- The flag taken for writing (-1), `Some(flag)` returned. -/
def newPost (n : Nat) (flag : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 flag]⌝ ∗ n ↦[i32][ flag.toNat ] 4294967295)

theorem entryLocals_f492 (a : UInt32) : entryLocals f492 [.i32 a] = #[.i32 a, .i32 0] := rfl

theorem activation_f672 (c : Nat) (a b : UInt32) :
    activationGas c (entryLocals f672 [.i32 a, .i32 b]) = 10 * c := by
  simp [activationGas, entryLocals, f672, ValType.default]

/-- `BorrowRefMut::new(flag)` (492), the flag 0: 12 instructions and
`replace` (its activation 10 and its 7), 29 in all. -/
theorem f492_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[672]? = some a672) (ty672 : FuncType)
    (hty : ty672.params.length = 2) (hty' : ty672.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (flag : UInt32) :
    a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f492 Cg (newPre n flag)
        (fun _ => 29 * cfg.regularOpCost) (newPost n flag) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold newPre at HP
  icases HP with ⟨%hargs, Hp⟩
  subst hargs
  rw [entryLocals_f492]
  simp only [f492]
  sstep; sstep; sclean
  sblock
  sstep; sstep [Hp]; sclean
  sbr_not
  sstep; sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 4 * cfg.regularOpCost + R) 672 a672 ty672 inst mi f672
    [.i32 flag, .i32 4294967295] (replacePre n flag 4294967295 0) (fun _ => 7 * cfg.regularOpCost)
    (replacePost n flag 4294967295 0) ha (by simp [hty]) hd
  isplitl [Hc]
  · rw [activation_f672]; scredits
  isplitr; iexact Hf
  isplitr; iexact Hi
  isplitr
  · iapply f672_spec cfg lim (d + 1) ty672 hty' inst mi n hn Cg
  isplitl [Hp]
  · iunfold replacePre
    iframe Hp
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold replacePost at HQ
  icases HQ with ⟨%hrs, Hp⟩
  subst hrs
  sclean
  sstep; sstep; sstep; sclean
  spay0
  sstep; sclean
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  iframe Hc
  iintro Hc
  iunfold newPost
  iframe Hc Hp
  ipureintro; rfl

end BorrowRefMutNew

/-! ## `RefCell::borrow_mut` (441), the cell free -/

section BorrowMutFn

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The stack pointer, the flag of the cell (free) and the two words at `out`. -/
def borrowMutPre (n g : Nat) (gi : GlobalInst) (out cell loc o1 o2 : UInt32)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 cell, .i32 loc]⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ cell.toNat ] 0 ∗
    n ↦[i32][ out.toNat ] o1 ∗ n ↦[i32][ out.toNat + 4 ] o2)

/-- The flag taken (-1); the `RefMut` (the value at `cell + 4`, the flag at
`cell`) at `out`. -/
def borrowMutPost (n g : Nat) (gi : GlobalInst) (out cell : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ cell.toNat ] 4294967295 ∗
    n ↦[i32][ out.toNat ] (cell + 4) ∗ n ↦[i32][ out.toNat + 4 ] cell)

theorem entryLocals_f441 (a b c : UInt32) :
    entryLocals f441 [.i32 a, .i32 b, .i32 c] = #[.i32 a, .i32 b, .i32 c, .i32 0, .i32 0] := rfl

theorem activation_f492 (c : Nat) (a : UInt32) :
    activationGas c (entryLocals f492 [.i32 a]) = 9 * c := by
  simp [activationGas, entryLocals, f492, ValType.default]

/-- `RefCell::borrow_mut(out, cell, loc)` (441), the cell free: 21
instructions and `BorrowRefMut::new` (its activation 9 and its 29), 59 in
all. -/
theorem f441_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a492 a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha2 : mi.funcAddrs[492]? = some a492) (ha7 : mi.funcAddrs[672]? = some a672)
    (ty492 ty672 : FuncType) (hty2 : ty492.params.length = 1) (hty2' : ty492.results.length = 1)
    (hty7 : ty672.params.length = 2) (hty7' : ty672.results.length = 1)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (out cell loc o1 o2 : UInt32) (hcell : cell ≠ 0) :
    a492 ↪[wf] FuncInst.wasm ty492 inst f492 ∗ a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f441 Cg (borrowMutPre n g gi out cell loc o1 o2)
        (fun _ => 59 * cfg.regularOpCost) (borrowMutPost n g gi out cell) := by
  iintro ⟨#Hf2, #Hf7, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold borrowMutPre at HP
  icases HP with ⟨%hargs, Hg, Hp, Ho1, Ho2⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  rw [entryLocals_f441]
  simp only [f441]
  -- sp -= 16
  sstep [Hg]; sstep; sstep; sstep; sclean; sstep [Hg]
  sblock
  sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 14 * cfg.regularOpCost + R) 492 a492 ty492 inst mi f492
    [.i32 cell] (newPre n cell) (fun _ => 29 * cfg.regularOpCost) (newPost n cell) ha2
    (by simp [hty2]) (by omega)
  isplitl [Hc]
  · rw [activation_f492]; scredits
  isplitr; iexact Hf2
  isplitr; iexact Hi
  isplitr
  · iapply f492_spec cfg lim (d + 1) ty492 hty2' inst mi n a672 hn ha7 ty672 hty7 hty7'
      (by omega) Cg cell
    iframe Hf7 Hi
  isplitl [Hp]
  · iunfold newPre
    iframe Hp
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold newPost at HQ
  icases HQ with ⟨%hrs, Hp⟩
  subst hrs
  sclean
  sstep; sclean
  sbr_taken
  spay
  -- the RefMut at out
  sstep; sstep; sstep [Ho2]
  sstep; sstep; sstep; sstep; sstep [Ho1]
  -- sp += 16
  sstep; sstep; sstep; sstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  simp only [e]
  sclean
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold borrowMutPost
  iframe Hc Hg Hp Ho1 Ho2
  ipureintro; rfl

end BorrowMutFn

/-! ## `drop_in_place<BorrowRefMut>` (442) -/

section DropRefMut

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The guard at `p` points to the flag `q`, holding `fl`. -/
def dropPre (n : Nat) (p q fl : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p]⌝ ∗ n ↦[i32][ p.toNat ] q ∗ n ↦[i32][ q.toNat ] fl)

/-- The flag incremented. -/
def dropPost (n : Nat) (p q fl : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ p.toNat ] q ∗ n ↦[i32][ q.toNat ] (fl + 1))

theorem entryLocals_f442 (a : UInt32) : entryLocals f442 [.i32 a] = #[.i32 a] := rfl

/-- `drop_in_place<BorrowRefMut>(p)` (442): 9 instructions and `replace`
(its activation 10 and its 7), 26 in all. -/
theorem f442_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n a672 : Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[672]? = some a672) (ty672 : FuncType)
    (hty : ty672.params.length = 2) (hty' : ty672.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (p q fl : UInt32) :
    a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f442 Cg (dropPre n p q fl)
        (fun _ => 26 * cfg.regularOpCost) (dropPost n p q fl) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold dropPre at HP
  icases HP with ⟨%hargs, Hp, Hq⟩
  subst hargs
  rw [entryLocals_f442]
  simp only [f442]
  sstep; sstep [Hp]; sclean; sstep; sclean; sstep; sstep [Hq]; sclean; sstep; sstep
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 1 * cfg.regularOpCost + R) 672 a672 ty672 inst mi f672
    [.i32 q, .i32 (fl + 1)] (replacePre n q (fl + 1) fl) (fun _ => 7 * cfg.regularOpCost)
    (replacePost n q (fl + 1) fl) ha (by simp [hty]) hd
  isplitl [Hc]
  · rw [activation_f672]; scredits
  isplitr; iexact Hf
  isplitr; iexact Hi
  isplitr
  · iapply f672_spec cfg lim (d + 1) ty672 hty' inst mi n hn Cg
  isplitl [Hq]
  · iunfold replacePre
    iframe Hq
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold replacePost at HQ
  icases HQ with ⟨%hrs, Hq⟩
  subst hrs
  sclean
  sstep
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  isplitl [Hc]
  · scredits
  iintro Hc
  iframe Hc
  iunfold dropPost
  iframe Hp Hq
  ipureintro; rfl

end DropRefMut

/-! ## `drop_in_place<Option<Box<dyn BlockchainInterface>>>` (464), for `None` -/

section DropNone

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def dropNonePre (n : Nat) (p : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p]⌝ ∗ n ↦[i32][ p.toNat ] 0)

def dropNonePost (n : Nat) (p : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ p.toNat ] 0)

theorem entryLocals_f464 (a : UInt32) : entryLocals f464 [.i32 a] = #[.i32 a] := rfl

/-- `drop_in_place::<Option<Box<dyn _>>>(p)` (464) on `None`: 4
instructions. -/
theorem f464_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (p : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f464 Cg (dropNonePre n p)
      (fun _ => 4 * cfg.regularOpCost) (dropNonePost n p) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold dropNonePre at HP
  icases HP with ⟨%hargs, Hp⟩
  subst hargs
  rw [entryLocals_f464]
  simp only [f464]
  sblock
  sstep; sstep [Hp]; sclean; sstep; sclean
  sbr_taken
  spay
  iapply mwpi_nil
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  isplitl [Hc]
  · scredits
  iintro Hc
  iunfold dropNonePost
  iframe Hc Hp
  ipureintro; rfl

end DropNone

/-! ## `Result::expect` (433), for `Ok` -/

section ExpectOk

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def expectPre (g : Nat) (gi : GlobalInst) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 0]⌝ ∗ g ↦[wg] gi)

def expectPost (g : Nat) (gi : GlobalInst) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi)

theorem entryLocals_f433 (a : UInt32) : entryLocals f433 [.i32 a] = #[.i32 a, .i32 0] := rfl

/-- `Result::expect(Ok)` (433): 12 instructions. -/
theorem f433_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (g : Nat)
    (hg : mi.globalAddrs[0]? = some g) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f433 Cg (expectPre g gi)
      (fun _ => 12 * cfg.regularOpCost) (expectPost g gi) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold expectPre at HP
  icases HP with ⟨%hargs, Hg⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  rw [entryLocals_f433]
  simp only [f433]
  sstep [Hg]; sstep; sstep; sstep; sclean; sstep [Hg]
  sblock
  sstep; sstep; sclean
  sbr_taken
  spay
  sstep; sstep; sstep; sstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  simp only [e]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold expectPost
  iframe Hc Hg
  ipureintro; rfl

end ExpectOk

end WNear.Binary.BorrowMut
