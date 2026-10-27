import NearLogic.Tactic.Step
import NearLogic.Rules.Control
import NearLogic.Rules.CallWasm

/-!
# `mstep` for control flow and calls

Importing this file extends `mstep` (`NearLogic/Tactic/Step.lean`) to the
control instructions, adds `mcall` for calls to a function with an
`MFunSpec`, and switches `mstep` to its full mode:

* loads and stores take the points-to at its own address (`mwpi_load_at'`,
  `mwpi_store_at'`), the effective address equated to it by `maddr`;
* after each step the goal is normalised with `mctrl_norm`: the block and
  sequence postconditions (`Post.mblock_*`, `Post.mseq_*`, block types), then
  `mstep_norm_full` (credits, locals, `entryLocals`, words, list literals);
* then every payment the goal asks for is made from `Hc` (`mpay`): leaving a
  block normally (`pay Cg 0`), branching to a block's label
  (`⌜…⌝ ∗ pay Cg c₀ …`), and ending the function (`Post.mfunc`'s `normal`,
  `br`, `ret`), whose goal becomes the function postcondition `Φf.ret rs`
  (for an `MFunSpec`, `credits Cg R ∗ Q args rs`).

## Interface

* `mstep` on a control instruction, the stack a list literal:
  - `block bt body` (no cost): the body runs on `[]` under
    `Post.mblock` (`mwpi_block0'`, block types without parameters, or
    `mwpi_block'`, the parameters the top of the stack);
  - `br_if n`: taken if the condition on top of the stack is provably
    nonzero (`mwpi_br_if_taken'`: the branch, then its payment), not taken if
    provably zero (`mwpi_br_if_not'`, one `regular_op_cost`);
  - `if bt th el` (one `regular_op_cost`): the `then` or the `else` branch,
    likewise;
  - `br n`, `return`, `br_table ls d` (the index a literal): the branch, then
    its payment;
  - the empty fragment (`mwpi_nil`).
* `mstep_taken`, `mstep_not_taken` force the direction of a `br_if` or `if`.
* `mcall spec using [H₁ …] as HQ` runs `call i` with `mwpi_call'`, `spec` proving
  the callee's `MFunSpec` (a term, possibly with persistent premises found by
  `iassumption`, or an iris hypothesis). The arguments are the top `n` values
  of the stack, `n` from a hypothesis `type.params.length = n` (or computed);
  the function and instance points-to are found with `iassumption`; the call,
  the activation (`activationGas` of the literal `entryLocals`) and the
  callee's cost are paid from `Hc` (side condition by `omega`). Two goals
  remain: first `P args` with `H₁, …`, then the continuation with
  `Hc : credits Cg (K - cost)`, `rs` and `HQ : Q args rs` (default name `HQ`).
* `mpay` makes one payment (see above); `mstep` makes them all.
* `with tac` on any of these tries `tac` first on each side condition.

Branch conditions are closed by `mcond` (`decide`, `assumption`,
`simp_all [Numeric.bool]`) after `mstep_side`; the payment side conditions
(`r ≤ X.length`, the amount) by `mstep_side`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Block types without parameters -/

theorem blockType_empty (mi : ModuleInst) :
    Exec.blockType mi .empty = { params := [], results := [] } := rfl

theorem blockType_val (mi : ModuleInst) (t : ValType) :
    Exec.blockType mi (.val t) = { params := [], results := [t] } := rfl

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

local notation "c₀" => cfg.regularOpCost

/-! ## Flexible control rules -/

theorem mwpi_block0' {bt : BlockType} {body : List Instr} :
    credits Cg K ∗ ⌜(Exec.blockType f.mi bt).params = []⌝ ∗
      ▷ (credits Cg K -∗ mwpi cfg lim d f [] body
          (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs Φ))
      ⊢ mwpi cfg lim d f vs [.block bt body] Φ := by
  iintro ⟨Hc, %hp, H⟩
  iapply mwpi_block0 bt body vs hp
  isplitl [Hc]
  · iexact Hc
  · iexact H

/-- A block with parameters, the top `p` values of the stack. -/
theorem mwpi_block' {bt : BlockType} {body : List Instr} {p : Nat} :
    credits Cg K ∗ ⌜(Exec.blockType f.mi bt).params.length = p ∧ p ≤ vs.length⌝ ∗
      ▷ (credits Cg K -∗ mwpi cfg lim d f (vs.drop (vs.length - p)) body
          (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length (vs.take (vs.length - p)) Φ))
      ⊢ mwpi cfg lim d f vs [.block bt body] Φ := by
  iintro ⟨Hc, %⟨hp, hl⟩, H⟩
  have h := mwpi_block (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := K)
    bt body (vs.take (vs.length - p)) (vs.drop (vs.length - p)) (by simp; omega)
  rw [List.take_append_drop] at h
  iapply h
  isplitl [Hc]
  · iexact Hc
  · iexact H

theorem mwpi_if_true' {bt : BlockType} {th el : List Instr} {rest : List Value} {c : UInt32} :
    credits Cg K ∗
      ⌜vs.reverse = .i32 c :: rest ∧ (Exec.blockType f.mi bt).params = [] ∧ c₀ ≤ K ∧ c ≠ 0⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ mwpi cfg lim d f [] th
          (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length rest.reverse Φ))
      ⊢ mwpi cfg lim d f vs [.«if» bt th el] Φ := by
  iintro ⟨Hc, %⟨hs, hp, hK, hc⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_if0_true (R := K - c₀) bt th el rest.reverse c hc hp
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  · iexact H

theorem mwpi_if_false' {bt : BlockType} {th el : List Instr} {rest : List Value} {c : UInt32} :
    credits Cg K ∗
      ⌜vs.reverse = .i32 c :: rest ∧ (Exec.blockType f.mi bt).params = [] ∧ c₀ ≤ K ∧ c = 0⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ mwpi cfg lim d f [] el
          (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length rest.reverse Φ))
      ⊢ mwpi cfg lim d f vs [.«if» bt th el] Φ := by
  iintro ⟨Hc, %⟨hs, hp, hK, hc⟩, H⟩
  subst hc
  rw [stack_top1 hs]
  iapply mwpi_if0_false (R := K - c₀) bt th el rest.reverse hp
  isplitl [Hc]
  · rw [Nat.add_sub_cancel' hK]; iexact Hc
  · iexact H

/-- `br_if` taken: the branch; its cost is paid where the label is consumed. -/
theorem mwpi_br_if_taken' {n : Nat} {rest : List Value} {c : UInt32} :
    ⌜vs.reverse = .i32 c :: rest ∧ c ≠ 0⌝ ∗ Φ.br n rest.reverse f
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ := by
  iintro ⟨%⟨hs, hc⟩, H⟩
  rw [stack_top1 hs]
  iapply mwpi_br_if_true n c hc $$ H

theorem mwpi_br_if_not' {n : Nat} {rest : List Value} {c : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 c :: rest ∧ c₀ ≤ K ∧ c = 0⌝ ∗
      ▷ (credits Cg (K - c₀) -∗ Φ.normal rest.reverse f)
      ⊢ mwpi cfg lim d f vs [.br_if n] Φ :=
  credits_flex fun hs hc => by subst hc; rw [stack_top1 hs]; exact mwpi_br_if_false n

theorem mwpi_br_table' {ls : List Nat} {dflt : Nat} {rest : List Value} {c : UInt32} :
    ⌜vs.reverse = .i32 c :: rest⌝ ∗ Φ.br (ls[c.toNat]?.getD dflt) rest.reverse f
      ⊢ mwpi cfg lim d f vs [.br_table ls dflt] Φ := by
  iintro ⟨%hs, H⟩
  rw [stack_top1 hs]
  iapply mwpi_br_table ls dflt c $$ H

/-! ## Payments -/

theorem pay_intro' {k : Nat} {P : IProp GF} :
    credits Cg K ∗ ⌜k ≤ K⌝ ∗ ▷ (credits Cg (K - k) -∗ P) ⊢ pay Cg k P := by
  iintro ⟨Hc, %h, HP⟩
  unfold pay
  iexists K - k
  rw [Nat.add_sub_cancel' h]
  iframe Hc
  iexact HP

theorem pure_pay_intro' {φ : Prop} {k : Nat} {P : IProp GF} :
    credits Cg K ∗ ⌜φ ∧ k ≤ K⌝ ∗ ▷ (credits Cg (K - k) -∗ P) ⊢ ⌜φ⌝ ∗ pay Cg k P := by
  iintro ⟨Hc, %⟨hφ, h⟩, HP⟩
  isplitr
  · ipureintro; exact hφ
  iapply pay_intro'
  iframe Hc HP
  ipureintro; exact h

theorem mfunc_normal_intro' {r : Nat} {Φf : FunPost GF} {g : Frame} :
    credits Cg K ∗ ⌜r ≤ vs.length⌝ ∗ (credits Cg K -∗ Φf.ret (vs.drop (vs.length - r)))
      ⊢ (Post.mfunc cfg Cg r Φf).normal vs g := by
  iintro ⟨Hc, %h, H⟩
  unfold Post.mfunc
  isplitr
  · ipureintro; exact h
  iexists K
  iframe Hc H

theorem mfunc_br_intro' {r n : Nat} {Φf : FunPost GF} {g : Frame} :
    credits Cg K ∗ ⌜r ≤ vs.length ∧ c₀ ≤ K⌝ ∗
      (credits Cg (K - c₀) -∗ Φf.ret (vs.drop (vs.length - r)))
      ⊢ (Post.mfunc cfg Cg r Φf).br n vs g := by
  iintro ⟨Hc, %⟨h, hK⟩, H⟩
  unfold Post.mfunc
  isplitr
  · ipureintro; exact h
  iexists K - c₀
  rw [Nat.add_sub_cancel' hK]
  iframe Hc H

theorem mfunc_ret_intro' {r : Nat} {Φf : FunPost GF} {g : Frame} :
    credits Cg K ∗ ⌜r ≤ vs.length ∧ c₀ ≤ K⌝ ∗
      (credits Cg (K - c₀) -∗ Φf.ret (vs.drop (vs.length - r)))
      ⊢ (Post.mfunc cfg Cg r Φf).ret vs g := by
  iintro ⟨Hc, %⟨h, hK⟩, H⟩
  unfold Post.mfunc
  isplitr
  · ipureintro; exact h
  iexists K - c₀
  rw [Nat.add_sub_cancel' hK]
  iframe Hc H

/-! ## Calls -/

/-- `call i` to a function with a specification, the arguments the top `n`
values of the stack, the credits any amount `K` covering the call, the
activation and the callee's cost. -/
theorem mwpi_call' {i a n : Nat} {type : FuncType} {inst : Nat} {mi : ModuleInst} {code : Func}
    {P : List Value → IProp GF} {Kf : List Value → Nat}
    {Q : List Value → List Value → IProp GF} :
    MFunSpec cfg lim (d + 1) type inst mi code Cg P Kf Q ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ⌜type.params.length = n ∧ n ≤ vs.length ∧ f.mi.funcAddrs[i]? = some a ∧
        d + 1 < lim.maxCallDepth⌝ ∗
      credits Cg K ∗
      ⌜c₀ + activationGas c₀ (entryLocals code (vs.drop (vs.length - n))) +
        Kf (vs.drop (vs.length - n)) ≤ K⌝ ∗
      P (vs.drop (vs.length - n)) ∗
      ▷ (∀ rs, credits Cg (K - (c₀ + activationGas c₀ (entryLocals code (vs.drop (vs.length - n))) +
            Kf (vs.drop (vs.length - n)))) -∗
          Q (vs.drop (vs.length - n)) rs -∗ Φ.normal (vs.take (vs.length - n) ++ rs) f)
      ⊢ mwpi cfg lim d f vs [.call i] Φ := by
  iintro ⟨Hs, Hf, Hi, %⟨hn, hl, ha, hd⟩, Hc, %hK, HP, H⟩
  have h := mwpi_call_spec (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg)
    (R := K - (c₀ + activationGas c₀ (entryLocals code (vs.drop (vs.length - n))) +
      Kf (vs.drop (vs.length - n))))
    i a type inst mi code (vs.take (vs.length - n)) (vs.drop (vs.length - n)) P Kf Q ha
    (by simp; omega) hd
  rw [List.take_append_drop] at h
  iapply h
  have e : c₀ + activationGas c₀ (entryLocals code (vs.drop (vs.length - n))) +
      (Kf (vs.drop (vs.length - n)) + (K - (c₀ + activationGas c₀
        (entryLocals code (vs.drop (vs.length - n))) + Kf (vs.drop (vs.length - n))))) = K := by
    omega
  rw [e]
  iframe Hc Hf Hi Hs HP
  iexact H

end Flex

/-! ## The tactics -/

/-- Normalise after a step in full mode: the sequence and block
postconditions, block types, then `mstep_norm_full`. -/
macro "mctrl_norm" : tactic =>
  `(tactic| (
    (try simp only [Post.mseq_normal, Post.mseq_br, Post.mseq_ret, Post.mseq_trap,
      Post.mblock_normal, Post.mblock_br_zero, Post.mblock_br_succ, Post.mblock_ret,
      Post.mblock_trap, blockType_empty, blockType_val, List.length_nil, List.length_cons,
      List.nil_append, List.append_nil, Nat.sub_zero, List.drop_length, List.drop_zero,
      List.drop_succ_cons, List.drop_nil, UInt32.reduceToNat, List.getElem?_cons_succ,
      List.getElem?_cons_zero, List.getElem?_nil, Option.getD_some, Option.getD_none])
    mstep_norm_full))

/-- A branch condition: `c ≠ 0` or `c = 0`. -/
macro "mcond" : tactic =>
  `(tactic| first
    | decide
    | assumption
    | (simp_all [Numeric.bool]; done)
    | (simp_all [Numeric.bool] <;> omega))

/-- Persistent premises of a specification, from the context. -/
syntax "mpersist" : tactic
macro_rules
  | `(tactic| mpersist) => `(tactic| first | iassumption | iempintro | (isplitr <;> mpersist))

/-- Make one payment from `Hc` (see the module docstring). -/
syntax (name := mpayStx) "mpay" (" with " tactic)? : tactic

open Lean Meta in
/-- The payment rule for an iris goal, if it asks for one. -/
def mpayRule (P : Lean.Expr) : MetaM (Option Name) := do
  let P := P.consumeMData
  if P.isAppOf ``pay then return some ``pay_intro'
  if P.isAppOf ``BIBase.sep && P.getAppNumArgs ≥ 2 then
    let args := P.getAppArgs
    let l := args[args.size - 2]!.consumeMData
    let r := args[args.size - 1]!.consumeMData
    if l.isAppOf ``BIBase.pure && r.isAppOf ``pay then return some ``pure_pay_intro'
  let isMfunc := P.getAppArgs.any fun a => a.consumeMData.isAppOf ``Post.mfunc
  if isMfunc then
    if P.isAppOf ``Post.normal then return some ``mfunc_normal_intro'
    if P.isAppOf ``Post.br then return some ``mfunc_br_intro'
    if P.isAppOf ``Post.ret then return some ``mfunc_ret_intro'
  return none

open Lean Meta Elab Tactic in
/-- The iris goal `P` of `Δ ⊢ P`. -/
def irisGoal : TacticM Lean.Expr := do
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  unless tgt.isAppOfArity ``Iris.ProofMode.Entails' 4 do
    throwError "not in the iris proof mode"
  return tgt.appArg!.consumeMData

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| mpay $[with $tac?]?) => do
    let some rule ← mpayRule (← irisGoal) | throwError "mpay: no payment to make here"
    let ruleId := mkIdent rule
    let hc := mkIdent `Hc
    let side ← match tac? with
      | some t => `(tactic| (and_intros <;> first | ($t; done) | mstep_side))
      | none => `(tactic| mstep_sides)
    evalTactic (← `(tactic| iapply $ruleId:ident))
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| (ipureintro; $side)))
    evalTactic (← `(tactic| try inext))
    evalTactic (← `(tactic| iintro $hc:ident))
    evalTactic (← `(tactic| mctrl_norm))

/-- Full mode: normalise, then make every payment the goal asks for. -/
macro_rules
  | `(tactic| mstep_post $[with $tac?]?) =>
    `(tactic| (mctrl_norm; repeat (mpay $[with $tac?]?)))

/-- Force the direction of a `br_if` or `if`. -/
syntax (name := mstepTakenStx) "mstep_taken" (" with " tactic)? : tactic
@[inherit_doc mstepTakenStx]
syntax (name := mstepNotTakenStx) "mstep_not_taken" (" with " tactic)? : tactic

open Lean Meta Elab Tactic in
/-- Step a control instruction: `dir` is `some true` (taken / `then`),
`some false` (not taken / `else`), or `none` (whichever side condition can be
proved). -/
def mstepCtrl (dir : Option Bool) (tac? : Option (TSyntax `tactic)) : TacticM Unit := do
  let some (i, last) ← mstepTarget
    | throwError "mstep: the fragment is empty"
  let some c := i.getAppFn.constName? | throwError "mstep: no rule for{indentExpr i}"
  let hc := mkIdent `Hc
  let side ← match tac? with
    | some t => `(tactic| (and_intros <;> first | ($t; done) | mstep_side | mcond))
    | none => `(tactic| (and_intros <;> first | mstep_side | mcond))
  let cons : TacticM Unit := unless last do evalTactic (← `(tactic| iapply mwpi_cons))
  -- a rule taking credits: credits, the side conditions, the continuation
  let credStep (rule : Name) : TacticM Unit := do
    let r := mkIdent rule
    cons
    evalTactic (← `(tactic| iapply $r:ident))
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| (ipureintro; $side)))
    evalTactic (← `(tactic| inext))
    evalTactic (← `(tactic| iintro $hc:ident))
  -- a branch: the side conditions, then the branch postcondition
  let brStep (rule : Name) : TacticM Unit := do
    let r := mkIdent rule
    cons
    evalTactic (← `(tactic| iapply $r:ident))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| (ipureintro; $side)))
  let plain (rule : Name) : TacticM Unit := do
    let r := mkIdent rule
    cons
    evalTactic (← `(tactic| iapply $r:ident))
  let either (yes no : TacticM Unit) : TacticM Unit :=
    match dir with
    | some true => yes
    | some false => no
    | none => yes <|> no
  let step : TacticM Unit := match c with
    | ``Instr.block =>
      if dir.isSome then throwError "mstep_taken/mstep_not_taken: not a `br_if` or `if`"
      else credStep ``mwpi_block0' <|> credStep ``mwpi_block'
    | ``Instr.«if» => either (credStep ``mwpi_if_true') (credStep ``mwpi_if_false')
    | ``Instr.br_if => either (brStep ``mwpi_br_if_taken') (credStep ``mwpi_br_if_not')
    | ``Instr.br_table => brStep ``mwpi_br_table'
    | ``Instr.br => plain ``mwpi_br
    | ``Instr.«return» => plain ``mwpi_return
    | ``Instr.call => throwError "mstep: a call; use `mcall spec`"
    | _ => throwError "mstep: no rule for{indentExpr i}\nstep it manually"
  try
    step
  catch e =>
    throwError "mstep: could not step{indentExpr i}\n(for a branch, neither direction's side \
      conditions could be proved: use `mstep_taken with tac` or `mstep_not_taken with tac`)\n\
      {e.toMessageData}"
  evalTactic (← `(tactic| mstep_post $[with $tac?]?))

elab_rules : tactic
  | `(tactic| mstep_ext $[with $tac?]?) => mstepCtrl none tac?

elab_rules : tactic
  | `(tactic| mstep_taken $[with $tac?]?) => mstepCtrl (some true) tac?

elab_rules : tactic
  | `(tactic| mstep_not_taken $[with $tac?]?) => mstepCtrl (some false) tac?

/-- Call a function with a specification; see the module docstring. -/
syntax (name := mcallStx) "mcall " pmTerm (" using " "[" ident* "]")? (" as " ident)? (" with " tactic)? :
  tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| mcall $spec $[using [$hs?*]]? $[as $hq?]? $[with $tac?]?) => do
    let some (i, last) ← mstepTarget | throwError "mcall: the fragment is empty"
    unless i.isAppOf ``Instr.call do throwError "mcall: not a call:{indentExpr i}"
    let hc := mkIdent `Hc
    let hq := hq?.getD (mkIdent `HQ)
    let rs := mkIdent `rs
    let hs : Array Ident := match hs? with
      | some l => l
      | none => #[]
    let first' (dflt : TSyntax `tactic) : TacticM (TSyntax `tactic) := match tac? with
      | some t => `(tactic| first | ($t; done) | ($dflt:tactic))
      | none => pure dflt
    unless last do evalTactic (← `(tactic| iapply mwpi_cons))
    evalTactic (← `(tactic| iapply mwpi_call'))
    -- the specification
    evalTactic (← `(tactic| isplitr))
    let gSpec :: gs ← getGoals | throwError "mcall: unexpected goals"
    setGoals [gSpec]
    evalTactic (← `(tactic| iapply $spec))
    evalTactic (← `(tactic| all_goals (try mpersist)))
    let specLeft ← getGoals
    setGoals gs
    -- the function and the instance
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| (iassumption)))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| (iassumption)))
    -- arity, stack, address, depth
    let arity ← first' (← `(tactic| first | assumption | rfl))
    let other ← first' (← `(tactic| mstep_side))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| ipureintro))
    evalTactic (← `(tactic| refine ⟨?_, ?_, ?_, ?_⟩))
    evalTactic (← `(tactic| focus ($arity:tactic)))
    evalTactic (← `(tactic| focus ($other:tactic)))
    evalTactic (← `(tactic| focus ($other:tactic)))
    evalTactic (← `(tactic| focus ($other:tactic)))
    -- the credits
    evalTactic (← `(tactic| isplitl [$hc:ident]))
    evalTactic (← `(tactic| iexact $hc:ident))
    let cost ← first' (← `(tactic| (mstep_norm_full; omega)))
    evalTactic (← `(tactic| isplitr))
    evalTactic (← `(tactic| focus (ipureintro; $cost)))
    -- the precondition, left to the caller, and the continuation
    evalTactic (← `(tactic| isplitl [$hs*]))
    let gP :: gK ← getGoals | throwError "mcall: unexpected goals"
    setGoals gK
    evalTactic (← `(tactic| inext))
    evalTactic (← `(tactic| iintro %$rs:ident $hc:ident $hq:ident))
    evalTactic (← `(tactic| mstep_post $[with $tac?]?))
    let kLeft ← getGoals
    setGoals [gP]
    evalTactic (← `(tactic| mstep_norm_full))
    let pLeft ← getGoals
    setGoals (specLeft ++ pLeft ++ kLeft)
    pruneSolvedGoals

/-! ## Tests -/

section Test

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

/-- `f(x)`: `block (x == 0 → br 0; local 1 := 7); local 1`, so `7` when
`x ≠ 0`. -/
def testF : Func where
  type := 0
  locals := [.num .i32]
  body := [.block .empty [.local_get 0, .i32_eqz, .br_if 0, .i32_const 7, .local_set 1],
    .local_get 1]

/-- `g()`: a taken `br_if` out of a block, an `if` on `0` (its `else`), a `br 1`
carrying `5` out of an `i32` block, and
`return` past the rest. -/
def testG : Func where
  type := 0
  locals := []
  body := [.block .empty [.i32_const 1, .br_if 0, .unreachable],
    .i32_const 0, .«if» .empty [.unreachable] [.nop],
    .block (.val (.num .i32)) [.block .empty [.i32_const 5, .br 1, .unreachable]],
    .return, .unreachable]

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `testF`, by `mstep`: five instructions in the block (the `br_if` not
taken), the block left normally for free, one after it. -/
theorem testF_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (x : UInt32)
    (hx : x ≠ 0) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi testF Cg (fun args => iprop(⌜args = [.i32 x]⌝))
      (fun _ => 6 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 7]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [testF]
  mstep_norm_full
  mstep                 -- block
  mstep; mstep          -- local.get 0; i32.eqz
  mstep                 -- br_if 0, not taken: x ≠ 0
  mstep; mstep          -- i32.const 7; local.set 1; the block left, paying 0
  mstep                 -- local.get 1; the function ends
  isplitl [Hc]
  · iexact Hc
  · ipureintro; simp [htype]

/-- `testG`, by `mstep`: a taken `br_if` (its branch paid at the label), an
`if` not taken, a `br 1` out of two blocks, and `return`. -/
theorem testG_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi testG Cg (fun args => iprop(⌜args = []⌝))
      (fun _ => 8 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 5]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [testG]
  mstep                 -- block
  mstep; mstep          -- i32.const 1; br_if 0, taken, paying the branch
  mstep                 -- i32.const 0
  mstep                 -- if, not taken
  mstep                 -- nop; the else block left
  mstep; mstep          -- two blocks, the outer one of type `i32`
  mstep; mstep          -- i32.const 5; br 1, paying the branch
  mstep                 -- return, paying it
  isplitl [Hc]
  · iexact Hc
  · ipureintro; simp [htype]

/-- A call: `testF(3)` by `mcall`, then `drop`. The call costs one
`regular_op_cost`, the activation of `#[.i32 3, .i32 0]` nine, `testF` six. -/
example (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF) (Cg R : Nat)
    (type : FuncType) (htype : type.results.length = 1) (hparams : type.params.length = 1)
    (inst a : Nat) (mi : ModuleInst) (f : Frame) (ha : f.mi.funcAddrs[0]? = some a)
    (hd : d + 1 < lim.maxCallDepth) :
    a ↪[wf] FuncInst.wasm type inst testF ∗ inst ↪[inst] mi ∗
      credits Cg (18 * cfg.regularOpCost + R) ∗ (credits Cg R -∗ Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] [.i32_const 3, .call 0, .drop] Φ := by
  iintro ⟨#Hf, #Hi, Hc, HΦ⟩
  mstep
  mcall (testF_spec cfg lim (d + 1) type htype inst mi Cg 3 (by decide))
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep
  iapply HΦ $$ Hc

/-- A `br_if` forced not taken, and `br_table` on a literal index (`1`: out of
both blocks). -/
example (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF) (Cg R : Nat)
    (f : Frame) :
    credits Cg (4 * cfg.regularOpCost + R) ∗ (credits Cg R -∗ Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] [.block .empty [.block .empty [.i32_const 0, .br_if 0, .i32_const 1,
          .br_table [0, 1] 0, .unreachable], .unreachable]] Φ := by
  iintro ⟨Hc, HΦ⟩
  mstep; mstep
  mstep
  mstep_not_taken
  mstep
  mstep
  iapply HΦ $$ Hc

/-- Loads and stores at their points-to's own address: a constant address
(`i32.const 0`, offset 1074920) and a computed one (`(x + 8).toNat` with
offset 4) against points-to stated at `1074920` and `x.toNat + 12`; the
locals of a literal frame after `local.set`. -/
example (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF) (Cg R : Nat)
    (n inst : Nat) (mi : ModuleInst) (hn : mi.memAddrs[0]? = some n) (x w v : UInt32)
    (hx : x.toNat + 16 < 2 ^ 32) :
    credits Cg (9 * cfg.regularOpCost + R) ∗ n ↦[i32][ 1074920 ] w ∗ n ↦[i32][ x.toNat + 12 ] v ∗
      (credits Cg R -∗ n ↦[i32][ 1074920 ] v -∗ n ↦[i32][ x.toNat + 12 ] v -∗
        Φ.normal [] ⟨#[.i32 x, .i32 v], inst, mi⟩)
      ⊢ mwpi cfg lim d ⟨#[.i32 x, .i32 0], inst, mi⟩ []
          [.local_get 0, .i32_const 8, .i32_binop .add, .load .i32 none ⟨2, 4⟩, .local_set 1,
            .i32_const 0, .local_get 1, .store .i32 none ⟨2, 1074920⟩, .nop] Φ := by
  iintro ⟨Hc, Hw, Hv, HΦ⟩
  mstep; mstep; mstep
  mstep [Hv]
  mstep
  mstep; mstep
  mstep [Hw]
  mstep
  iapply HΦ $$ Hc Hw Hv

end Test

end NearLogic
