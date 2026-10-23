import WasmLogic.Frag
import Lean

/-!
# Tactics for stepping through code

`wp_step k rule` runs the first instruction of the fragment in the goal with
`rule`, an instruction rule that consumes `k` operands: it splits the
operand stack into its bottom and its top `k` values so that the rule's
conclusion matches syntactically, applies the rule, and leaves its premise.
-/

namespace WasmLogic

open Lean Meta Elab Tactic in
/-- Close `a = b` by `Eq.refl`, checked by the kernel only, as `decide +kernel`
does for decidable propositions: for equations the elaborator cannot unfold
(the validator and decoder use well-founded recursion) but the kernel
evaluates. Sound: the auxiliary lemma is type-checked by the kernel. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (ty, lhs, _) := tgt.eq? | throwError "kernel_rfl: the goal is not an equation"
  let lvl ← getLevel ty
  let pf := mkApp2 (mkConst ``Eq.refl [lvl]) ty lhs
  let levelsInType := (collectLevelParams {} tgt).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels tgt pf
  goal.assign (mkConst name (lemmaLevels.map .param))

theorem toArray_set! {α} (l : List α) (i : Nat) (v : α) : l.toArray.set! i v = (l.set i v).toArray := by
  simp [Array.set!]

/-- Normalise locals: `set!` on a literal array is a literal array. -/
macro "wp_locals" : tactic =>
  `(tactic| (try simp only [toArray_set!, List.set_cons_zero, List.set_cons_succ, List.set_nil]))

/-- Normalise an operand stack to a list literal. -/
macro "wp_norm" : tactic =>
  `(tactic| (try simp only [List.nil_append, List.cons_append, List.append_nil, List.append_assoc]))

/-- Split the operand stack, after normalising it, into bottom and top `k`. -/
macro "wp_split " k:num : tactic =>
  `(tactic| (
    iapply (wpi_split $k)
    try simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.sub_self,
      Nat.zero_sub, Nat.sub_zero, List.take_zero, List.drop_zero, List.take_succ_cons,
      List.drop_succ_cons, List.take_nil, List.drop_nil]))

/-- Apply `rule` to a one-instruction fragment, splitting off `k` operands. -/
macro "wp_apply " k:num r:pmTerm : tactic =>
  `(tactic| (
    wp_norm
    wp_split $k
    iapply $r))

/-- Run the first instruction with `rule`, which consumes `k` operands. -/
macro "wp_step " k:num r:pmTerm : tactic =>
  `(tactic| (
    iapply wpi_cons
    wp_apply $k $r))

end WasmLogic
