import Spec.Views

/-!
# View methods and initialisation
-/

namespace WNear

@[simp] theorem throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

/-- Simp set that evaluates `step` on a concrete call. -/
local macro "step_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [step, dispatch, Call.isPayable, Call.isView, Call.isPrivate, require,
      pure, Except.pure, bind, Except.bind, Except.ok.injEq] $[$loc]?)

@[blueprint "thm:views-pure"
  (statement := /-- \cref{spec:views-pure} holds. -/)]
theorem views_pure : ViewsPure := by
  intro cfg s env call o hview hstep
  cases call <;> simp [Call.isView] at hview <;> step_simp at hstep <;> subst hstep <;> simp

@[blueprint "thm:views-total"
  (statement := /-- \cref{spec:views-total} holds. -/)]
theorem views_total : ViewsTotal := by
  intro cfg s env call hview
  cases call <;> simp [Call.isView] at hview <;> step_simp

@[blueprint "thm:balance-of"
  (statement := /-- \cref{spec:balance-of} holds. -/)]
theorem balance_of_correct : BalanceOfCorrect := by
  intro cfg s env a o hinv hstep
  step_simp at hstep
  subst hstep
  simp [State.balanceOf_eq_balance hinv.toWF]

@[blueprint "thm:total-supply"
  (statement := /-- \cref{spec:total-supply} holds. -/)]
theorem total_supply_correct : TotalSupplyCorrect := by
  intro cfg s env o hinv hstep
  step_simp at hstep
  subst hstep
  simp [hinv.supply]

@[blueprint "thm:init-once"
  (statement := /-- \cref{spec:init-once} holds. -/)]
theorem init_once : InitOnce := by
  refine ⟨?_, ?_⟩
  · intro cfg s env hdep
    step_simp
    simp [hdep]
  · intro cfg env call hcall
    cases call <;> simp at hcall <;> (step_simp; repeat' split) <;> simp

end WNear
