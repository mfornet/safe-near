import Wasm
import Iris.ProgramLogic.Language

/-!
# The Wasm machine as an iris-lean language

An expression is a running thread with its execution limits, or a finished
outcome; the state is the store. The primitive step is `Wasm.Exec.step`,
which is a function, so the step relation is deterministic, silent and never
forks. Traps are values of the language: a trapped machine is finished, and
whether that is acceptable is for postconditions to say.
-/

namespace WasmLogic

open Wasm Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib

/-- How a call ended. -/
inductive Outcome where
  | values (vs : List Value)
  | trap (reason : Trap)
deriving DecidableEq, Inhabited, Repr

/-- A thread still running, or a finished one. -/
inductive Code (H : Type) where
  | running (limits : ExecLimits) (thread : Thread)
  | finished (outcome : Outcome)

/-- The machine configuration of a running thread over a store. -/
def Code.config (store : Store H) (limits : ExecLimits) (thread : Thread) : Config H :=
  { store, thread, limits }

/-- What `Exec.step` does to a thread, as an expression and a store. -/
def next (store : Store H) (limits : ExecLimits) (thread : Thread) : Code H × Store H :=
  match Exec.step (Code.config store limits thread) with
  | .next c => (.running limits c.thread, c.store)
  | .done vs s => (.finished (.values vs), s)
  | .trap r s => (.finished (.trap r), s)

instance instToVal : ToVal (Code H) Outcome where
  toVal
    | .running _ _ => none
    | .finished o => some o
  ofVal := .finished
  coe_of_toVal_eq_some := by
    intro e v h
    cases e <;> simp_all
  toVal_coe := by intro v; rfl

/-- Silent, deterministic, no forks. -/
instance instPrimStep : PrimStep (Code H) (Store H) (List Unit) where
  primStep source obs target :=
    obs = [] ∧ target.2.2 = [] ∧
    ∃ limits thread, source.1 = .running limits thread ∧
      (target.1, target.2.1) = next source.2 limits thread

instance instLanguage : Language (Code H) (Store H) Unit Outcome where
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨_, _, limits, thread, he, _⟩ := h
    subst he
    rfl

theorem step_iff {limits : ExecLimits} {thread : Thread} {σ σ' : Store H} {e' : Code H}
    {obs : List Unit} {eₜ : List (Code H)} :
    (Code.running limits thread, σ) -<obs>-> (e', σ', eₜ) ↔
      obs = [] ∧ eₜ = [] ∧ (e', σ') = next σ limits thread := by
  constructor
  · rintro ⟨hobs, hforks, l, t, he, hnext⟩
    cases he
    exact ⟨hobs, hforks, hnext⟩
  · rintro ⟨hobs, hforks, hnext⟩
    exact ⟨hobs, hforks, limits, thread, rfl, hnext⟩

/-- Every running thread can step: the machine is total. -/
theorem running_reducible (limits : ExecLimits) (thread : Thread) (σ : Store H) :
    PrimStep.Reducible (Code.running limits thread, σ) :=
  ⟨[], (next σ limits thread).1, (next σ limits thread).2, [],
    step_iff.mpr ⟨rfl, rfl, rfl⟩⟩

/-- The step is deterministic: whatever a step produces is `next`. -/
theorem step_det {limits : ExecLimits} {thread : Thread} {σ σ' : Store H} {e' : Code H}
    {obs : List Unit} {eₜ : List (Code H)}
    (h : (Code.running limits thread, σ) -<obs>-> (e', σ', eₜ)) :
    obs = [] ∧ eₜ = [] ∧ e' = (next σ limits thread).1 ∧
      σ' = (next σ limits thread).2 := by
  obtain ⟨hobs, hforks, hnext⟩ := step_iff.mp h
  exact ⟨hobs, hforks, congrArg Prod.fst hnext, congrArg Prod.snd hnext⟩

/-! ## Runs of the machine as thread-pool steps -/

/-- The outcome `Exec.run` reports, as an expression and a store. -/
def RunResult.code : Exec.RunResult H → Code H × Store H
  | .done vs s => (.finished (.values vs), s)
  | .trap r s => (.finished (.trap r), s)
  | .outOfFuel c => (.running c.limits c.thread, c.store)

/-- `Exec.run` is a sequence of language steps from the single thread. -/
theorem run_steps (fuel : Nat) (store : Store H) (limits : ExecLimits) (thread : Thread) :
    ([Code.running limits thread], store) -·->ₜₚ*
      ([(RunResult.code (Exec.run fuel (Code.config store limits thread))).1],
        (RunResult.code (Exec.run fuel (Code.config store limits thread))).2) := by
  induction fuel generalizing store thread with
  | zero => exact .refl
  | succ fuel ih =>
    unfold Exec.run
    simp only [Code.config] at ih ⊢
    cases hc : Exec.step { store := store, thread := thread, limits := limits } with
    | next c =>
      have hl := Exec.step_limits _ hc
      have ih' := ih c.store c.thread
      have hc' : ({ store := c.store, thread := c.thread, limits := limits } : Config H) = c := by
        cases c; simp_all
      rw [hc'] at ih'
      refine Relation.ReflTransGen.head ?_ ih'
      refine ⟨[], .atomic (step_iff.mpr ⟨rfl, rfl, ?_⟩) [] []⟩
      simp [next, Code.config, hc]
    | done vs s =>
      refine .single ⟨[], .atomic (step_iff.mpr ⟨rfl, rfl, ?_⟩) [] []⟩
      simp [next, Code.config, hc, RunResult.code]
    | trap r s =>
      refine .single ⟨[], .atomic (step_iff.mpr ⟨rfl, rfl, ?_⟩) [] []⟩
      simp [next, Code.config, hc, RunResult.code]

end WasmLogic
