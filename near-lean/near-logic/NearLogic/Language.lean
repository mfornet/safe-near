import WasmLogic.Resources
import NearVM.Run

/-!
# NEAR's metered machine as an iris-lean language

The machine `Wasm.Near.runMetered` runs: before each instruction it charges
the instruction's cost (`nextInstructionGas`) to the host's gas counter,
then takes a step of `Wasm.Exec.step`, then charges a new frame's activation
(`frameTransitionGas`). A failed charge stops the machine with the host
error. `mnext` is one such step; `runMetered_succ` says `runMetered` is a
sequence of them.

An expression is a running thread, with the Wasm cost table and the
execution limits, or a finished one; the state is the store, whose host
state is NEAR's (`NearState`). As in WasmLogic, the step is a function, so
it is deterministic, silent and never forks.
-/

namespace NearLogic

open Wasm Wasm.Near Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib

/-- The state of the metered language: a store. A type of its own, so that
its state interpretation is not WasmLogic's. -/
structure MStore where
  store : Store NearState

/-- How a metered run ended. -/
inductive Ending where
  | values (vs : List Value)
  | trap (reason : Trap)
  /-- A gas charge failed, with the error the charge reported. -/
  | gas (error : HostError)

/-- A thread still running, or a finished one. -/
inductive MCode where
  | running (cfg : WasmConfig) (limits : ExecLimits) (thread : Thread)
  | finished (ending : Ending)

/-- The expression a machine state is, once its charges succeeded. -/
def ofMachine (cfg : WasmConfig) (lim : ExecLimits) : StepResult NearState → MCode
  | .next c => .running cfg lim c.thread
  | .done vs _ => .finished (.values vs)
  | .trap r _ => .finished (.trap r)

/-- One metered step, as `runMetered` takes it. -/
def mnext (σ : MStore) (cfg : WasmConfig) (lim : ExecLimits) (t : Thread) : MCode × MStore :=
  let c : Config NearState := { store := σ.store, thread := t, limits := lim }
  let charged := chargeConfig c (nextInstructionGas cfg c)
  match charged.2 with
  | some e => (.finished (.gas e), ⟨charged.1.store⟩)
  | none =>
    let nx := Exec.step charged.1
    let charged' := chargeWasm nx (frameTransitionGas cfg charged.1 nx)
    match charged'.2 with
    | some e => (.finished (.gas e), ⟨charged'.1.store⟩)
    | none => (ofMachine cfg lim charged'.1, ⟨charged'.1.store⟩)

instance instToVal : ToVal MCode Ending where
  toVal
    | .running .. => none
    | .finished e => some e
  ofVal := .finished
  coe_of_toVal_eq_some := by
    intro e v h
    cases e <;> simp_all
  toVal_coe := by intro v; rfl

/-- Silent, deterministic, no forks. -/
instance instPrimStep : PrimStep MCode MStore (List Unit) where
  primStep source obs target :=
    obs = [] ∧ target.2.2 = [] ∧
    ∃ cfg limits thread, source.1 = .running cfg limits thread ∧
      (target.1, target.2.1) = mnext source.2 cfg limits thread

instance instLanguage : Language MCode MStore Unit Ending where
  val_stuck := by
    intro e σ obs e' σ' eₜ h
    obtain ⟨_, _, cfg, limits, thread, he, _⟩ := h
    subst he
    rfl

theorem step_iff {cfg : WasmConfig} {limits : ExecLimits} {thread : Thread} {σ σ' : MStore}
    {e' : MCode} {obs : List Unit} {eₜ : List MCode} :
    (MCode.running cfg limits thread, σ) -<obs>-> (e', σ', eₜ) ↔
      obs = [] ∧ eₜ = [] ∧ (e', σ') = mnext σ cfg limits thread := by
  constructor
  · rintro ⟨hobs, hforks, c, l, t, he, hnext⟩
    cases he
    exact ⟨hobs, hforks, hnext⟩
  · rintro ⟨hobs, hforks, hnext⟩
    exact ⟨hobs, hforks, cfg, limits, thread, rfl, hnext⟩

theorem running_reducible (cfg : WasmConfig) (limits : ExecLimits) (thread : Thread) (σ : MStore) :
    PrimStep.Reducible (MCode.running cfg limits thread, σ) :=
  ⟨[], (mnext σ cfg limits thread).1, (mnext σ cfg limits thread).2, [],
    step_iff.mpr ⟨rfl, rfl, rfl⟩⟩

theorem step_det {cfg : WasmConfig} {limits : ExecLimits} {thread : Thread} {σ σ' : MStore}
    {e' : MCode} {obs : List Unit} {eₜ : List MCode}
    (h : (MCode.running cfg limits thread, σ) -<obs>-> (e', σ', eₜ)) :
    obs = [] ∧ eₜ = [] ∧ e' = (mnext σ cfg limits thread).1 ∧
      σ' = (mnext σ cfg limits thread).2 := by
  obtain ⟨hobs, hforks, hnext⟩ := step_iff.mp h
  exact ⟨hobs, hforks, congrArg Prod.fst hnext, congrArg Prod.snd hnext⟩

end NearLogic
