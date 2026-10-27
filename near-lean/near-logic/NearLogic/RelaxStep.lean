import NearLogic.Hosts.ValueReturnRelax

/-!
# Steps under raised gas limits

A host function *respects raised limits* (`RelaxFn`) when, run on a host
whose gas limits are raised, it gives the same outcome with those limits,
unless under the lower limits it traps with a gas error recorded in the
host (a failed charge). The linked `value_return` does.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host outcome with its host's limits raised. -/
def _root_.Wasm.HostOutcome.relax (p m : Nat) : HostOutcome NearState → HostOutcome NearState
  | .return vs h mem => .return vs (NearLogic.relax h p m) mem
  | .trap r h mem => .trap r (NearLogic.relax h p m) mem

/-- A trap whose host records a gas error: a failed charge. -/
def GasTrap (o : HostOutcome NearState) : Prop :=
  ∃ r h mem e, o = .trap r h mem ∧ h.lastError = some e ∧ isGasError e

/-- The host function respects raised limits. -/
def RelaxFn (fn : HostFn NearState) : Prop :=
  ∀ host mem args p m, host.gas.prepaid ≤ p → host.gas.maxBurnt ≤ m →
    GasTrap (fn.call host mem args) ∨ fn.call (relax host p m) mem args = (fn.call host mem args).relax p m

theorem valueReturn_relaxFn (extra : Nat) : RelaxFn (metered extra "value_return" valueReturnFn).toHostFn := by
  intro host mem args p m hp hm
  rcases meteredValueReturn_relax extra { mem := mem.getD (Memory.new 0 none), host } args p m hp hm with
    ⟨st', e, hinv, he⟩ | hrel
  · left
    refine ⟨.host e.message, { st'.host with lastError := some e }, some st'.mem, e, ?_, rfl, he⟩
    simp only [NearHostFn.toHostFn, hinv, trapWith]
  · right
    simp only [NearHostFn.toHostFn]
    have : ({ mem := mem.getD (Memory.new 0 none), host := relax host p m } : HostStore NearState) =
        relaxSt { mem := mem.getD (Memory.new 0 none), host } p m := rfl
    rw [this, hrel]
    cases (metered extra "value_return" valueReturnFn).invoke { mem := mem.getD (Memory.new 0 none), host } args <;>
      rfl

/-! ## One step -/

/-- A store with its host's limits raised. -/
def relaxStore (σ : Store NearState) (p m : Nat) : Store NearState := { σ with host := relax σ.host p m }

/-- A step result with its store's host limits raised. -/
def _root_.Wasm.StepResult.relax (p m : Nat) : StepResult NearState → StepResult NearState
  | .next c => .next { c with store := relaxStore c.store p m }
  | .done vs s => .done vs (relaxStore s p m)
  | .trap r s => .trap r (relaxStore s p m)

/-- A trap whose host records a gas error. -/
def GasStep (r : StepResult NearState) : Prop :=
  ∃ reason s e, r = .trap reason s ∧ s.host.lastError = some e ∧ isGasError e

/-- Every host function of the store respects raised limits. -/
def StoreRelaxFns (σ : Store NearState) : Prop :=
  ∀ (a : Nat) (fn : HostFn NearState), σ.funcs[a]? = some (FuncInst.host fn) → RelaxFn fn

theorem leave_relax (c : Config NearState) (σ : Store NearState) (stack : Array Value) (frame : CallFrame)
    (frames : List CallFrame) (p m : Nat) :
    Exec.leave c (relaxStore σ p m) stack frame frames = (Exec.leave c σ stack frame frames).relax p m := by
  unfold Exec.leave
  dsimp only
  split <;> rfl

theorem commitHost_relax (σ : Store NearState) (ci : Option ModuleInst) (h : NearState) (mem : Option Memory)
    (p m : Nat) :
    Exec.commitHost σ ci (relax h p m) mem = relaxStore (Exec.commitHost σ ci h mem) p m := by
  unfold Exec.commitHost Store.setMemOf
  split
  · split <;> rfl
  · rfl

theorem commitHost_relaxStore (σ : Store NearState) (ci : Option ModuleInst) (h : NearState)
    (mem : Option Memory) (p m : Nat) :
    Exec.commitHost (relaxStore σ p m) ci (relax h p m) mem = relaxStore (Exec.commitHost σ ci h mem) p m := by
  unfold Exec.commitHost Store.setMemOf
  split
  · split <;> rfl
  · rfl

theorem enter_relax (c : Config NearState) (stack : Array Value) (frames : List CallFrame) (addr : Nat) (p m : Nat)
    (hp : c.store.host.gas.prepaid ≤ p) (hm : c.store.host.gas.maxBurnt ≤ m) (hf : StoreRelaxFns c.store) :
    GasStep (Exec.enter c stack frames addr) ∨
      Exec.enter { c with store := relaxStore c.store p m } stack frames addr =
        (Exec.enter c stack frames addr).relax p m := by
  unfold Exec.enter
  dsimp only
  cases hfn : c.store.funcs[addr]? with
  | none => right; simp only [relaxStore, hfn]; rfl
  | some f =>
    have hfn' : (relaxStore c.store p m).funcs[addr]? = some f := hfn
    rw [hfn']
    cases f with
    | wasm type inst code => right; simp only [relaxStore]; split <;> rfl
    | host fn =>
      simp only
      rcases hf addr fn hfn c.store.host _ _ p m hp hm with ⟨r, h, mem, e, hcall, hl, he⟩ | hrel
      · left
        rw [hcall]
        refine ⟨r, _, e, rfl, ?_, he⟩
        rw [Exec.commitHost_host]
        exact hl
      · right
        have hmemOf : (relaxStore c.store p m).memOf = c.store.memOf := rfl
        have hmods : (relaxStore c.store p m).modules = c.store.modules := rfl
        have hhost : (relaxStore c.store p m).host = relax c.store.host p m := rfl
        simp only [hmemOf, hmods, hhost]
        rw [hrel]
        cases fn.call c.store.host _ _ with
        | «return» values host mem' =>
          simp only [HostOutcome.relax]
          rw [commitHost_relaxStore]
          split <;> rfl
        | trap reason host mem' =>
          simp only [HostOutcome.relax]
          rw [commitHost_relaxStore]
          rfl

/-- One step of the machine under raised limits: the same step with those
limits, unless the step is a host call that fails a charge. -/
theorem step_relax (c : Config NearState) (p m : Nat) (hp : c.store.host.gas.prepaid ≤ p)
    (hm : c.store.host.gas.maxBurnt ≤ m) (hf : StoreRelaxFns c.store) :
    GasStep (Exec.step c) ∨ Exec.step { c with store := relaxStore c.store p m } = (Exec.step c).relax p m := by
  obtain ⟨σ, ⟨stack, frames⟩, lim⟩ := c
  cases frames with
  | nil => right; rfl
  | cons frame frames =>
    simp only [Exec.step]
    split
    · right
      rw [Exec.leave_congr (c' := ⟨σ, ⟨stack, frame :: frames⟩, lim⟩) rfl]
      exact leave_relax _ σ stack frame frames p m
    · right; rfl
    · rename_i _ i rest _
      have hmods : (relaxStore σ p m).modules = σ.modules := rfl
      rw [hmods, show relaxStore σ p m = { σ with host := relax σ.host p m } from rfl,
        instr_withHost σ (relax σ.host p m) σ.modules[frame.inst]! frame.locals stack frame.labels i rest]
      obtain ⟨hsh, hsf⟩ := Exec.instr_store σ σ.modules[frame.inst]! frame.locals stack frame.labels i rest
      generalize Exec.instr σ σ.modules[frame.inst]! frame.locals stack frame.labels i rest = eff at hsh hsf ⊢
      obtain ⟨st, kind⟩ := eff
      simp only at hsh hsf
      have hst : ({ st with host := relax σ.host p m } : Store NearState) = relaxStore st p m := by
        rw [← hsh]; rfl
      cases kind with
      | «continue» stack' labels' code' locals' =>
        right; simp only [Exec.Effect.withHost, hst]; rfl
      | call stack' addr rest' =>
        simp only [Exec.Effect.withHost, hst]
        have := enter_relax { store := st, thread := { stack := stack, frames := frame :: frames }, limits := lim }
          stack' ({ frame with code := rest' } :: frames) addr p m (by rw [hsh]; exact hp) (by rw [hsh]; exact hm)
          (fun a fn h => hf a fn (by rw [← hsf]; exact h))
        exact this
      | «return» stack' =>
        right; simp only [Exec.Effect.withHost, hst]
        rw [Exec.leave_congr (c' := ⟨σ, ⟨stack, frame :: frames⟩, lim⟩) rfl]
        exact leave_relax _ st stack' frame frames p m
      | trap reason =>
        right; simp only [Exec.Effect.withHost, hst]; rfl

end NearLogic
