import NearVM.HostDispatch
import NearVM.MeteredInvariant
import NearVM.InterpreterInvariant

/-!
Dependency preservation through the authoritative small-step interpreter and
its metered runner. This invariant concerns promise references; it does not
assert action validity, numeric bounds, or token conservation.
-/

namespace Wasm.Near

/-- Every callable host in every instance preserves promise dependencies.
Foreign-function slots are included because indirect calls can reach them. -/
def RuntimePreservesPromises (runtime : SmallStep.RuntimeEnv NearState) : Prop :=
  ∀ (index : Nat) (fn : HostFn NearState), (fn ∈ (runtime.instances[index]!).host.funcs ∨
    fn ∈ (runtime.instances[index]!).host.foreignFuncs) → HostPreservesPromises fn

theorem RuntimePreservesPromises.of_hosts_eq {before after : SmallStep.RuntimeEnv NearState}
    (h : ∀ (slot : Nat), (after.instances[slot]!).host = (before.instances[slot]!).host)
    (hhosts : RuntimePreservesPromises before) : RuntimePreservesPromises after := by
  intro slot fn hmember
  apply hhosts slot fn
  simpa only [h slot] using hmember

theorem step_instances {before after : SmallStep.Config NearState} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after) :
    after.store.runtime.instances = before.store.runtime.instances := by
  exact SmallStep.instances_preserved h

theorem hostReturn_promises {runtime : SmallStep.RuntimeEnv NearState}
    {fn : HostFn NearState} {st after : Store NearState} {args : List Value}
    (values : List Value)
    (hcall : fn.invoke st args = .Return values after)
    (hhosts : RuntimePreservesPromises runtime)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    PromisesWellFormedFrom 0 after.host.promises := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

theorem hostTrap_promises {runtime : SmallStep.RuntimeEnv NearState}
    {fn : HostFn NearState} {st after : Store NearState} {args : List Value}
    (message : String)
    (hcall : fn.invoke st args = .Trap after message)
    (hhosts : RuntimePreservesPromises runtime)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    PromisesWellFormedFrom 0 after.host.promises := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

theorem hostThrow_promises {runtime : SmallStep.RuntimeEnv NearState}
    {fn : HostFn NearState} {st after : Store NearState} {args : List Value}
    (tag : Nat) (values : List Value)
    (hcall : fn.invoke st args = .Throw after tag values)
    (hhosts : RuntimePreservesPromises runtime)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    PromisesWellFormedFrom 0 after.host.promises := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

set_option maxHeartbeats 2000000 in
theorem step_promises {before after : SmallStep.Config NearState} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after)
    (hhosts : RuntimePreservesPromises before.store.runtime)
    (hwf : PromisesWellFormedFrom 0 before.store.wasm.host.promises) :
    PromisesWellFormedFrom 0 after.store.wasm.host.promises := by
  exact step_hostInvariant (P := fun ns : NearState => PromisesWellFormedFrom 0 ns.promises) h hhosts hwf

/-- The dependency invariant includes the callable environments needed by
subsequent steps, including cross-instance calls. -/
def ConfigPromisesValid (config : SmallStep.Config NearState) : Prop :=
  RuntimePreservesPromises config.store.runtime ∧
    PromisesWellFormedFrom 0 config.store.wasm.host.promises

theorem step_preserves_promises {before after : SmallStep.Config NearState} {kind : SmallStep.StepKind}
    (hstep : SmallStep.Step before kind after) (h : ConfigPromisesValid before) :
    ConfigPromisesValid after := by
  refine ⟨?_, step_promises hstep h.1 h.2⟩
  apply RuntimePreservesPromises.of_hosts_eq _ h.1
  intro slot
  rw [step_instances hstep]

theorem chargeWasm_preserves_promises (config : SmallStep.Config NearState) (cost : Nat)
    (h : ConfigPromisesValid config) : ConfigPromisesValid (chargeWasm config cost).1 := by
  exact h

/-- Dependency validity survives every exit, including fuel exhaustion, gas
exhaustion and diagnostic errors, without relying on output validation. -/
theorem runMetered_preserves_promises (cfg : WasmConfig) (fuel : Nat)
    (config : SmallStep.Config NearState) (h : ConfigPromisesValid config) :
    ConfigPromisesValid (runMetered cfg fuel config).1 := by
  exact runMetered_hostInvariant (fun ns => PromisesWellFormedFrom 0 ns.promises)
    (by intro config cost hwf; exact hwf) cfg fuel config h

theorem steps_preserve_promises {before after : SmallStep.Config NearState} {trace : List SmallStep.StepKind}
    (hsteps : SmallStep.Steps before trace after) (h : ConfigPromisesValid before) :
    ConfigPromisesValid after := by
  induction hsteps with
  | refl => exact h
  | cons head tail ih => exact ih (step_preserves_promises head h)

theorem singleton_runtime_preserves (instance_ : SmallStep.ModuleInstance NearState)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostPreservesPromises fn) :
    RuntimePreservesPromises { instances := #[instance_], entry := ⟨0⟩ } := by
  intro index fn hmember
  cases index with
  | zero => exact hhosts fn (by simpa using hmember)
  | succ index =>
    simp only [getElem!_def, Array.getElem?_singleton, Nat.succ_ne_zero, ite_false] at hmember
    change fn ∈ ([] : List (HostFn NearState)) ∨ fn ∈ [] at hmember
    simp at hmember

theorem initConfig_promises {instance_ : SmallStep.ModuleInstance NearState} {entry : Nat}
    {st : Store NearState} {args : List Value} {config : SmallStep.Config NearState}
    (hinit : SmallStep.initConfig instance_ entry st args = .ok config)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostPreservesPromises fn)
    (hwf : PromisesWellFormedFrom 0 st.host.promises) : ConfigPromisesValid config := by
  unfold SmallStep.initConfig at hinit
  split at hinit <;> split at hinit <;> simp only [Except.ok.injEq, reduceCtorEq] at hinit
  all_goals subst config; exact ⟨singleton_runtime_preserves instance_ hhosts, hwf⟩

theorem resolveMeteredImports_noForeign (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    env.foreignFuncs = [] := by
  induction imports generalizing env with
  | nil =>
    simp only [resolveMeteredImports, Except.ok.injEq] at h
    subst env
    rfl
  | cons decl rest _ =>
    cases hf : (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => simp [resolveMeteredImports, hf] at h
    | some entry =>
      obtain ⟨found, fn⟩ := entry
      cases hr : resolveMeteredImports cfg rest with
      | error message => simp [resolveMeteredImports, hf, hr] at h
      | ok tail =>
        simp only [resolveMeteredImports, hf, hr, Except.ok.injEq] at h
        subst env
        rfl

theorem initResolvedConfig_promises {cfg : RuntimeConfig} {code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hwf : PromisesWellFormedFrom 0 st.host.promises) : ConfigPromisesValid config := by
  apply initConfig_promises hinit _ hwf
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact resolveMetered_preserves cfg code env hresolve fn hmember
  · have hempty := resolveMeteredImports_noForeign cfg code.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

/-- Actual resolved execution produces a convertible valid dependency graph
without a post-execution graph validator as a premise. -/
theorem runResolved_promises_convertible {cfg : RuntimeConfig} {code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    ∃ graph, convertPromises (runMetered cfg.wasm fuel config).1.store.wasm.host.promises = some graph ∧
      graph.Valid := by
  have hfinal := runMetered_preserves_promises cfg.wasm fuel config
    (initResolvedConfig_promises hresolve hinit hwf)
  obtain ⟨graph, hgraph⟩ := convertPromises_total _ hfinal.2
  exact ⟨graph, hgraph, convertPromises_valid hgraph⟩

end Wasm.Near
