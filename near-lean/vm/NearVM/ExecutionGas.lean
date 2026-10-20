import NearVM.HostGasLimits

namespace Wasm.Near

/-- Interpreter initialization carries the supplied counter without changes. -/
theorem initConfig_gas {instance_ : SmallStep.ModuleInstance NearState} {entry : Nat}
    {st : Store NearState} {args : List Value} {config : SmallStep.Config NearState}
    (hinit : SmallStep.initConfig instance_ entry st args = .ok config) :
    config.store.wasm.host.gas = st.host.gas := by
  unfold SmallStep.initConfig at hinit
  split at hinit <;> split at hinit <;> simp only [Except.ok.injEq, reduceCtorEq] at hinit
  all_goals subst config; rfl

/-- A resolved registry supplies the host invariant required by the interpreter.
The module used at initialization may have adjusted memory declarations. -/
theorem initResolvedConfig_gasLimits {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config) :
    ConfigHostInvariant (GasLimits st.host.gas.prepaid st.host.gas.maxBurnt) config := by
  apply initConfig_hostInvariant hinit _ ⟨rfl, rfl⟩
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact resolveMetered_gasLimits cfg resolvedCode env hresolve fn hmember _ _
  · have hempty := resolveMeteredImports_noForeign cfg resolvedCode.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

/-- Executable resolved calls preserve the original call's gas limits without
an assumed host-invariant oracle. -/
theorem runResolved_gas_limits {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config) :
    let gas := (runMetered cfg.wasm fuel config).1.store.wasm.host.gas
    gas.prepaid = st.host.gas.prepaid ∧ gas.maxBurnt = st.host.gas.maxBurnt := by
  have hfinal := runMetered_hostInvariant
    (GasLimits st.host.gas.prepaid st.host.gas.maxBurnt)
    (by
      intro current cost h
      have hp := chargeWasm_gas_limits current cost
      exact ⟨hp.1.trans h.1, hp.2.trans h.2⟩) cfg.wasm fuel config
    (initResolvedConfig_gasLimits hresolve hinit)
  exact hfinal.2

/-- Actual resolved execution respects the supplied prepaid/per-call budgets
on every exit. The only gas premise is that the supplied initial counter fits
its limits; imported-host preservation is derived from the concrete registry. -/
theorem runResolved_gas_bounds {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hbound : st.host.gas.Bounded) :
    let gas := (runMetered cfg.wasm fuel config).1.store.wasm.host.gas
    gas.burnt ≤ gas.used ∧ gas.used ≤ st.host.gas.prepaid ∧ gas.burnt ≤ st.host.gas.maxBurnt := by
  have hb := runMetered_fixed_budget cfg.wasm fuel config st.host.gas.prepaid st.host.gas.maxBurnt
    (initResolvedConfig_gasLimits hresolve hinit) (by rw [initConfig_gas hinit]; exact hbound)
  exact ⟨Nat.le_add_right _ _, hb.2, hb.1⟩

end Wasm.Near
