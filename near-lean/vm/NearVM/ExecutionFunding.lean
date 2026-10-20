import NearVM.HostNoThrow
import NearVM.MeteredLiveInvariant

namespace Wasm.Near

/-- Financial value, with explicit subsidy creation on the opposite side. -/
def Funding (funds subsidy : Nat) (ns : NearState) : Prop :=
  ns.liquidFunds + subsidy = funds + ns.subsidizedAmount

theorem HostPreservesFunding.live {fn : HostFn NearState}
    (hfund : HostPreservesFunding fn) (hthrow : HostNeverThrows fn)
    (funds subsidy : Nat) : HostFn.PreservesLive (Funding funds subsidy) fn := by
  intro st args hwf
  have hf := hfund st args
  have ht := hthrow st args
  cases hr : fn.invoke st args <;> rw [hr] at hf ht <;>
    dsimp only [HostResult.LiveSatisfies, HostResultFunded, HostResult.NoThrow] at hf ht ⊢
  · unfold Funding at hwf ⊢
    omega

theorem chargeWasm_funding (config : SmallStep.Config NearState) (cost : Nat)
    {funds subsidy : Nat} (h : Funding funds subsidy config.store.wasm.host) :
    Funding funds subsidy (chargeWasm config cost).1.store.wasm.host := h

/-- Concrete host resolution discharges all host funding and exception premises. -/
theorem initResolvedConfig_funding {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config) :
    ConfigLiveInvariant (Funding st.host.liquidFunds st.host.subsidizedAmount) config := by
  apply initConfig_liveInvariant (P := Funding st.host.liquidFunds st.host.subsidizedAmount) hinit _ rfl
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact HostPreservesFunding.live (resolveMetered_funding cfg resolvedCode env hresolve fn hmember)
      (resolveMetered_noThrow cfg resolvedCode env hresolve fn hmember) _ _
  · have hempty := resolveMeteredImports_noForeign cfg resolvedCode.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

theorem runInitialized_liveFunding (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    {funds subsidy : Nat} (h : ConfigLiveInvariant (Funding funds subsidy) config) :
    ConfigLiveInvariant (Funding funds subsidy) (runInitialized cfg fuel config).1 := by
  let cost := match config.expr with
    | .running thread => activationGas cfg.regularOpCost thread.locals
    | _ => 0
  unfold runInitialized
  dsimp only
  cases hc : chargeWasm config cost with
  | mk paid error =>
    have hp := chargeWasm_liveInvariant (P := Funding funds subsidy)
      (fun current n h => chargeWasm_funding current n h) config cost h
    rw [hc] at hp
    cases error with
    | some error => exact hp
    | none =>
      exact runMetered_liveInvariant _
        (fun current n h => chargeWasm_funding current n h) cfg fuel paid hp

/-- Successful resolved interpreter execution conserves liquid funds plus raw
promise backing, even across catchable Wasm exceptions and indexed memories. -/
theorem runResolved_funding {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    {values : List Value} (hdone : (runMetered cfg.wasm fuel config).1.expr = .done values) :
    Funding st.host.liquidFunds st.host.subsidizedAmount
      (runMetered cfg.wasm fuel config).1.store.wasm.host := by
  have h := runMetered_liveInvariant (Funding st.host.liquidFunds st.host.subsidizedAmount)
    (fun current cost hp => chargeWasm_funding current cost hp) cfg.wasm fuel config
    (initResolvedConfig_funding hresolve hinit)
  simpa only [SmallStep.Config.LiveHost, hdone] using h.2

end Wasm.Near
