import NearVM.ReservationRegistry
import NearVM.ExecutionPromises

namespace Wasm.Near

/-- Structural import resolution introduces only hosts covered by the concrete
registry preservation proof. -/
theorem resolveMeteredImports_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : RuntimeConfig) (imports : List ImportDecl) (env : HostEnv NearState)
    (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostFn.PreservesLive (ReservationInvariant fees ethEnabled) fn := by
  induction imports generalizing env with
  | nil =>
    simp only [resolveMeteredImports, Except.ok.injEq] at h
    subst env
    simp
  | cons decl rest ih =>
    cases hf : (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => simp [resolveMeteredImports, hf] at h
    | some entry =>
      obtain ⟨found, fn⟩ := entry
      cases hr : resolveMeteredImports cfg rest with
      | error message => simp [resolveMeteredImports, hf, hr] at h
      | ok tail =>
        simp only [resolveMeteredImports, hf, hr, Except.ok.injEq] at h
        subst env
        intro candidate hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact meteredHostFns_reservationInvariant fees ethEnabled cfg (found, candidate)
            (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : RuntimeConfig) (code : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg code = .ok env) :
    ∀ fn ∈ env.funcs, HostFn.PreservesLive (ReservationInvariant fees ethEnabled) fn :=
  resolveMeteredImports_reservationInvariant fees ethEnabled cfg code.imports env h

/-- The concrete registry discharges the live-host premise at initialization.
No host gas-accounting equation is supplied by a contract proof. -/
theorem initResolvedConfig_reservationInvariant {fees : ActionFees} {ethEnabled : Bool}
    {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hbefore : ReservationInvariant fees ethEnabled st.host) :
    ConfigLiveInvariant (ReservationInvariant fees ethEnabled) config := by
  apply initConfig_liveInvariant hinit _ hbefore
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact resolveMetered_reservationInvariant fees ethEnabled cfg resolvedCode env hresolve fn hmember
  · have hempty := resolveMeteredImports_noForeign cfg resolvedCode.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

/-- Fresh calls begin with no raw promise obligations or reserved gas. -/
theorem VMContext.toNearState_reservationInvariant (ctx : VMContext) (cfg : RuntimeConfig)
    (storage : List (Bytes × Bytes)) :
    ReservationInvariant cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (ctx.toNearState cfg storage) := by
  exact ⟨rfl, rfl, rfl⟩

end Wasm.Near
