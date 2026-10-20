import NearVM.EncodingRegistry
import NearVM.ExecutionPromises

namespace Wasm.Near

/-- Structural import resolution introduces only hosts covered by the concrete
registry preservation proof. -/
theorem resolveMeteredImports_encodingInvariant (cfg : RuntimeConfig) (imports : List ImportDecl) (env : HostEnv NearState)
    (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostFn.PreservesLive EncodingInvariant fn := by
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
        · exact meteredHostFns_encodingInvariant cfg (found, candidate)
            (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_encodingInvariant (cfg : RuntimeConfig) (code : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg code = .ok env) :
    ∀ fn ∈ env.funcs, HostFn.PreservesLive EncodingInvariant fn :=
  resolveMeteredImports_encodingInvariant cfg code.imports env h

/-- The concrete registry discharges the live-host premise at initialization.
No host preservation or receipt-decoding premise is supplied by a contract proof. -/
theorem initResolvedConfig_encodingInvariant {cfg : RuntimeConfig} {resolvedCode code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg resolvedCode = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hbefore : EncodingInvariant st.host) :
    ConfigLiveInvariant EncodingInvariant config := by
  apply initConfig_liveInvariant hinit _ hbefore
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact resolveMetered_encodingInvariant cfg resolvedCode env hresolve fn hmember
  · have hempty := resolveMeteredImports_noForeign cfg resolvedCode.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

/-- A strict runtime call starts with an empty, encoding-safe promise list. -/
theorem VMContext.toNearState_encodingInvariant (ctx : VMContext) (cfg : RuntimeConfig)
    (storage : List (Bytes × Bytes)) (hpolicy : ctx.validateActionMethodUtf8 = true) :
    EncodingInvariant (ctx.toNearState cfg storage) := by
  exact ⟨hpolicy, by intro promise hm; cases hm⟩

end Wasm.Near
