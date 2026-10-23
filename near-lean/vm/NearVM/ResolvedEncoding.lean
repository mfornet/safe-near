import NearVM.EncodingRegistry
import NearVM.ExecutionPromises

namespace Wasm.Near

/-- Structural import resolution introduces only hosts covered by the concrete
registry preservation proof. -/
theorem resolveMeteredImports_encodingInvariant (cfg : RuntimeConfig) (imports : List ImportDecl) (env : HostEnv NearState)
    (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, NearHostFn.PreservesLive EncodingInvariant fn := by
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
    ∀ fn ∈ env.funcs, NearHostFn.PreservesLive EncodingInvariant fn :=
  resolveMeteredImports_encodingInvariant cfg code.importDecls env h

/-- The concrete registry discharges the live-host premise at the first
configuration. No host preservation or receipt-decoding premise is supplied by
a contract proof. -/
theorem resolvedStart_encodingInvariant {cfg : RuntimeConfig} {code : Module}
    {env : HostEnv NearState} {host : NearState} {store store' : Store NearState}
    {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst} {addr : Nat}
    {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hbefore : EncodingInvariant host) : ConfigLiveInvariant EncodingInvariant c :=
  resolvedStart_liveInvariant (resolveMetered_encodingInvariant cfg code env hresolve) halloc hinst
    hstart hbefore

/-- A strict runtime call starts with an empty, encoding-safe promise list. -/
theorem VMContext.toNearState_encodingInvariant (ctx : VMContext) (cfg : RuntimeConfig)
    (storage : List (Bytes × Bytes)) (hpolicy : ctx.validateActionMethodUtf8 = true) :
    EncodingInvariant (ctx.toNearState cfg storage) := by
  exact ⟨hpolicy, by intro promise hm; cases hm⟩

end Wasm.Near
