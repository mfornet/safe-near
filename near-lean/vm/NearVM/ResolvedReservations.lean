import NearVM.ReservationRegistry
import NearVM.ExecutionPromises

namespace Wasm.Near

/-- Structural import resolution introduces only hosts covered by the concrete
registry preservation proof. -/
theorem resolveMeteredImports_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : RuntimeConfig) (imports : List ImportDecl) (env : HostEnv NearState)
    (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) fn := by
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
    ∀ fn ∈ env.funcs, NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) fn :=
  resolveMeteredImports_reservationInvariant fees ethEnabled cfg code.importDecls env h

/-- The concrete registry discharges the live-host premise at the first
configuration. No host gas-accounting equation is supplied by a contract proof. -/
theorem resolvedStart_reservationInvariant {fees : ActionFees} {ethEnabled : Bool}
    {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState} {host : NearState}
    {store store' : Store NearState} {imports : List ExternVal} {vm : ValidModule}
    {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hbefore : ReservationInvariant fees ethEnabled host) :
    ConfigLiveInvariant (ReservationInvariant fees ethEnabled) c :=
  resolvedStart_liveInvariant
    (resolveMetered_reservationInvariant fees ethEnabled cfg code env hresolve) halloc hinst hstart
    hbefore

/-- Fresh calls begin with no raw promise obligations or reserved gas. -/
theorem VMContext.toNearState_reservationInvariant (ctx : VMContext) (cfg : RuntimeConfig)
    (storage : List (Bytes × Bytes)) :
    ReservationInvariant cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (ctx.toNearState cfg storage) := by
  exact ⟨rfl, rfl, rfl⟩

end Wasm.Near
