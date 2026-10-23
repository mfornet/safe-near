import NearVM.HostGasLimits

namespace Wasm.Near

/-- The first configuration of a resolved call keeps the supplied limits. -/
theorem resolvedStart_gasLimits {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c) :
    ConfigHostInvariant (GasLimits host.gas.prepaid host.gas.maxBurnt) c :=
  resolvedStart_hostInvariant
    (fun fn hm => resolveMetered_gasLimits cfg code env hresolve fn hm _ _) halloc hinst hstart
    ⟨rfl, rfl⟩

/-- Starting a call changes no gas: the host state is the instantiated store's. -/
theorem resolvedStart_gas {env : HostEnv NearState} {host : NearState}
    {store store' : Store NearState} {imports : List ExternVal} {vm : ValidModule}
    {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c) :
    c.store.host = host := by
  rw [Exec.startWasm_store hstart, (Link.instantiateModule_same store vm imports hinst).1]
  have hh := HostEnv.allocate_host (Store.empty host) env
  rw [halloc] at hh
  exact hh

/-- Executable resolved calls preserve the original call's gas limits without
an assumed host-invariant oracle. -/
theorem runResolved_gas_limits {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c) :
    let gas := (runMetered cfg.wasm fuel (.next c)).1.host.gas
    gas.prepaid = host.gas.prepaid ∧ gas.maxBurnt = host.gas.maxBurnt := by
  have hfinal := runMetered_hostInvariant (GasLimits host.gas.prepaid host.gas.maxBurnt)
    (by
      intro current cost h
      have hp := chargeHost_gas_limits current cost
      exact ⟨hp.1.trans h.1, hp.2.trans h.2⟩) cfg.wasm fuel (.next c)
    (resolvedStart_gasLimits hresolve halloc hinst hstart)
  exact hfinal.host

/-- Actual resolved execution respects the supplied prepaid/per-call budgets
on every exit. The only gas premise is that the supplied initial counter fits
its limits; imported-host preservation is derived from the concrete registry. -/
theorem runResolved_gas_bounds {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hbound : host.gas.Bounded) :
    let gas := (runMetered cfg.wasm fuel (.next c)).1.host.gas
    gas.burnt ≤ gas.used ∧ gas.used ≤ host.gas.prepaid ∧ gas.burnt ≤ host.gas.maxBurnt := by
  have hb := runMetered_fixed_budget cfg.wasm fuel (.next c) host.gas.prepaid host.gas.maxBurnt
    (resolvedStart_gasLimits hresolve halloc hinst hstart)
    (by
      show c.store.host.gas.Bounded
      rw [resolvedStart_gas halloc hinst hstart]; exact hbound)
  exact ⟨Nat.le_add_right _ _, hb.2, hb.1⟩

end Wasm.Near
