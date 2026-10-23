import NearVM.HostDispatch
import NearVM.MeteredInvariant
import NearVM.InterpreterInvariant

/-!
Dependency preservation through the runtime and its metered runner. This
invariant concerns promise references; it does not assert action validity,
numeric bounds, or token conservation.
-/

namespace Wasm.Near

/-- The dependency invariant on a machine state: every host function in the
store preserves it and it holds now. -/
def ConfigPromisesValid (m : Machine) : Prop :=
  MachineHostInvariant (fun ns : NearState => PromisesWellFormedFrom 0 ns.promises) m

theorem chargeWasm_preserves_promises (m : Machine) (cost : Nat)
    (h : ConfigPromisesValid m) : ConfigPromisesValid (chargeWasm m cost).1 :=
  chargeWasm_hostInvariant (fun _ _ h => h) m cost h

/-- Dependency validity survives every exit, including fuel exhaustion, gas
exhaustion and diagnostic errors, without relying on output validation. -/
theorem runMetered_preserves_promises (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : ConfigPromisesValid m) : ConfigPromisesValid (runMetered cfg fuel m).1 :=
  runMetered_hostInvariant (fun ns => PromisesWellFormedFrom 0 ns.promises)
    (fun _ _ h => h) cfg fuel m h

/-- The first configuration of a resolved call carries the invariant. -/
theorem resolvedStart_promises {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hwf : PromisesWellFormedFrom 0 host.promises) : ConfigPromisesValid (.next c) :=
  resolvedStart_hostInvariant (resolveMetered_preserves cfg code env hresolve) halloc hinst hstart hwf

/-- Actual resolved execution produces a convertible valid dependency graph
without a post-execution graph validator as a premise. -/
theorem runResolved_promises_convertible {cfg : RuntimeConfig} {code : Module}
    {env : HostEnv NearState} {host : NearState} {store store' : Store NearState}
    {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst} {addr : Nat}
    {c : Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hwf : PromisesWellFormedFrom 0 host.promises) :
    ∃ graph, convertPromises (runMetered cfg.wasm fuel (.next c)).1.host.promises = some graph ∧
      graph.Valid := by
  have hfinal := runMetered_preserves_promises cfg.wasm fuel (.next c)
    (resolvedStart_promises hresolve halloc hinst hstart hwf)
  obtain ⟨graph, hgraph⟩ := convertPromises_total _ hfinal.host
  exact ⟨graph, hgraph, convertPromises_valid hgraph⟩

end Wasm.Near
