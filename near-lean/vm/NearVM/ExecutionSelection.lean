import NearVM.ExecutionPromises
import NearVM.MeteredSelection
import NearVM.ReturnGraph

namespace Wasm.Near

abbrev ConfigSelectionValid := MachineHostInvariant ReturnSelectionValid

theorem runMetered_preserves_selection (cfg : WasmConfig) (fuel : Nat)
    (m : Machine) (h : ConfigSelectionValid m) :
    ConfigSelectionValid (runMetered cfg fuel m).1 :=
  runMetered_hostInvariant ReturnSelectionValid (fun _ _ hwf => hwf) cfg fuel m h

theorem resolvedStart_selection {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hselection : ReturnSelectionValid host) : ConfigSelectionValid (.next c) :=
  resolvedStart_hostInvariant (resolveMetered_selection cfg code env hresolve) halloc hinst hstart
    hselection

theorem toNearState_selection (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) : ReturnSelectionValid (ctx.toNearState cfg storage) := by
  intro index hreturn
  cases hreturn

/-- Resolved execution yields both a valid graph and a resolvable exact return
selection, without using either post-execution check as a premise. -/
theorem runResolved_return_selection {cfg : RuntimeConfig} {code : Module}
    {env : HostEnv NearState} {host : NearState} {store store' : Store NearState}
    {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst} {addr : Nat}
    {c : Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    (hwf : PromisesWellFormedFrom 0 host.promises) (hselection : ReturnSelectionValid host) :
    let ns := (runMetered cfg.wasm fuel (.next c)).1.host
    ∃ graph, convertPromises ns.promises = some graph ∧ graph.Valid ∧
      (∃ data, graph.returnData? ns = some data) ∧
      (∀ index, ns.returnedPromise = some index →
        ∃ receipt, graph.returnedReceipt? index = some receipt ∧ receipt < graph.receipts.length) := by
  have hfinal := runMetered_preserves_selection cfg.wasm fuel (.next c)
    (resolvedStart_selection hresolve halloc hinst hstart hselection)
  obtain ⟨graph, hconvert, hvalid⟩ :=
    runResolved_promises_convertible fuel hresolve halloc hinst hstart hwf
  exact ⟨graph, hconvert, hvalid, PromiseGraph.returnData?_total hconvert hfinal.host,
    fun index hreturn => convertPromises_return_selection hconvert hfinal.host hreturn⟩

end Wasm.Near
