import NearVM.ExecutionPromises
import NearVM.MeteredSelection
import NearVM.ReturnGraph

namespace Wasm.Near

abbrev ConfigSelectionValid := ConfigHostInvariant ReturnSelectionValid

theorem runMetered_preserves_selection (cfg : WasmConfig) (fuel : Nat)
    (config : SmallStep.Config NearState) (h : ConfigSelectionValid config) :
    ConfigSelectionValid (runMetered cfg fuel config).1 :=
  runMetered_hostInvariant ReturnSelectionValid (by intro config cost hwf; exact hwf) cfg fuel config h

theorem initResolvedConfig_selection {cfg : RuntimeConfig} {code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hselection : ReturnSelectionValid st.host) : ConfigSelectionValid config := by
  apply initConfig_hostInvariant hinit _ hselection
  intro fn hmember
  rcases hmember with hmember | hmember
  · exact resolveMetered_selection cfg code env hresolve fn hmember
  · have hempty := resolveMeteredImports_noForeign cfg code.imports env hresolve
    simp only [hempty, List.not_mem_nil] at hmember

theorem toNearState_selection (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) : ReturnSelectionValid (ctx.toNearState cfg storage) := by
  intro index hreturn
  cases hreturn

/-- Resolved execution yields both a valid graph and a resolvable exact return
selection, without using either post-execution check as a premise. -/
theorem runResolved_return_selection {cfg : RuntimeConfig} {code : Module} {entry : Nat}
    {env : HostEnv NearState} {st : Store NearState} {args : List Value}
    {config : SmallStep.Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (hinit : SmallStep.initConfig { module := code, host := env } entry st args = .ok config)
    (hwf : PromisesWellFormedFrom 0 st.host.promises) (hselection : ReturnSelectionValid st.host) :
    let ns := (runMetered cfg.wasm fuel config).1.store.wasm.host
    ∃ graph, convertPromises ns.promises = some graph ∧ graph.Valid ∧
      (∃ data, graph.returnData? ns = some data) ∧
      (∀ index, ns.returnedPromise = some index →
        ∃ receipt, graph.returnedReceipt? index = some receipt ∧ receipt < graph.receipts.length) := by
  have hfinal := runMetered_preserves_selection cfg.wasm fuel config
    (initResolvedConfig_selection hresolve hinit hselection)
  obtain ⟨graph, hconvert, hvalid⟩ := runResolved_promises_convertible fuel hresolve hinit hwf
  exact ⟨graph, hconvert, hvalid, PromiseGraph.returnData?_total hconvert hfinal.2,
    fun index hreturn => convertPromises_return_selection hconvert hfinal.2 hreturn⟩

end Wasm.Near
