import NearVM.HostNeutralDeposits
import NearVM.HostGasLimits

namespace Wasm.Near

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
/-- Every successful published host call preserves liquid funds plus pending
promise deposits, accounting explicitly for permitted subsidies. Rejected calls
carry no success guarantee. -/
theorem meteredHostFns_funding (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesFunding entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro st args; trivial)
      | apply metered_funding
    all_goals first
      | exact inputFn_noDeposits
      | exact readRegisterFn_noDeposits
      | exact registerLenFn_noDeposits
      | exact writeRegisterFn_noDeposits
      | exact storageWriteFn_noDeposits
      | exact storageReadFn_noDeposits
      | exact storageRemoveFn_noDeposits
      | exact storageHasKeyFn_noDeposits
      | exact currentAccountIdFn_noDeposits
      | exact predecessorAccountIdFn_noDeposits
      | exact signerAccountIdFn_noDeposits
      | exact signerAccountPkFn_noDeposits
      | exact attachedDepositFn_noDeposits
      | exact blockIndexFn_noDeposits
      | exact blockTimestampFn_noDeposits
      | exact epochHeightFn_noDeposits
      | exact storageUsageFn_noDeposits
      | exact accountBalanceFn_noDeposits
      | exact accountLockedBalanceFn_noDeposits
      | exact prepaidGasFn_noDeposits
      | exact usedGasFn_noDeposits
      | exact randomSeedFn_noDeposits
      | exact logUtf8Fn_noDeposits
      | exact logUtf16Fn_noDeposits
      | exact panicMetered_noDeposits
      | exact panicUtf8Metered_noDeposits
      | exact abortMetered_noDeposits
      | exact HostCreatesNoDeposits.funding (gasFn_noDeposits _)
      | exact promiseCreateFn_deposits
      | exact promiseThenFn_deposits
      | exact promiseAndFn_noDeposits
      | exact promiseBatchCreateFn_noDeposits
      | exact promiseBatchThenFn_noDeposits
      | exact promiseBatchActionCreateAccountFn_noDeposits
      | exact promiseBatchActionDeployContractFn_noDeposits
      | exact promiseBatchActionFunctionCallFn_deposits
      | exact promiseBatchActionFunctionCallWeightFn_deposits
      | exact promiseBatchActionTransferFn_deposits
      | exact promiseBatchActionStakeFn_noDeposits
      | exact promiseBatchActionAddKeyWithFullAccessFn_noDeposits
      | exact promiseBatchActionAddKeyWithFunctionCallFn_noDeposits
      | exact promiseBatchActionDeleteKeyFn_noDeposits
      | exact promiseBatchActionDeleteAccountFn_noDeposits
      | exact promiseBatchActionUseGlobalContractFn_noDeposits
      | exact promiseBatchActionUseGlobalContractByAccountIdFn_noDeposits
      | exact promiseBatchActionDeployGlobalContractFn_noDeposits
      | exact promiseBatchActionDeployGlobalContractByAccountIdFn_noDeposits
      | exact promiseBatchActionTransferToGasKeyFn_deposits
      | exact promiseBatchActionAddGasKeyWithFullAccessFn_noDeposits
      | exact promiseBatchActionAddGasKeyWithFunctionCallFn_noDeposits
      | exact promiseYieldCreateFn_noDeposits
      | exact promiseYieldResumeFn_noDeposits
      | exact chainIdFn_noDeposits
      | exact valueReturnFn_noDeposits
      | exact promiseReturnFn_noDeposits
      | exact promiseResultsCountFn_noDeposits
      | exact promiseResultFn_noDeposits
  · subst entry
    exact HostCreatesNoDeposits.funding (gasFn_noDeposits _)

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_funding (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesFunding fn := by
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
        · exact meteredHostFns_funding cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_funding (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesFunding fn :=
  resolveMeteredImports_funding cfg m.importDecls env h

end Wasm.Near
