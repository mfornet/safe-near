import NearVM.HostNeutralDeposits
import NearVM.HostGasLimits

namespace Wasm.Near

/-- Every successful published host call preserves liquid funds plus pending
promise deposits, accounting explicitly for permitted subsidies. Rejected calls
carry no success guarantee. -/
theorem meteredHostFns_funding (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesFunding entry.2 := by
  revert entry h
  simp only [meteredHostFns, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
  refine ⟨?_, HostCreatesNoDeposits.funding gasFn_noDeposits⟩
  simp only [nearHostFns, List.forall_mem_cons]
  and_intros
  · apply metered_funding; exact inputFn_noDeposits
  · apply metered_funding; exact readRegisterFn_noDeposits
  · apply metered_funding; exact registerLenFn_noDeposits
  · apply metered_funding; exact writeRegisterFn_noDeposits
  · apply metered_funding; exact valueReturnFn_noDeposits
  · apply metered_funding; exact storageWriteFn_noDeposits
  · apply metered_funding; exact storageReadFn_noDeposits
  · apply metered_funding; exact storageRemoveFn_noDeposits
  · apply metered_funding; exact storageHasKeyFn_noDeposits
  · apply metered_funding; exact panicMetered_noDeposits
  · apply metered_funding; exact panicUtf8Metered_noDeposits
  · apply metered_funding; exact currentAccountIdFn_noDeposits
  · apply metered_funding; exact predecessorAccountIdFn_noDeposits
  · apply metered_funding; exact signerAccountIdFn_noDeposits
  · apply metered_funding; exact attachedDepositFn_noDeposits
  · apply metered_funding; exact logUtf8Fn_noDeposits
  · apply metered_funding; exact sha256Fn_noDeposits
  · apply metered_funding; exact keccak256Fn_noDeposits
  · apply metered_funding; exact signerAccountPkFn_noDeposits
  · apply metered_funding; exact blockIndexFn_noDeposits
  · apply metered_funding; exact blockIndexFn_noDeposits
  · apply metered_funding; exact blockTimestampFn_noDeposits
  · apply metered_funding; exact epochHeightFn_noDeposits
  · apply metered_funding; exact storageUsageFn_noDeposits
  · apply metered_funding; exact accountBalanceFn_noDeposits
  · apply metered_funding; exact accountLockedBalanceFn_noDeposits
  · apply metered_funding; exact prepaidGasFn_noDeposits
  · apply metered_funding; exact usedGasFn_noDeposits
  · apply metered_funding; intro st args; trivial -- validator_stake
  · apply metered_funding; intro st args; trivial -- validator_total_stake
  · apply metered_funding; exact logUtf16Fn_noDeposits
  · apply metered_funding; exact abortMetered_noDeposits
  · intro st args; trivial -- storage_iter_prefix
  · intro st args; trivial -- storage_iter_range
  · intro st args; trivial -- storage_iter_next
  · apply metered_funding; exact keccak512Fn_noDeposits
  · apply metered_funding; exact ripemd160Fn_noDeposits
  · apply metered_funding; intro st args; trivial -- ecrecover
  · apply metered_funding; intro st args; trivial -- ed25519_verify
  · apply metered_funding; exact randomSeedFn_noDeposits
  · apply metered_funding; intro st args; trivial -- alt_bn128_g1_multiexp
  · apply metered_funding; intro st args; trivial -- alt_bn128_g1_sum
  · apply metered_funding; intro st args; trivial -- alt_bn128_pairing_check
  · apply metered_funding; intro st args; trivial -- bls12381_g1_multiexp
  · apply metered_funding; intro st args; trivial -- bls12381_g2_multiexp
  · apply metered_funding; intro st args; trivial -- bls12381_map_fp_to_g1
  · apply metered_funding; intro st args; trivial -- bls12381_map_fp2_to_g2
  · apply metered_funding; intro st args; trivial -- bls12381_p1_decompress
  · apply metered_funding; intro st args; trivial -- bls12381_p2_decompress
  · apply metered_funding; intro st args; trivial -- bls12381_p1_sum
  · apply metered_funding; intro st args; trivial -- bls12381_p2_sum
  · apply metered_funding; intro st args; trivial -- bls12381_pairing_check
  · apply metered_funding; exact promiseCreateFn_deposits
  · apply metered_funding; exact promiseThenFn_deposits
  · apply metered_funding; exact promiseAndFn_noDeposits
  · apply metered_funding; exact promiseBatchCreateFn_noDeposits
  · apply metered_funding; exact promiseBatchThenFn_noDeposits
  · apply metered_funding; exact promiseBatchActionCreateAccountFn_noDeposits
  · apply metered_funding; exact promiseBatchActionDeployContractFn_noDeposits
  · apply metered_funding; exact promiseBatchActionFunctionCallFn_deposits
  · apply metered_funding; exact promiseBatchActionFunctionCallWeightFn_deposits
  · apply metered_funding; exact promiseBatchActionTransferFn_deposits
  · apply metered_funding; exact promiseBatchActionStakeFn_noDeposits
  · apply metered_funding; exact promiseBatchActionAddKeyWithFullAccessFn_noDeposits
  · apply metered_funding; exact promiseBatchActionAddKeyWithFunctionCallFn_noDeposits
  · apply metered_funding; exact promiseBatchActionDeleteKeyFn_noDeposits
  · apply metered_funding; exact promiseBatchActionDeleteAccountFn_noDeposits
  · apply metered_funding; intro st args; trivial -- promise_batch_action_deploy_global_contract
  · apply metered_funding; intro st args; trivial -- promise_batch_action_deploy_global_contract_by_account_id
  · apply metered_funding; exact promiseBatchActionUseGlobalContractFn_noDeposits
  · apply metered_funding; exact promiseBatchActionUseGlobalContractByAccountIdFn_noDeposits
  · apply metered_funding; intro st args; trivial -- promise_yield_create
  · apply metered_funding; intro st args; trivial -- promise_yield_resume
  · apply metered_funding; exact promiseResultsCountFn_noDeposits
  · apply metered_funding; exact promiseResultFn_noDeposits
  · apply metered_funding; exact promiseReturnFn_noDeposits
  · simp

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
