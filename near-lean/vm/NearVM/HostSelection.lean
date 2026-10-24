import NearVM.ReturnSelection

namespace Wasm.Near

/-- Unfold a register/context host and close each branch from `hwf`. -/
local macro "host_selection_tac" hwf:ident : tactic => `(tactic| (
    dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
    repeat (first
      | exact $hwf
      | exact writeRegisterResult_selection _ _ _ _ _ $hwf
      | split)))

theorem inputFn_selection : HostPreservesSelection inputFn := by
  intro st args hwf
  unfold inputFn
  host_selection_tac hwf

theorem readRegisterFn_selection : HostPreservesSelection readRegisterFn := by
  intro st args hwf
  unfold readRegisterFn
  host_selection_tac hwf

theorem registerLenFn_selection : HostPreservesSelection registerLenFn := by
  intro st args hwf
  unfold registerLenFn
  host_selection_tac hwf

theorem writeRegisterFn_selection : HostPreservesSelection writeRegisterFn := by
  intro st args hwf
  unfold writeRegisterFn
  host_selection_tac hwf

theorem storageWriteFn_selection : HostPreservesSelection storageWriteFn := by
  intro st args hwf
  unfold storageWriteFn
  host_selection_tac hwf
  all_goals
    simp_all only [HostResult.Satisfies, NearState.setStorage,
      NearState.invalidateIterators]
  all_goals first
    | exact hwf
    | (rename_i hreg; exact checkedSetRegister_selection hreg hwf)

theorem storageReadFn_selection : HostPreservesSelection storageReadFn := by
  intro st args hwf
  unfold storageReadFn
  host_selection_tac hwf

theorem storageRemoveFn_selection : HostPreservesSelection storageRemoveFn := by
  intro st args hwf
  unfold storageRemoveFn
  host_selection_tac hwf
  all_goals
    simp_all only [HostResult.Satisfies, NearState.removeStorage,
      NearState.invalidateIterators]
  all_goals first
    | exact hwf
    | (rename_i hreg; exact checkedSetRegister_selection hreg hwf)

theorem storageHasKeyFn_selection : HostPreservesSelection storageHasKeyFn := by
  intro st args hwf
  unfold storageHasKeyFn
  host_selection_tac hwf

theorem currentAccountIdFn_selection : HostPreservesSelection currentAccountIdFn := by
  intro st args hwf
  unfold currentAccountIdFn
  host_selection_tac hwf

theorem predecessorAccountIdFn_selection : HostPreservesSelection predecessorAccountIdFn := by
  intro st args hwf
  unfold predecessorAccountIdFn
  host_selection_tac hwf

theorem signerAccountIdFn_selection : HostPreservesSelection signerAccountIdFn := by
  intro st args hwf
  unfold signerAccountIdFn
  host_selection_tac hwf

theorem signerAccountPkFn_selection : HostPreservesSelection signerAccountPkFn := by
  intro st args hwf
  unfold signerAccountPkFn
  host_selection_tac hwf

theorem attachedDepositFn_selection : HostPreservesSelection attachedDepositFn := by
  intro st args hwf
  unfold attachedDepositFn
  host_selection_tac hwf

theorem blockIndexFn_selection : HostPreservesSelection blockIndexFn := by
  intro st args hwf
  unfold blockIndexFn
  host_selection_tac hwf

theorem blockTimestampFn_selection : HostPreservesSelection blockTimestampFn := by
  intro st args hwf
  unfold blockTimestampFn
  host_selection_tac hwf

theorem epochHeightFn_selection : HostPreservesSelection epochHeightFn := by
  intro st args hwf
  unfold epochHeightFn
  host_selection_tac hwf

theorem storageUsageFn_selection : HostPreservesSelection storageUsageFn := by
  intro st args hwf
  unfold storageUsageFn
  host_selection_tac hwf

theorem accountBalanceFn_selection : HostPreservesSelection accountBalanceFn := by
  intro st args hwf
  unfold accountBalanceFn
  host_selection_tac hwf

theorem accountLockedBalanceFn_selection : HostPreservesSelection accountLockedBalanceFn := by
  intro st args hwf
  unfold accountLockedBalanceFn
  host_selection_tac hwf

theorem prepaidGasFn_selection : HostPreservesSelection prepaidGasFn := by
  intro st args hwf
  unfold prepaidGasFn
  host_selection_tac hwf

theorem usedGasFn_selection : HostPreservesSelection usedGasFn := by
  intro st args hwf
  unfold usedGasFn
  host_selection_tac hwf

theorem randomSeedFn_selection : HostPreservesSelection randomSeedFn := by
  intro st args hwf
  unfold randomSeedFn
  host_selection_tac hwf

theorem logUtf8Fn_selection : HostPreservesSelection logUtf8Fn := by
  intro st args hwf
  unfold logUtf8Fn
  host_selection_tac hwf

theorem logUtf16Fn_selection : HostPreservesSelection logUtf16Fn := by
  intro st args hwf
  unfold logUtf16Fn
  host_selection_tac hwf

theorem panicMetered_selection : HostPreservesSelection panicMetered := by
  intro st args hwf
  unfold panicMetered
  host_selection_tac hwf

theorem panicUtf8Metered_selection : HostPreservesSelection panicUtf8Metered := by
  intro st args hwf
  unfold panicUtf8Metered
  host_selection_tac hwf

theorem abortMetered_selection : HostPreservesSelection abortMetered := by
  intro st args hwf
  unfold abortMetered
  host_selection_tac hwf

theorem gasFn_selection : HostPreservesSelection gasFn := by
  intro st args hwf
  unfold gasFn
  host_selection_tac hwf

/-- Close each branch of a promise host from `hwf`. -/
local macro "promise_selection_tac" hwf:ident : tactic => `(tactic| (
    dsimp only
    repeat (first
      | exact $hwf
      | exact appendPromise_selection _ _ $hwf
      | exact appendPromiseActionResult_selection _ _ _ _ $hwf
      | exact createBatchPromiseResult_selection _ _ _ $hwf
      | exact createCallbackPromiseResult_selection _ _ _ _ $hwf
      | apply checkAccountId_selection _ _ _ _ $hwf
      | apply checkPublicKey_selection _ _ _ _ $hwf
      | split)))

theorem promiseCreateFn_selection : HostPreservesSelection promiseCreateFn := by
  unfold promiseCreateFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseThenFn_selection : HostPreservesSelection promiseThenFn := by
  unfold promiseThenFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseAndFn_selection : HostPreservesSelection promiseAndFn := by
  unfold promiseAndFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchCreateFn_selection : HostPreservesSelection promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchThenFn_selection : HostPreservesSelection promiseBatchThenFn := by
  unfold promiseBatchThenFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionCreateAccountFn_selection : HostPreservesSelection promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionDeployContractFn_selection : HostPreservesSelection promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionFunctionCallFn_selection : HostPreservesSelection promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionFunctionCallWeightFn_selection : HostPreservesSelection promiseBatchActionFunctionCallWeightFn := by
  unfold promiseBatchActionFunctionCallWeightFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionTransferFn_selection : HostPreservesSelection promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionStakeFn_selection : HostPreservesSelection promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionAddKeyWithFullAccessFn_selection : HostPreservesSelection promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionAddKeyWithFunctionCallFn_selection : HostPreservesSelection promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionDeleteKeyFn_selection : HostPreservesSelection promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionDeleteAccountFn_selection : HostPreservesSelection promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionUseGlobalContractFn_selection : HostPreservesSelection promiseBatchActionUseGlobalContractFn := by
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem promiseBatchActionUseGlobalContractByAccountIdFn_selection : HostPreservesSelection promiseBatchActionUseGlobalContractByAccountIdFn := by
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  promise_selection_tac hwf

theorem valueReturnFn_selection : HostPreservesSelection valueReturnFn := by
  intro st args hwf
  unfold valueReturnFn
  dsimp only
  repeat (first
    | exact hwf
    | apply checkDataLimit_selection _ _ _ _ _ _ hwf
    | exact selectReturnValue_valid _ _
    | split)

theorem promiseReturnFn_selection : HostPreservesSelection promiseReturnFn := by
  unfold promiseReturnFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first | exact hwf | exact selectReturnPromise_valid_of_not_joint (by assumption) (by assumption) | split)

theorem promiseResultsCountFn_selection : HostPreservesSelection promiseResultsCountFn := by
  intro st args hwf
  unfold promiseResultsCountFn
  dsimp only
  split <;> exact hwf

theorem promiseResultFn_selection : HostPreservesSelection promiseResultFn := by
  unfold promiseResultFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

end Wasm.Near
