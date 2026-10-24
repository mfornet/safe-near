import NearVM.ReturnSelection

namespace Wasm.Near

theorem inputFn_selection : HostPreservesSelection inputFn := by
  intro st args hwf
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem readRegisterFn_selection : HostPreservesSelection readRegisterFn := by
  intro st args hwf
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem registerLenFn_selection : HostPreservesSelection registerLenFn := by
  intro st args hwf
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem writeRegisterFn_selection : HostPreservesSelection writeRegisterFn := by
  intro st args hwf
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem storageWriteFn_selection : HostPreservesSelection storageWriteFn := by
  intro st args hwf
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)
  all_goals
    simp_all only [HostResult.Satisfies, NearState.setStorage,
      NearState.invalidateIterators]
  all_goals first
    | exact hwf
    | (rename_i hreg; exact checkedSetRegister_selection hreg hwf)

theorem storageReadFn_selection : HostPreservesSelection storageReadFn := by
  intro st args hwf
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem storageRemoveFn_selection : HostPreservesSelection storageRemoveFn := by
  intro st args hwf
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)
  all_goals
    simp_all only [HostResult.Satisfies, NearState.removeStorage,
      NearState.invalidateIterators]
  all_goals first
    | exact hwf
    | (rename_i hreg; exact checkedSetRegister_selection hreg hwf)

theorem storageHasKeyFn_selection : HostPreservesSelection storageHasKeyFn := by
  intro st args hwf
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem currentAccountIdFn_selection : HostPreservesSelection currentAccountIdFn := by
  intro st args hwf
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem predecessorAccountIdFn_selection : HostPreservesSelection predecessorAccountIdFn := by
  intro st args hwf
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem signerAccountIdFn_selection : HostPreservesSelection signerAccountIdFn := by
  intro st args hwf
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem signerAccountPkFn_selection : HostPreservesSelection signerAccountPkFn := by
  intro st args hwf
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem attachedDepositFn_selection : HostPreservesSelection attachedDepositFn := by
  intro st args hwf
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem blockIndexFn_selection : HostPreservesSelection blockIndexFn := by
  intro st args hwf
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem blockTimestampFn_selection : HostPreservesSelection blockTimestampFn := by
  intro st args hwf
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem epochHeightFn_selection : HostPreservesSelection epochHeightFn := by
  intro st args hwf
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem storageUsageFn_selection : HostPreservesSelection storageUsageFn := by
  intro st args hwf
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem accountBalanceFn_selection : HostPreservesSelection accountBalanceFn := by
  intro st args hwf
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem accountLockedBalanceFn_selection : HostPreservesSelection accountLockedBalanceFn := by
  intro st args hwf
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem prepaidGasFn_selection : HostPreservesSelection prepaidGasFn := by
  intro st args hwf
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem usedGasFn_selection : HostPreservesSelection usedGasFn := by
  intro st args hwf
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem randomSeedFn_selection : HostPreservesSelection randomSeedFn := by
  intro st args hwf
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem chainIdFn_selection : HostPreservesSelection chainIdFn := by
  intro st args hwf
  unfold chainIdFn contextRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem logUtf8Fn_selection : HostPreservesSelection logUtf8Fn := by
  intro st args hwf
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem logUtf16Fn_selection : HostPreservesSelection logUtf16Fn := by
  intro st args hwf
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem panicMetered_selection : HostPreservesSelection panicMetered := by
  intro st args hwf
  unfold panicMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem panicUtf8Metered_selection : HostPreservesSelection panicUtf8Metered := by
  intro st args hwf
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem abortMetered_selection : HostPreservesSelection abortMetered := by
  intro st args hwf
  unfold abortMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem gasFn_selection (opCost : Nat) : HostPreservesSelection (gasFn opCost) := by
  intro st args hwf
  unfold gasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn, contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit, checkAccountId, checkPublicKey, NearState.setRegister, trapWith]
  repeat (first
    | exact hwf
    | exact writeRegisterResult_selection _ _ _ _ _ hwf
    | split)

theorem promiseCreateFn_selection : HostPreservesSelection promiseCreateFn := by
  unfold promiseCreateFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseThenFn_selection : HostPreservesSelection promiseThenFn := by
  unfold promiseThenFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseAndFn_selection : HostPreservesSelection promiseAndFn := by
  unfold promiseAndFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchCreateFn_selection : HostPreservesSelection promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchThenFn_selection : HostPreservesSelection promiseBatchThenFn := by
  unfold promiseBatchThenFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionCreateAccountFn_selection : HostPreservesSelection promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeployContractFn_selection : HostPreservesSelection promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionFunctionCallFn_selection : HostPreservesSelection promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionFunctionCallWeightFn_selection : HostPreservesSelection promiseBatchActionFunctionCallWeightFn := by
  unfold promiseBatchActionFunctionCallWeightFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionTransferFn_selection : HostPreservesSelection promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionTransferToGasKeyFn_selection : HostPreservesSelection promiseBatchActionTransferToGasKeyFn := by
  unfold promiseBatchActionTransferToGasKeyFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionStakeFn_selection : HostPreservesSelection promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_selection : HostPreservesSelection promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddGasKeyWithFullAccessFn_selection : HostPreservesSelection promiseBatchActionAddGasKeyWithFullAccessFn := by
  unfold promiseBatchActionAddGasKeyWithFullAccessFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_selection : HostPreservesSelection promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddGasKeyWithFunctionCallFn_selection : HostPreservesSelection promiseBatchActionAddGasKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddGasKeyWithFunctionCallFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeleteKeyFn_selection : HostPreservesSelection promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeleteAccountFn_selection : HostPreservesSelection promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionUseGlobalContractFn_selection : HostPreservesSelection promiseBatchActionUseGlobalContractFn := by
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeployGlobalContractFn_selection : HostPreservesSelection promiseBatchActionDeployGlobalContractFn := by
  unfold promiseBatchActionDeployGlobalContractFn deployGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionUseGlobalContractByAccountIdFn_selection : HostPreservesSelection promiseBatchActionUseGlobalContractByAccountIdFn := by
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeployGlobalContractByAccountIdFn_selection : HostPreservesSelection promiseBatchActionDeployGlobalContractByAccountIdFn := by
  unfold promiseBatchActionDeployGlobalContractByAccountIdFn deployGlobalContractFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendPromise_selection _ _ hwf
    | exact appendPromiseActionResult_selection _ _ _ _ hwf
    | exact createBatchPromiseResult_selection _ _ _ hwf
    | exact createCallbackPromiseResult_selection _ _ _ _ hwf
    | apply checkAccountId_selection _ _ _ _ hwf
    | apply checkPublicKey_selection _ _ _ _ hwf
    | split)

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


theorem promiseYieldCreateFn_selection : HostPreservesSelection promiseYieldCreateFn := by
  unfold promiseYieldCreateFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first | exact hwf | split)
  all_goals first
    | trivial
    | exact appendPromise_selection _ _ (checkedSetRegister_selection ‹_› hwf)

theorem promiseYieldResumeFn_selection : HostPreservesSelection promiseYieldResumeFn := by
  unfold promiseYieldResumeFn
  apply disallowInView_selection
  intro st args hwf
  dsimp only
  repeat (first | exact hwf | split)

end Wasm.Near
