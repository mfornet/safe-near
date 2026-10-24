import NearVM.GasInvariants

namespace Wasm.Near

/-- Functional hosts leave gas charging to the metered wrapper. -/
def HostPreservesGas (fn : NearHostFn NearState) : Prop :=
  ∀ st args, HostResult.Satisfies (fun ns => ns.gas = st.host.gas) (fn.invoke st args)

theorem checkedSetRegister_gas {st after : HostStore NearState} {register : UInt64} {bytes : List UInt8}
    (h : checkedSetRegister? st register bytes = some after) : after.host.gas = st.host.gas := by
  unfold checkedSetRegister? at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem writeRegisterResult_gas (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (vals : List Value) :
    HostResult.Satisfies (fun ns => ns.gas = st.host.gas) (writeRegisterResult name st register bytes vals) := by
  unfold writeRegisterResult
  split
  · exact checkedSetRegister_gas (by assumption)
  · rfl

theorem inputFn_gas : HostPreservesGas inputFn := by
  intro st args
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem readRegisterFn_gas : HostPreservesGas readRegisterFn := by
  intro st args
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem registerLenFn_gas : HostPreservesGas registerLenFn := by
  intro st args
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem writeRegisterFn_gas : HostPreservesGas writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem storageWriteFn_gas : HostPreservesGas storageWriteFn := by
  intro st args
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)
  all_goals simp_all only [HostResult.Satisfies, NearState.setStorage,
    NearState.invalidateIterators]
  all_goals first | rfl | (rename_i hreg; exact checkedSetRegister_gas hreg)

theorem storageReadFn_gas : HostPreservesGas storageReadFn := by
  intro st args
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem storageRemoveFn_gas : HostPreservesGas storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)
  all_goals simp_all only [HostResult.Satisfies, NearState.removeStorage,
    NearState.invalidateIterators]
  all_goals first | rfl | (rename_i hreg; exact checkedSetRegister_gas hreg)

theorem storageHasKeyFn_gas : HostPreservesGas storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem currentAccountIdFn_gas : HostPreservesGas currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem predecessorAccountIdFn_gas : HostPreservesGas predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem signerAccountIdFn_gas : HostPreservesGas signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem signerAccountPkFn_gas : HostPreservesGas signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem attachedDepositFn_gas : HostPreservesGas attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem blockIndexFn_gas : HostPreservesGas blockIndexFn := by
  intro st args
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem blockTimestampFn_gas : HostPreservesGas blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem epochHeightFn_gas : HostPreservesGas epochHeightFn := by
  intro st args
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem storageUsageFn_gas : HostPreservesGas storageUsageFn := by
  intro st args
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem accountBalanceFn_gas : HostPreservesGas accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem accountLockedBalanceFn_gas : HostPreservesGas accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem prepaidGasFn_gas : HostPreservesGas prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem usedGasFn_gas : HostPreservesGas usedGasFn := by
  intro st args
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem randomSeedFn_gas : HostPreservesGas randomSeedFn := by
  intro st args
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem chainIdFn_gas : HostPreservesGas chainIdFn := by
  intro st args
  unfold chainIdFn contextRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem logUtf8Fn_gas : HostPreservesGas logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem logUtf16Fn_gas : HostPreservesGas logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem panicMetered_gas : HostPreservesGas panicMetered := by
  intro st args
  unfold panicMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem panicUtf8Metered_gas : HostPreservesGas panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem abortMetered_gas : HostPreservesGas abortMetered := by
  intro st args
  unfold abortMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseCreateFn_gas : HostPreservesGas promiseCreateFn := by
  intro st args
  unfold promiseCreateFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseThenFn_gas : HostPreservesGas promiseThenFn := by
  intro st args
  unfold promiseThenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseAndFn_gas : HostPreservesGas promiseAndFn := by
  intro st args
  unfold promiseAndFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchCreateFn_gas : HostPreservesGas promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchThenFn_gas : HostPreservesGas promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionCreateAccountFn_gas : HostPreservesGas promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionDeployContractFn_gas : HostPreservesGas promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionFunctionCallFn_gas : HostPreservesGas promiseBatchActionFunctionCallFn := by
  intro st args
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionFunctionCallWeightFn_gas : HostPreservesGas promiseBatchActionFunctionCallWeightFn := by
  intro st args
  unfold promiseBatchActionFunctionCallWeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionTransferFn_gas : HostPreservesGas promiseBatchActionTransferFn := by
  intro st args
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionTransferToGasKeyFn_gas : HostPreservesGas promiseBatchActionTransferToGasKeyFn := by
  intro st args
  unfold promiseBatchActionTransferToGasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionStakeFn_gas : HostPreservesGas promiseBatchActionStakeFn := by
  intro st args
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_gas : HostPreservesGas promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionAddGasKeyWithFullAccessFn_gas : HostPreservesGas promiseBatchActionAddGasKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddGasKeyWithFullAccessFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_gas : HostPreservesGas promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionAddGasKeyWithFunctionCallFn_gas : HostPreservesGas promiseBatchActionAddGasKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddGasKeyWithFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionDeleteKeyFn_gas : HostPreservesGas promiseBatchActionDeleteKeyFn := by
  intro st args
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionDeleteAccountFn_gas : HostPreservesGas promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionUseGlobalContractFn_gas : HostPreservesGas promiseBatchActionUseGlobalContractFn := by
  intro st args
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionDeployGlobalContractFn_gas : HostPreservesGas promiseBatchActionDeployGlobalContractFn := by
  intro st args
  unfold promiseBatchActionDeployGlobalContractFn deployGlobalContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionUseGlobalContractByAccountIdFn_gas : HostPreservesGas promiseBatchActionUseGlobalContractByAccountIdFn := by
  intro st args
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseBatchActionDeployGlobalContractByAccountIdFn_gas : HostPreservesGas promiseBatchActionDeployGlobalContractByAccountIdFn := by
  intro st args
  unfold promiseBatchActionDeployGlobalContractByAccountIdFn deployGlobalContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem valueReturnFn_gas : HostPreservesGas valueReturnFn := by
  intro st args
  unfold valueReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseReturnFn_gas : HostPreservesGas promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseResultsCountFn_gas : HostPreservesGas promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem promiseResultFn_gas : HostPreservesGas promiseResultFn := by
  intro st args
  unfold promiseResultFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)


-- TODO(proof): yield create/resume gas preservation.
theorem promiseYieldCreateFn_gas : HostPreservesGas promiseYieldCreateFn := by
  sorry

theorem promiseYieldResumeFn_gas : HostPreservesGas promiseYieldResumeFn := by
  sorry

end Wasm.Near
