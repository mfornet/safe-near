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

/-- Unfolds the shared host helpers and closes the gas-preserving cases. -/
local macro "host_gas_tac" : tactic => `(tactic| (
    dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
      contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
      checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
      appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
      NearState.selectReturnValue, NearState.selectReturnPromise]
    repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)))

theorem inputFn_gas : HostPreservesGas inputFn := by
  intro st args
  unfold inputFn
  host_gas_tac

theorem readRegisterFn_gas : HostPreservesGas readRegisterFn := by
  intro st args
  unfold readRegisterFn
  host_gas_tac

theorem registerLenFn_gas : HostPreservesGas registerLenFn := by
  intro st args
  unfold registerLenFn
  host_gas_tac

theorem writeRegisterFn_gas : HostPreservesGas writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  host_gas_tac

theorem storageWriteFn_gas : HostPreservesGas storageWriteFn := by
  intro st args
  unfold storageWriteFn
  host_gas_tac
  all_goals simp_all only [HostResult.Satisfies, NearState.setStorage,
    NearState.invalidateIterators]
  all_goals first | rfl | (rename_i hreg; exact checkedSetRegister_gas hreg)

theorem storageReadFn_gas : HostPreservesGas storageReadFn := by
  intro st args
  unfold storageReadFn
  host_gas_tac

theorem storageRemoveFn_gas : HostPreservesGas storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  host_gas_tac
  all_goals simp_all only [HostResult.Satisfies, NearState.removeStorage,
    NearState.invalidateIterators]
  all_goals first | rfl | (rename_i hreg; exact checkedSetRegister_gas hreg)

theorem storageHasKeyFn_gas : HostPreservesGas storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  host_gas_tac

theorem currentAccountIdFn_gas : HostPreservesGas currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  host_gas_tac

theorem predecessorAccountIdFn_gas : HostPreservesGas predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  host_gas_tac

theorem signerAccountIdFn_gas : HostPreservesGas signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  host_gas_tac

theorem signerAccountPkFn_gas : HostPreservesGas signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  host_gas_tac

theorem attachedDepositFn_gas : HostPreservesGas attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  host_gas_tac

theorem blockIndexFn_gas : HostPreservesGas blockIndexFn := by
  intro st args
  unfold blockIndexFn
  host_gas_tac

theorem blockTimestampFn_gas : HostPreservesGas blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  host_gas_tac

theorem epochHeightFn_gas : HostPreservesGas epochHeightFn := by
  intro st args
  unfold epochHeightFn
  host_gas_tac

theorem storageUsageFn_gas : HostPreservesGas storageUsageFn := by
  intro st args
  unfold storageUsageFn
  host_gas_tac

theorem accountBalanceFn_gas : HostPreservesGas accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  host_gas_tac

theorem accountLockedBalanceFn_gas : HostPreservesGas accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  host_gas_tac

theorem validatorStakeFn_gas : HostPreservesGas validatorStakeFn := by
  intro st args
  unfold validatorStakeFn
  host_gas_tac

theorem validatorTotalStakeFn_gas : HostPreservesGas validatorTotalStakeFn := by
  intro st args
  unfold validatorTotalStakeFn
  host_gas_tac

theorem prepaidGasFn_gas : HostPreservesGas prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  host_gas_tac

theorem usedGasFn_gas : HostPreservesGas usedGasFn := by
  intro st args
  unfold usedGasFn
  host_gas_tac

theorem randomSeedFn_gas : HostPreservesGas randomSeedFn := by
  intro st args
  unfold randomSeedFn
  host_gas_tac

theorem cryptoHostFn_gas (name : String) (params results : List ValType) : HostPreservesGas (cryptoHostFn name params results) := by
  intro st args
  unfold cryptoHostFn
  dsimp only
  repeat (first | rfl | exact writeRegisterResult_gas _ _ _ _ _ | split)

theorem sha256Fn_gas : HostPreservesGas sha256Fn := cryptoHostFn_gas _ _ _

theorem keccak256Fn_gas : HostPreservesGas keccak256Fn := cryptoHostFn_gas _ _ _

theorem keccak512Fn_gas : HostPreservesGas keccak512Fn := cryptoHostFn_gas _ _ _

theorem ripemd160Fn_gas : HostPreservesGas ripemd160Fn := cryptoHostFn_gas _ _ _

theorem ecrecoverFn_gas : HostPreservesGas ecrecoverFn := cryptoHostFn_gas _ _ _

theorem ed25519VerifyFn_gas : HostPreservesGas ed25519VerifyFn := cryptoHostFn_gas _ _ _

theorem p256VerifyFn_gas : HostPreservesGas p256VerifyFn := cryptoHostFn_gas _ _ _

theorem altBn128G1MultiexpFn_gas : HostPreservesGas altBn128G1MultiexpFn := cryptoHostFn_gas _ _ _

theorem altBn128G1SumFn_gas : HostPreservesGas altBn128G1SumFn := cryptoHostFn_gas _ _ _

theorem altBn128PairingCheckFn_gas : HostPreservesGas altBn128PairingCheckFn := cryptoHostFn_gas _ _ _

theorem bls12381P1SumFn_gas : HostPreservesGas bls12381P1SumFn := cryptoHostFn_gas _ _ _

theorem bls12381P2SumFn_gas : HostPreservesGas bls12381P2SumFn := cryptoHostFn_gas _ _ _

theorem bls12381G1MultiexpFn_gas : HostPreservesGas bls12381G1MultiexpFn := cryptoHostFn_gas _ _ _

theorem bls12381G2MultiexpFn_gas : HostPreservesGas bls12381G2MultiexpFn := cryptoHostFn_gas _ _ _

theorem bls12381MapFpToG1Fn_gas : HostPreservesGas bls12381MapFpToG1Fn := cryptoHostFn_gas _ _ _

theorem bls12381MapFp2ToG2Fn_gas : HostPreservesGas bls12381MapFp2ToG2Fn := cryptoHostFn_gas _ _ _

theorem bls12381P1DecompressFn_gas : HostPreservesGas bls12381P1DecompressFn := cryptoHostFn_gas _ _ _

theorem bls12381P2DecompressFn_gas : HostPreservesGas bls12381P2DecompressFn := cryptoHostFn_gas _ _ _

theorem bls12381PairingCheckFn_gas : HostPreservesGas bls12381PairingCheckFn := cryptoHostFn_gas _ _ _

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
  host_gas_tac

theorem logUtf16Fn_gas : HostPreservesGas logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  host_gas_tac

theorem panicMetered_gas : HostPreservesGas panicMetered := by
  intro st args
  unfold panicMetered
  host_gas_tac

theorem panicUtf8Metered_gas : HostPreservesGas panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  host_gas_tac

theorem abortMetered_gas : HostPreservesGas abortMetered := by
  intro st args
  unfold abortMetered
  host_gas_tac

theorem promiseCreateFn_gas : HostPreservesGas promiseCreateFn := by
  intro st args
  unfold promiseCreateFn
  host_gas_tac

theorem promiseThenFn_gas : HostPreservesGas promiseThenFn := by
  intro st args
  unfold promiseThenFn
  host_gas_tac

theorem promiseAndFn_gas : HostPreservesGas promiseAndFn := by
  intro st args
  unfold promiseAndFn
  host_gas_tac

theorem promiseBatchCreateFn_gas : HostPreservesGas promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  host_gas_tac

theorem promiseBatchThenFn_gas : HostPreservesGas promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  host_gas_tac

theorem promiseBatchActionCreateAccountFn_gas : HostPreservesGas promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  host_gas_tac

theorem promiseBatchActionDeployContractFn_gas : HostPreservesGas promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  host_gas_tac

theorem promiseBatchActionFunctionCallFn_gas : HostPreservesGas promiseBatchActionFunctionCallFn := by
  intro st args
  unfold promiseBatchActionFunctionCallFn
  host_gas_tac

theorem promiseBatchActionFunctionCallWeightFn_gas : HostPreservesGas promiseBatchActionFunctionCallWeightFn := by
  intro st args
  unfold promiseBatchActionFunctionCallWeightFn
  host_gas_tac

theorem promiseBatchActionTransferFn_gas : HostPreservesGas promiseBatchActionTransferFn := by
  intro st args
  unfold promiseBatchActionTransferFn
  host_gas_tac

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
  host_gas_tac

theorem promiseBatchActionAddKeyWithFullAccessFn_gas : HostPreservesGas promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  host_gas_tac

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
  host_gas_tac

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
  host_gas_tac

theorem promiseBatchActionDeleteAccountFn_gas : HostPreservesGas promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  host_gas_tac

theorem promiseBatchActionUseGlobalContractFn_gas : HostPreservesGas promiseBatchActionUseGlobalContractFn := by
  intro st args
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  host_gas_tac

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
  host_gas_tac

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
  host_gas_tac

theorem promiseReturnFn_gas : HostPreservesGas promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  host_gas_tac

theorem promiseResultsCountFn_gas : HostPreservesGas promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  host_gas_tac

theorem promiseResultFn_gas : HostPreservesGas promiseResultFn := by
  intro st args
  unfold promiseResultFn
  host_gas_tac


theorem promiseYieldCreateFn_gas : HostPreservesGas promiseYieldCreateFn := by
  intro st args
  unfold promiseYieldCreateFn
  dsimp only [disallowInView, appendPromise]
  repeat (first | rfl | split)
  all_goals first | trivial | (simp only [HostResult.Satisfies]; exact checkedSetRegister_gas ‹_›)

theorem promiseYieldResumeFn_gas : HostPreservesGas promiseYieldResumeFn := by
  intro st args
  unfold promiseYieldResumeFn
  dsimp only [disallowInView]
  repeat (first | rfl | trivial | split)

end Wasm.Near
