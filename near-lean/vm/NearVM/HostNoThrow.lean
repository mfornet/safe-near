import NearVM.DepositRegistry
import NearVM.LiveInvariant

namespace Wasm.Near

/-- NEAR host APIs return or trap; they do not raise catchable Wasm exceptions. -/
def HostResult.NoThrow : HostResult α → Prop
  | .Throw .. => False
  | .Return .. | .Trap .. => True

def HostNeverThrows (fn : HostFn α) : Prop := ∀ st args, HostResult.NoThrow (fn.invoke st args)

theorem inputFn_noThrow : HostNeverThrows inputFn := by
  intro st args
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem readRegisterFn_noThrow : HostNeverThrows readRegisterFn := by
  intro st args
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem registerLenFn_noThrow : HostNeverThrows registerLenFn := by
  intro st args
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem writeRegisterFn_noThrow : HostNeverThrows writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem storageWriteFn_noThrow : HostNeverThrows storageWriteFn := by
  intro st args
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem storageReadFn_noThrow : HostNeverThrows storageReadFn := by
  intro st args
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem storageRemoveFn_noThrow : HostNeverThrows storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem storageHasKeyFn_noThrow : HostNeverThrows storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem currentAccountIdFn_noThrow : HostNeverThrows currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem predecessorAccountIdFn_noThrow : HostNeverThrows predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem signerAccountIdFn_noThrow : HostNeverThrows signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem signerAccountPkFn_noThrow : HostNeverThrows signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem attachedDepositFn_noThrow : HostNeverThrows attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem blockIndexFn_noThrow : HostNeverThrows blockIndexFn := by
  intro st args
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem blockTimestampFn_noThrow : HostNeverThrows blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem epochHeightFn_noThrow : HostNeverThrows epochHeightFn := by
  intro st args
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem storageUsageFn_noThrow : HostNeverThrows storageUsageFn := by
  intro st args
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem accountBalanceFn_noThrow : HostNeverThrows accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem accountLockedBalanceFn_noThrow : HostNeverThrows accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem prepaidGasFn_noThrow : HostNeverThrows prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem usedGasFn_noThrow : HostNeverThrows usedGasFn := by
  intro st args
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem randomSeedFn_noThrow : HostNeverThrows randomSeedFn := by
  intro st args
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem logUtf8Fn_noThrow : HostNeverThrows logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem logUtf16Fn_noThrow : HostNeverThrows logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem panicMetered_noThrow : HostNeverThrows panicMetered := by
  intro st args
  unfold panicMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem panicUtf8Metered_noThrow : HostNeverThrows panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem abortMetered_noThrow : HostNeverThrows abortMetered := by
  intro st args
  unfold abortMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseCreateFn_noThrow : HostNeverThrows promiseCreateFn := by
  intro st args
  unfold promiseCreateFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseThenFn_noThrow : HostNeverThrows promiseThenFn := by
  intro st args
  unfold promiseThenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseAndFn_noThrow : HostNeverThrows promiseAndFn := by
  intro st args
  unfold promiseAndFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchCreateFn_noThrow : HostNeverThrows promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchThenFn_noThrow : HostNeverThrows promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionCreateAccountFn_noThrow : HostNeverThrows promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionDeployContractFn_noThrow : HostNeverThrows promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionFunctionCallFn_noThrow : HostNeverThrows promiseBatchActionFunctionCallFn := by
  intro st args
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionTransferFn_noThrow : HostNeverThrows promiseBatchActionTransferFn := by
  intro st args
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionStakeFn_noThrow : HostNeverThrows promiseBatchActionStakeFn := by
  intro st args
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_noThrow : HostNeverThrows promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_noThrow : HostNeverThrows promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionDeleteKeyFn_noThrow : HostNeverThrows promiseBatchActionDeleteKeyFn := by
  intro st args
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseBatchActionDeleteAccountFn_noThrow : HostNeverThrows promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem valueReturnFn_noThrow : HostNeverThrows valueReturnFn := by
  intro st args
  unfold valueReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseReturnFn_noThrow : HostNeverThrows promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseResultsCountFn_noThrow : HostNeverThrows promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem promiseResultFn_noThrow : HostNeverThrows promiseResultFn := by
  intro st args
  unfold promiseResultFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult,
    NearState.selectReturnValue, NearState.selectReturnPromise, writeRegisterResult]
  repeat (first | trivial | split)

theorem gasFn_noThrow : HostNeverThrows gasFn := by
  intro st args
  unfold gasFn
  dsimp only
  repeat (first | trivial | split)

theorem finishMeteredCall_noThrow (extra : Nat) (name : String) (before : Store NearState)
    (args : List Value) (result : HostResult NearState) (h : HostResult.NoThrow result) :
    HostResult.NoThrow (finishMeteredCall extra name before args result) := by
  cases result <;> try exact h
  unfold finishMeteredCall
  dsimp only
  repeat (first | trivial | split)

theorem metered_noThrow (extra : Nat) (name : String) (fn : HostFn NearState)
    (hfn : HostNeverThrows fn) : HostNeverThrows (metered extra name fn) := by
  intro st args
  unfold metered invokeStorageCall
  dsimp only
  repeat (first | trivial | exact finishMeteredCall_noThrow _ _ _ _ _ (hfn _ _) | split)

set_option maxHeartbeats 2000000 in
/-- Published host imports cannot raise catchable exceptions. -/
theorem meteredHostFns_noThrow (cfg : RuntimeConfig) (entry : ImportDecl × HostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostNeverThrows entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro st args; trivial)
      | apply metered_noThrow
    all_goals first
      | exact inputFn_noThrow
      | exact readRegisterFn_noThrow
      | exact registerLenFn_noThrow
      | exact writeRegisterFn_noThrow
      | exact storageWriteFn_noThrow
      | exact storageReadFn_noThrow
      | exact storageRemoveFn_noThrow
      | exact storageHasKeyFn_noThrow
      | exact currentAccountIdFn_noThrow
      | exact predecessorAccountIdFn_noThrow
      | exact signerAccountIdFn_noThrow
      | exact signerAccountPkFn_noThrow
      | exact attachedDepositFn_noThrow
      | exact blockIndexFn_noThrow
      | exact blockTimestampFn_noThrow
      | exact epochHeightFn_noThrow
      | exact storageUsageFn_noThrow
      | exact accountBalanceFn_noThrow
      | exact accountLockedBalanceFn_noThrow
      | exact prepaidGasFn_noThrow
      | exact usedGasFn_noThrow
      | exact randomSeedFn_noThrow
      | exact logUtf8Fn_noThrow
      | exact logUtf16Fn_noThrow
      | exact panicMetered_noThrow
      | exact panicUtf8Metered_noThrow
      | exact abortMetered_noThrow
      | exact gasFn_noThrow
      | exact promiseCreateFn_noThrow
      | exact promiseThenFn_noThrow
      | exact promiseAndFn_noThrow
      | exact promiseBatchCreateFn_noThrow
      | exact promiseBatchThenFn_noThrow
      | exact promiseBatchActionCreateAccountFn_noThrow
      | exact promiseBatchActionDeployContractFn_noThrow
      | exact promiseBatchActionFunctionCallFn_noThrow
      | exact promiseBatchActionTransferFn_noThrow
      | exact promiseBatchActionStakeFn_noThrow
      | exact promiseBatchActionAddKeyWithFullAccessFn_noThrow
      | exact promiseBatchActionAddKeyWithFunctionCallFn_noThrow
      | exact promiseBatchActionDeleteKeyFn_noThrow
      | exact promiseBatchActionDeleteAccountFn_noThrow
      | exact valueReturnFn_noThrow
      | exact promiseReturnFn_noThrow
      | exact promiseResultsCountFn_noThrow
      | exact promiseResultFn_noThrow
  · subst entry
    exact gasFn_noThrow

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_noThrow (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostNeverThrows fn := by
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
        · exact meteredHostFns_noThrow cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_noThrow (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostNeverThrows fn :=
  resolveMeteredImports_noThrow cfg m.imports env h

end Wasm.Near
