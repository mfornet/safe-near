import NearVM.MeteredDeposits

namespace Wasm.Near

def HostCreatesNoDeposits (fn : NearHostFn NearState) : Prop :=
  ∀ st args, HostResultCreatesDeposits st.host 0 (fn.invoke st args)

theorem checkedSetRegister_deposits {st after : HostStore NearState} {register : UInt64} {bytes : List UInt8}
    (h : checkedSetRegister? st register bytes = some after) : DepositEffect st.host after.host 0 := by
  unfold checkedSetRegister? at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h

theorem writeRegisterResult_deposits (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (values : List Value) :
    HostResultCreatesDeposits st.host 0 (writeRegisterResult name st register bytes values) := by
  unfold writeRegisterResult
  split
  · exact checkedSetRegister_deposits (by assumption)
  · trivial

theorem createBatchPromiseResult_deposits (name : String) (st : HostStore NearState) (account : List UInt8) :
    HostResultCreatesDeposits st.host 0 (createBatchPromiseResult name st account) := by
  unfold createBatchPromiseResult checkAccountId
  split
  · exact appendPromise_return_deposits _ _ _
  · trivial

theorem createCallbackPromiseResult_deposits (name : String) (st : HostStore NearState) (base : UInt64)
    (account : List UInt8) : HostResultCreatesDeposits st.host 0 (createCallbackPromiseResult name st base account) := by
  unfold createCallbackPromiseResult checkAccountId
  split
  · split
    · exact appendPromise_return_deposits _ _ _
    · trivial
  · trivial

theorem inputFn_noDeposits : HostCreatesNoDeposits inputFn := by
  intro st args
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem readRegisterFn_noDeposits : HostCreatesNoDeposits readRegisterFn := by
  intro st args
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem registerLenFn_noDeposits : HostCreatesNoDeposits registerLenFn := by
  intro st args
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem writeRegisterFn_noDeposits : HostCreatesNoDeposits writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem storageWriteFn_noDeposits : HostCreatesNoDeposits storageWriteFn := by
  intro st args
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)
  all_goals simp_all only [HostResultCreatesDeposits, DepositEffect, NearState.setStorage, NearState.invalidateIterators]
  all_goals first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | (have h := checkedSetRegister_deposits (by assumption); exact h)

theorem storageReadFn_noDeposits : HostCreatesNoDeposits storageReadFn := by
  intro st args
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem storageRemoveFn_noDeposits : HostCreatesNoDeposits storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)
  all_goals simp_all only [HostResultCreatesDeposits, DepositEffect, NearState.removeStorage, NearState.invalidateIterators]
  all_goals first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | (have h := checkedSetRegister_deposits (by assumption); exact h)

theorem storageHasKeyFn_noDeposits : HostCreatesNoDeposits storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem currentAccountIdFn_noDeposits : HostCreatesNoDeposits currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem predecessorAccountIdFn_noDeposits : HostCreatesNoDeposits predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem signerAccountIdFn_noDeposits : HostCreatesNoDeposits signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem signerAccountPkFn_noDeposits : HostCreatesNoDeposits signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem attachedDepositFn_noDeposits : HostCreatesNoDeposits attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem blockIndexFn_noDeposits : HostCreatesNoDeposits blockIndexFn := by
  intro st args
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem blockTimestampFn_noDeposits : HostCreatesNoDeposits blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem epochHeightFn_noDeposits : HostCreatesNoDeposits epochHeightFn := by
  intro st args
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem storageUsageFn_noDeposits : HostCreatesNoDeposits storageUsageFn := by
  intro st args
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem accountBalanceFn_noDeposits : HostCreatesNoDeposits accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem accountLockedBalanceFn_noDeposits : HostCreatesNoDeposits accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem prepaidGasFn_noDeposits : HostCreatesNoDeposits prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem usedGasFn_noDeposits : HostCreatesNoDeposits usedGasFn := by
  intro st args
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem randomSeedFn_noDeposits : HostCreatesNoDeposits randomSeedFn := by
  intro st args
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem logUtf8Fn_noDeposits : HostCreatesNoDeposits logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem logUtf16Fn_noDeposits : HostCreatesNoDeposits logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem panicMetered_noDeposits : HostCreatesNoDeposits panicMetered := by
  intro st args
  unfold panicMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem panicUtf8Metered_noDeposits : HostCreatesNoDeposits panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem abortMetered_noDeposits : HostCreatesNoDeposits abortMetered := by
  intro st args
  unfold abortMetered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseAndFn_noDeposits : HostCreatesNoDeposits promiseAndFn := by
  intro st args
  unfold promiseAndFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchCreateFn_noDeposits : HostCreatesNoDeposits promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchThenFn_noDeposits : HostCreatesNoDeposits promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionCreateAccountFn_noDeposits : HostCreatesNoDeposits promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionDeployContractFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionStakeFn_noDeposits : HostCreatesNoDeposits promiseBatchActionStakeFn := by
  intro st args
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_noDeposits : HostCreatesNoDeposits promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_noDeposits : HostCreatesNoDeposits promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionDeleteKeyFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeleteKeyFn := by
  intro st args
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseBatchActionDeleteAccountFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem valueReturnFn_noDeposits : HostCreatesNoDeposits valueReturnFn := by
  intro st args
  unfold valueReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseReturnFn_noDeposits : HostCreatesNoDeposits promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseResultsCountFn_noDeposits : HostCreatesNoDeposits promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem promiseResultFn_noDeposits : HostCreatesNoDeposits promiseResultFn := by
  intro st args
  unfold promiseResultFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise]
  repeat (first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | exact writeRegisterResult_deposits _ _ _ _ _
    | exact appendPromise_return_deposits _ _ _
    | exact appendPromiseActionResult_deposits _ _ _ _
    | exact createBatchPromiseResult_deposits _ _ _
    | exact createCallbackPromiseResult_deposits _ _ _ _
    | split)

theorem gasFn_noDeposits : HostCreatesNoDeposits gasFn := by
  intro st args
  unfold gasFn
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · trivial
  · trivial

theorem HostCreatesNoDeposits.funding {fn : NearHostFn NearState} (h : HostCreatesNoDeposits fn) :
    HostPreservesFunding fn := by
  intro st args
  have hp := h st args
  cases hr : fn.invoke st args with
  | Trap paid message => trivial
  | Return values paid =>
    rw [hr] at hp
    change DepositEffect st.host paid.host 0 at hp
    change paid.host.liquidFunds + st.host.subsidizedAmount = st.host.liquidFunds + paid.host.subsidizedAmount
    simp only [NearState.liquidFunds, hp.1, hp.2.1, hp.2.2, Nat.add_zero]

end Wasm.Near
