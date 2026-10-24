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

/-- Unfolds the shared host helpers and closes the deposit-neutral cases. -/
local macro "no_deposits_tac" : tactic => `(tactic| (
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
      | split)))

theorem inputFn_noDeposits : HostCreatesNoDeposits inputFn := by
  intro st args
  unfold inputFn
  no_deposits_tac

theorem readRegisterFn_noDeposits : HostCreatesNoDeposits readRegisterFn := by
  intro st args
  unfold readRegisterFn
  no_deposits_tac

theorem registerLenFn_noDeposits : HostCreatesNoDeposits registerLenFn := by
  intro st args
  unfold registerLenFn
  no_deposits_tac

theorem writeRegisterFn_noDeposits : HostCreatesNoDeposits writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  no_deposits_tac

theorem storageWriteFn_noDeposits : HostCreatesNoDeposits storageWriteFn := by
  intro st args
  unfold storageWriteFn
  no_deposits_tac
  all_goals simp_all only [HostResultCreatesDeposits, DepositEffect, NearState.setStorage, NearState.invalidateIterators]
  all_goals first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | (have h := checkedSetRegister_deposits (by assumption); exact h)

theorem storageReadFn_noDeposits : HostCreatesNoDeposits storageReadFn := by
  intro st args
  unfold storageReadFn
  no_deposits_tac

theorem storageRemoveFn_noDeposits : HostCreatesNoDeposits storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  no_deposits_tac
  all_goals simp_all only [HostResultCreatesDeposits, DepositEffect, NearState.removeStorage, NearState.invalidateIterators]
  all_goals first
    | trivial
    | exact ⟨rfl, rfl, rfl⟩
    | (have h := checkedSetRegister_deposits (by assumption); exact h)

theorem storageHasKeyFn_noDeposits : HostCreatesNoDeposits storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  no_deposits_tac

theorem currentAccountIdFn_noDeposits : HostCreatesNoDeposits currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  no_deposits_tac

theorem predecessorAccountIdFn_noDeposits : HostCreatesNoDeposits predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  no_deposits_tac

theorem signerAccountIdFn_noDeposits : HostCreatesNoDeposits signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  no_deposits_tac

theorem signerAccountPkFn_noDeposits : HostCreatesNoDeposits signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  no_deposits_tac

theorem attachedDepositFn_noDeposits : HostCreatesNoDeposits attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  no_deposits_tac

theorem blockIndexFn_noDeposits : HostCreatesNoDeposits blockIndexFn := by
  intro st args
  unfold blockIndexFn
  no_deposits_tac

theorem blockTimestampFn_noDeposits : HostCreatesNoDeposits blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  no_deposits_tac

theorem epochHeightFn_noDeposits : HostCreatesNoDeposits epochHeightFn := by
  intro st args
  unfold epochHeightFn
  no_deposits_tac

theorem storageUsageFn_noDeposits : HostCreatesNoDeposits storageUsageFn := by
  intro st args
  unfold storageUsageFn
  no_deposits_tac

theorem accountBalanceFn_noDeposits : HostCreatesNoDeposits accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  no_deposits_tac

theorem accountLockedBalanceFn_noDeposits : HostCreatesNoDeposits accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  no_deposits_tac

theorem prepaidGasFn_noDeposits : HostCreatesNoDeposits prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  no_deposits_tac

theorem usedGasFn_noDeposits : HostCreatesNoDeposits usedGasFn := by
  intro st args
  unfold usedGasFn
  no_deposits_tac

theorem randomSeedFn_noDeposits : HostCreatesNoDeposits randomSeedFn := by
  intro st args
  unfold randomSeedFn
  no_deposits_tac

theorem chainIdFn_noDeposits : HostCreatesNoDeposits chainIdFn := by
  intro st args
  unfold chainIdFn contextRegisterFn
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
  no_deposits_tac

theorem logUtf16Fn_noDeposits : HostCreatesNoDeposits logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  no_deposits_tac

theorem panicMetered_noDeposits : HostCreatesNoDeposits panicMetered := by
  intro st args
  unfold panicMetered
  no_deposits_tac

theorem panicUtf8Metered_noDeposits : HostCreatesNoDeposits panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  no_deposits_tac

theorem abortMetered_noDeposits : HostCreatesNoDeposits abortMetered := by
  intro st args
  unfold abortMetered
  no_deposits_tac

theorem promiseAndFn_noDeposits : HostCreatesNoDeposits promiseAndFn := by
  intro st args
  unfold promiseAndFn
  no_deposits_tac

theorem promiseBatchCreateFn_noDeposits : HostCreatesNoDeposits promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  no_deposits_tac

theorem promiseBatchThenFn_noDeposits : HostCreatesNoDeposits promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  no_deposits_tac

theorem promiseBatchActionCreateAccountFn_noDeposits : HostCreatesNoDeposits promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  no_deposits_tac

theorem promiseBatchActionDeployContractFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  no_deposits_tac

theorem promiseBatchActionStakeFn_noDeposits : HostCreatesNoDeposits promiseBatchActionStakeFn := by
  intro st args
  unfold promiseBatchActionStakeFn
  no_deposits_tac

theorem promiseBatchActionAddKeyWithFullAccessFn_noDeposits : HostCreatesNoDeposits promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  no_deposits_tac

theorem promiseBatchActionAddGasKeyWithFullAccessFn_noDeposits : HostCreatesNoDeposits promiseBatchActionAddGasKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddGasKeyWithFullAccessFn
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
  no_deposits_tac

theorem promiseBatchActionAddGasKeyWithFunctionCallFn_noDeposits : HostCreatesNoDeposits promiseBatchActionAddGasKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddGasKeyWithFunctionCallFn
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
  no_deposits_tac

theorem promiseBatchActionDeleteAccountFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  no_deposits_tac

theorem promiseBatchActionUseGlobalContractFn_noDeposits : HostCreatesNoDeposits promiseBatchActionUseGlobalContractFn := by
  intro st args
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  no_deposits_tac

theorem promiseBatchActionDeployGlobalContractFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeployGlobalContractFn := by
  intro st args
  unfold promiseBatchActionDeployGlobalContractFn deployGlobalContractFn
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

theorem promiseBatchActionUseGlobalContractByAccountIdFn_noDeposits : HostCreatesNoDeposits promiseBatchActionUseGlobalContractByAccountIdFn := by
  intro st args
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  no_deposits_tac

theorem promiseBatchActionDeployGlobalContractByAccountIdFn_noDeposits : HostCreatesNoDeposits promiseBatchActionDeployGlobalContractByAccountIdFn := by
  intro st args
  unfold promiseBatchActionDeployGlobalContractByAccountIdFn deployGlobalContractFn
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
  no_deposits_tac

theorem promiseReturnFn_noDeposits : HostCreatesNoDeposits promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  no_deposits_tac

theorem promiseResultsCountFn_noDeposits : HostCreatesNoDeposits promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  no_deposits_tac

theorem promiseResultFn_noDeposits : HostCreatesNoDeposits promiseResultFn := by
  intro st args
  unfold promiseResultFn
  no_deposits_tac

theorem gasFn_noDeposits (opCost : Nat) : HostCreatesNoDeposits (gasFn opCost) := by
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


theorem promiseYieldCreateFn_noDeposits : HostCreatesNoDeposits promiseYieldCreateFn := by
  intro st args
  unfold promiseYieldCreateFn
  dsimp only [disallowInView]
  repeat (first | trivial | exact ⟨rfl, rfl, rfl⟩ | split)
  all_goals first
    | trivial
    | (obtain ⟨a1, a2, a3⟩ := checkedSetRegister_deposits ‹_›
       refine ⟨a1, a2, (appendPromise_deposits _ _).trans ?_⟩
       rw [a3]
       simp [promiseValue, depositValue, PromiseAction.deposit])

theorem promiseYieldResumeFn_noDeposits : HostCreatesNoDeposits promiseYieldResumeFn := by
  intro st args
  unfold promiseYieldResumeFn
  dsimp only [disallowInView]
  repeat (first | trivial | exact ⟨rfl, rfl, rfl⟩ | split)

end Wasm.Near
