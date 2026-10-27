import Binary.Run
import NearLogic

/-!
# wNEAR's host functions under raised gas limits

Every host function `contract.wasm` links respects raised gas limits
(`wHosts_relax`), so every host function of the instantiated store does
(`storeRelaxFns_wStore`): the hypothesis of `NearLogic.runMetered_relax`
for every method of the binary.
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic

theorem wHosts_relax (cfg : RuntimeConfig) : ∀ fn ∈ wHosts cfg, RelaxFn fn.toHostFn := by
  intro fn h
  simp only [wHosts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [relaxFn_readRegister _, relaxFn_registerLen _, relaxFn_currentAccountId _, relaxFn_signerAccountId _,
    relaxFn_signerAccountPk _, relaxFn_predecessorAccountId _, relaxFn_input _, relaxFn_blockIndex _,
    relaxFn_blockTimestamp _, relaxFn_epochHeight _, relaxFn_storageUsage _, relaxFn_accountBalance _,
    relaxFn_accountLockedBalance _, relaxFn_attachedDeposit _, relaxFn_prepaidGas _, relaxFn_usedGas _,
    relaxFn_randomSeed _, relaxFn_sha256 _, relaxFn_keccak256 _, relaxFn_keccak512 _, relaxFn_valueReturn _,
    relaxFn_panic _, relaxFn_panicUtf8 _, relaxFn_logUtf8 _, relaxFn_logUtf16 _, relaxFn_promiseCreate _,
    relaxFn_promiseThen _, relaxFn_promiseAnd _, relaxFn_promiseBatchCreate _, relaxFn_promiseBatchThen _,
    relaxFn_promiseBatchActionCreateAccount _, relaxFn_promiseBatchActionDeployContract _,
    relaxFn_promiseBatchActionFunctionCall _, relaxFn_promiseBatchActionTransfer _,
    relaxFn_promiseBatchActionStake _, relaxFn_promiseBatchActionAddKeyWithFullAccess _,
    relaxFn_promiseBatchActionAddKeyWithFunctionCall _, relaxFn_promiseBatchActionDeleteKey _,
    relaxFn_promiseBatchActionDeleteAccount _, relaxFn_promiseResultsCount _, relaxFn_promiseResult _,
    relaxFn_promiseReturn _, relaxFn_storageWrite _, relaxFn_storageRead _, relaxFn_storageRemove _,
    relaxFn_storageHasKey _, relaxFn_validatorStake _, relaxFn_validatorTotalStake _]

/-- Every host function of the instantiated store respects raised limits. -/
theorem storeRelaxFns_wStore (cfg : RuntimeConfig) (h : NearState) : StoreRelaxFns (wStore cfg h) := by
  intro a fn hfn
  have hm := Array.mem_of_getElem? hfn
  simp only [wStore, Array.mem_append, List.mem_toArray, List.mem_map] at hm
  rcases hm with ⟨f, hf, heq⟩ | ⟨g, -, heq⟩
  · cases heq
    exact wHosts_relax cfg f hf
  · cases heq

theorem panicUtf8Metered_keep : ∀ (st : HostStore NearState) (args : List Value) vals st2,
    panicUtf8Metered.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt := by
  intro st args vals st2 h
  simp only [panicUtf8Metered] at h
  split at h
  · split at h <;> simp [trapWith] at h
  · simp [trapWith] at h

/-- Every host `contract.wasm` links respects raised limits, with logs. -/
theorem wHosts_relaxL (cfg : RuntimeConfig) : ∀ fn ∈ wHosts cfg, RelaxFnL fn.toHostFn := by
  intro fn h
  simp only [wHosts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact relaxFnL_metered _ (by simp [gasNames]) readRegisterFn (invokeRelaxL_plain _ _ readRegisterFn (by decide) readRegisterFn_relax readRegisterFn_keep readRegisterFn_mono) readRegisterFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) registerLenFn (invokeRelaxL_plain _ _ registerLenFn (by decide) registerLenFn_relax registerLenFn_keep registerLenFn_mono) registerLenFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) currentAccountIdFn (invokeRelaxL_plain _ _ currentAccountIdFn (by decide) currentAccountIdFn_relax currentAccountIdFn_keep currentAccountIdFn_mono) currentAccountIdFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) signerAccountIdFn (invokeRelaxL_plain _ _ signerAccountIdFn (by decide) signerAccountIdFn_relax signerAccountIdFn_keep signerAccountIdFn_mono) signerAccountIdFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) signerAccountPkFn (invokeRelaxL_plain _ _ signerAccountPkFn (by decide) signerAccountPkFn_relax signerAccountPkFn_keep signerAccountPkFn_mono) signerAccountPkFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) predecessorAccountIdFn (invokeRelaxL_plain _ _ predecessorAccountIdFn (by decide) predecessorAccountIdFn_relax predecessorAccountIdFn_keep predecessorAccountIdFn_mono) predecessorAccountIdFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) inputFn (invokeRelaxL_plain _ _ inputFn (by decide) inputFn_relax inputFn_keep inputFn_mono) inputFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) blockIndexFn (invokeRelaxL_plain _ _ blockIndexFn (by decide) blockIndexFn_relax blockIndexFn_keep blockIndexFn_mono) blockIndexFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) blockTimestampFn (invokeRelaxL_plain _ _ blockTimestampFn (by decide) blockTimestampFn_relax blockTimestampFn_keep blockTimestampFn_mono) blockTimestampFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) epochHeightFn (invokeRelaxL_plain _ _ epochHeightFn (by decide) epochHeightFn_relax epochHeightFn_keep epochHeightFn_mono) epochHeightFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) storageUsageFn (invokeRelaxL_plain _ _ storageUsageFn (by decide) storageUsageFn_relax storageUsageFn_keep storageUsageFn_mono) storageUsageFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) accountBalanceFn (invokeRelaxL_plain _ _ accountBalanceFn (by decide) accountBalanceFn_relax accountBalanceFn_keep accountBalanceFn_mono) accountBalanceFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) accountLockedBalanceFn (invokeRelaxL_plain _ _ accountLockedBalanceFn (by decide) accountLockedBalanceFn_relax accountLockedBalanceFn_keep accountLockedBalanceFn_mono) accountLockedBalanceFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) attachedDepositFn (invokeRelaxL_plain _ _ attachedDepositFn (by decide) attachedDepositFn_relax attachedDepositFn_keep attachedDepositFn_mono) attachedDepositFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) prepaidGasFn (invokeRelaxL_plain _ _ prepaidGasFn (by decide) prepaidGasFn_relax prepaidGasFn_keep prepaidGasFn_mono) prepaidGasFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) usedGasFn (invokeRelaxL_plain _ _ usedGasFn (by decide) usedGasFn_relax usedGasFn_keep usedGasFn_mono) usedGasFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) randomSeedFn (invokeRelaxL_plain _ _ randomSeedFn (by decide) randomSeedFn_relax randomSeedFn_keep randomSeedFn_mono) randomSeedFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) sha256Fn (invokeRelaxL_plain _ _ sha256Fn (by decide) sha256Fn_relax sha256Fn_keep sha256Fn_mono) sha256Fn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) keccak256Fn (invokeRelaxL_plain _ _ keccak256Fn (by decide) keccak256Fn_relax keccak256Fn_keep keccak256Fn_mono) keccak256Fn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) keccak512Fn (invokeRelaxL_plain _ _ keccak512Fn (by decide) keccak512Fn_relax keccak512Fn_keep keccak512Fn_mono) keccak512Fn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) valueReturnFn (invokeRelaxL_plain _ _ valueReturnFn (by decide) valueReturnFn_relax valueReturnFn_keep valueReturnFn_mono) valueReturnFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) panicMetered (invokeRelaxL_plain _ _ panicMetered (by decide) panicMetered_relax (fun st args vals st2 h => by simp [panicMetered, trapWith] at h) panicMetered_mono) panicMetered_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) panicUtf8Metered (invokeRelaxL_plain _ _ panicUtf8Metered (by decide) panicUtf8Metered_relax panicUtf8Metered_keep panicUtf8Metered_mono) panicUtf8Metered_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) logUtf8Fn (invokeRelaxL_plain _ _ logUtf8Fn (by decide) logUtf8Fn_relax logUtf8Fn_keep logUtf8Fn_mono) logUtf8Fn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) logUtf16Fn (invokeRelaxL_plain _ _ logUtf16Fn (by decide) logUtf16Fn_relax logUtf16Fn_keep logUtf16Fn_mono) logUtf16Fn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseCreateFn (invokeRelaxL_plain _ _ promiseCreateFn (by decide) promiseCreateFn_relax promiseCreateFn_keep promiseCreateFn_mono) promiseCreateFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseThenFn (invokeRelaxL_plain _ _ promiseThenFn (by decide) promiseThenFn_relax promiseThenFn_keep promiseThenFn_mono) promiseThenFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseAndFn (invokeRelaxL_plain _ _ promiseAndFn (by decide) promiseAndFn_relax promiseAndFn_keep promiseAndFn_mono) promiseAndFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchCreateFn (invokeRelaxL_plain _ _ promiseBatchCreateFn (by decide) promiseBatchCreateFn_relax promiseBatchCreateFn_keep promiseBatchCreateFn_mono) promiseBatchCreateFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchThenFn (invokeRelaxL_plain _ _ promiseBatchThenFn (by decide) promiseBatchThenFn_relax promiseBatchThenFn_keep promiseBatchThenFn_mono) promiseBatchThenFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionCreateAccountFn (invokeRelaxL_plain _ _ promiseBatchActionCreateAccountFn (by decide) promiseBatchActionCreateAccountFn_relax promiseBatchActionCreateAccountFn_keep promiseBatchActionCreateAccountFn_mono) promiseBatchActionCreateAccountFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionDeployContractFn (invokeRelaxL_plain _ _ promiseBatchActionDeployContractFn (by decide) promiseBatchActionDeployContractFn_relax promiseBatchActionDeployContractFn_keep promiseBatchActionDeployContractFn_mono) promiseBatchActionDeployContractFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionFunctionCallFn (invokeRelaxL_plain _ _ promiseBatchActionFunctionCallFn (by decide) promiseBatchActionFunctionCallFn_relax promiseBatchActionFunctionCallFn_keep promiseBatchActionFunctionCallFn_mono) promiseBatchActionFunctionCallFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionTransferFn (invokeRelaxL_plain _ _ promiseBatchActionTransferFn (by decide) promiseBatchActionTransferFn_relax promiseBatchActionTransferFn_keep promiseBatchActionTransferFn_mono) promiseBatchActionTransferFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionStakeFn (invokeRelaxL_plain _ _ promiseBatchActionStakeFn (by decide) promiseBatchActionStakeFn_relax promiseBatchActionStakeFn_keep promiseBatchActionStakeFn_mono) promiseBatchActionStakeFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionAddKeyWithFullAccessFn (invokeRelaxL_plain _ _ promiseBatchActionAddKeyWithFullAccessFn (by decide) promiseBatchActionAddKeyWithFullAccessFn_relax promiseBatchActionAddKeyWithFullAccessFn_keep promiseBatchActionAddKeyWithFullAccessFn_mono) promiseBatchActionAddKeyWithFullAccessFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionAddKeyWithFunctionCallFn (invokeRelaxL_plain _ _ promiseBatchActionAddKeyWithFunctionCallFn (by decide) promiseBatchActionAddKeyWithFunctionCallFn_relax promiseBatchActionAddKeyWithFunctionCallFn_keep promiseBatchActionAddKeyWithFunctionCallFn_mono) promiseBatchActionAddKeyWithFunctionCallFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionDeleteKeyFn (invokeRelaxL_plain _ _ promiseBatchActionDeleteKeyFn (by decide) promiseBatchActionDeleteKeyFn_relax promiseBatchActionDeleteKeyFn_keep promiseBatchActionDeleteKeyFn_mono) promiseBatchActionDeleteKeyFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseBatchActionDeleteAccountFn (invokeRelaxL_plain _ _ promiseBatchActionDeleteAccountFn (by decide) promiseBatchActionDeleteAccountFn_relax promiseBatchActionDeleteAccountFn_keep promiseBatchActionDeleteAccountFn_mono) promiseBatchActionDeleteAccountFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseResultsCountFn (invokeRelaxL_plain _ _ promiseResultsCountFn (by decide) promiseResultsCountFn_relax promiseResultsCountFn_keep promiseResultsCountFn_mono) promiseResultsCountFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseResultFn (invokeRelaxL_plain _ _ promiseResultFn (by decide) promiseResultFn_relax promiseResultFn_keep promiseResultFn_mono) promiseResultFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) promiseReturnFn (invokeRelaxL_plain _ _ promiseReturnFn (by decide) promiseReturnFn_relax promiseReturnFn_keep promiseReturnFn_mono) promiseReturnFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) storageWriteFn (invokeRelaxL_storage _ _ storageWriteFn storageWriteFn_relax storageWriteFn_keep storageWriteFn_mono) storageWriteFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) storageReadFn (invokeRelaxL_storage _ _ storageReadFn storageReadFn_relax storageReadFn_keep storageReadFn_mono) storageReadFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) storageRemoveFn (invokeRelaxL_storage _ _ storageRemoveFn storageRemoveFn_relax storageRemoveFn_keep storageRemoveFn_mono) storageRemoveFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) storageHasKeyFn (invokeRelaxL_storage _ _ storageHasKeyFn storageHasKeyFn_relax storageHasKeyFn_keep storageHasKeyFn_mono) storageHasKeyFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) validatorStakeFn (invokeRelaxL_plain _ _ validatorStakeFn (by decide) validatorStakeFn_relax validatorStakeFn_keep validatorStakeFn_mono) validatorStakeFn_mono
  · exact relaxFnL_metered _ (by simp [gasNames]) validatorTotalStakeFn (invokeRelaxL_plain _ _ validatorTotalStakeFn (by decide) validatorTotalStakeFn_relax validatorTotalStakeFn_keep validatorTotalStakeFn_mono) validatorTotalStakeFn_mono

theorem storeRelaxFnsL_wStore (cfg : RuntimeConfig) (h : NearState) : StoreRelaxFnsL (wStore cfg h) := by
  intro a fn hfn
  have hm := Array.mem_of_getElem? hfn
  simp only [wStore, Array.mem_append, List.mem_toArray, List.mem_map] at hm
  rcases hm with ⟨f, hf, heq⟩ | ⟨g, -, heq⟩
  · cases heq
    exact wHosts_relaxL cfg f hf
  · cases heq

/-- Every host `contract.wasm` links only grows the logs, and keeps the execution issue when it returns. -/
theorem wHosts_mono (cfg : RuntimeConfig) : ∀ fn ∈ wHosts cfg, FnMono fn := by
  intro fn h
  simp only [wHosts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [
    metered_mono _ _ _ readRegisterFn_mono, metered_mono _ _ _ registerLenFn_mono, metered_mono _ _ _
    currentAccountIdFn_mono, metered_mono _ _ _ signerAccountIdFn_mono, metered_mono _ _ _
    signerAccountPkFn_mono, metered_mono _ _ _ predecessorAccountIdFn_mono, metered_mono _ _ _
    inputFn_mono, metered_mono _ _ _ blockIndexFn_mono, metered_mono _ _ _ blockTimestampFn_mono,
    metered_mono _ _ _ epochHeightFn_mono, metered_mono _ _ _ storageUsageFn_mono, metered_mono _ _ _
    accountBalanceFn_mono, metered_mono _ _ _ accountLockedBalanceFn_mono, metered_mono _ _ _
    attachedDepositFn_mono, metered_mono _ _ _ prepaidGasFn_mono, metered_mono _ _ _ usedGasFn_mono,
    metered_mono _ _ _ randomSeedFn_mono, metered_mono _ _ _ sha256Fn_mono, metered_mono _ _ _
    keccak256Fn_mono, metered_mono _ _ _ keccak512Fn_mono, metered_mono _ _ _ valueReturnFn_mono,
    metered_mono _ _ _ panicMetered_mono, metered_mono _ _ _ panicUtf8Metered_mono, metered_mono _ _ _
    logUtf8Fn_mono, metered_mono _ _ _ logUtf16Fn_mono, metered_mono _ _ _ promiseCreateFn_mono,
    metered_mono _ _ _ promiseThenFn_mono, metered_mono _ _ _ promiseAndFn_mono, metered_mono _ _ _
    promiseBatchCreateFn_mono, metered_mono _ _ _ promiseBatchThenFn_mono, metered_mono _ _ _
    promiseBatchActionCreateAccountFn_mono, metered_mono _ _ _ promiseBatchActionDeployContractFn_mono,
    metered_mono _ _ _ promiseBatchActionFunctionCallFn_mono, metered_mono _ _ _
    promiseBatchActionTransferFn_mono, metered_mono _ _ _ promiseBatchActionStakeFn_mono, metered_mono
    _ _ _ promiseBatchActionAddKeyWithFullAccessFn_mono, metered_mono _ _ _
    promiseBatchActionAddKeyWithFunctionCallFn_mono, metered_mono _ _ _
    promiseBatchActionDeleteKeyFn_mono, metered_mono _ _ _ promiseBatchActionDeleteAccountFn_mono,
    metered_mono _ _ _ promiseResultsCountFn_mono, metered_mono _ _ _ promiseResultFn_mono,
    metered_mono _ _ _ promiseReturnFn_mono, metered_mono _ _ _ storageWriteFn_mono, metered_mono _ _ _
    storageReadFn_mono, metered_mono _ _ _ storageRemoveFn_mono, metered_mono _ _ _
    storageHasKeyFn_mono, metered_mono _ _ _ validatorStakeFn_mono, metered_mono _ _ _
    validatorTotalStakeFn_mono]

theorem wStore_host {cfg : RuntimeConfig} {h : NearState} {fn : HostFn NearState}
    (hm : FuncInst.host fn ∈ (wStore cfg h).funcs) : ∃ f ∈ wHosts cfg, f.toHostFn = fn := by
  simp only [wStore, Array.mem_append, List.mem_toArray, List.mem_map] at hm
  rcases hm with ⟨f, hf, heq⟩ | ⟨g, -, heq⟩
  · cases heq; exact ⟨f, hf, rfl⟩
  · cases heq

theorem storeLogsMono_wStore (cfg : RuntimeConfig) (h : NearState) : StoreLogsMono (wStore cfg h) := by
  intro fn hm L
  obtain ⟨f, hf, rfl⟩ := wStore_host hm
  exact fnMono_logs (wHosts_mono cfg f hf) L

theorem storeLive_wStore (cfg : RuntimeConfig) (h : NearState) (I : Option ExecutionIssue) :
    Exec.StoreHosts (Exec.HostFn.PreservesLive (fun x => x.lastExecutionIssue = I)) (wStore cfg h) := by
  intro fn hm
  obtain ⟨f, hf, rfl⟩ := wStore_host hm
  exact fnMono_live (wHosts_mono cfg f hf) I

end WNear.Binary
