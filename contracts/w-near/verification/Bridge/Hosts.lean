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

end WNear.Binary
