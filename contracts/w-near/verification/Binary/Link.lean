import Binary.Valid
import NearVM.Metered

/-!
# What `contract.wasm` links to

`resolve_wPrepared`: the 48 imports of `contract.wasm` resolve, in order,
to the metered host functions `wHosts` lists. `panic` and `panic_utf8` are
nearcore's structured panics.
-/

namespace WNear.Binary

open Wasm Wasm.Near

/-- The metered host functions of the imports, in import order (function
indices 0 to 47). -/
def wHosts (cfg : RuntimeConfig) : List (NearHostFn NearState) :=
  let e := cfg.fees.numExtraBytesRecord
  [ metered e "read_register" readRegisterFn, metered e "register_len" registerLenFn
  , metered e "current_account_id" currentAccountIdFn, metered e "signer_account_id" signerAccountIdFn
  , metered e "signer_account_pk" signerAccountPkFn
  , metered e "predecessor_account_id" predecessorAccountIdFn, metered e "input" inputFn
  , metered e "block_index" blockIndexFn, metered e "block_timestamp" blockTimestampFn
  , metered e "epoch_height" epochHeightFn, metered e "storage_usage" storageUsageFn
  , metered e "account_balance" accountBalanceFn
  , metered e "account_locked_balance" accountLockedBalanceFn
  , metered e "attached_deposit" attachedDepositFn, metered e "prepaid_gas" prepaidGasFn
  , metered e "used_gas" usedGasFn, metered e "random_seed" randomSeedFn
  , metered e "sha256" sha256Fn, metered e "keccak256" keccak256Fn, metered e "keccak512" keccak512Fn
  , metered e "value_return" valueReturnFn, metered e "panic" panicMetered
  , metered e "panic_utf8" panicUtf8Metered, metered e "log_utf8" logUtf8Fn
  , metered e "log_utf16" logUtf16Fn, metered e "promise_create" promiseCreateFn
  , metered e "promise_then" promiseThenFn, metered e "promise_and" promiseAndFn
  , metered e "promise_batch_create" promiseBatchCreateFn
  , metered e "promise_batch_then" promiseBatchThenFn
  , metered e "promise_batch_action_create_account" promiseBatchActionCreateAccountFn
  , metered e "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn
  , metered e "promise_batch_action_function_call" promiseBatchActionFunctionCallFn
  , metered e "promise_batch_action_transfer" promiseBatchActionTransferFn
  , metered e "promise_batch_action_stake" promiseBatchActionStakeFn
  , metered e "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn
  , metered e "promise_batch_action_add_key_with_function_call"
      promiseBatchActionAddKeyWithFunctionCallFn
  , metered e "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn
  , metered e "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn
  , metered e "promise_results_count" promiseResultsCountFn
  , metered e "promise_result" promiseResultFn, metered e "promise_return" promiseReturnFn
  , metered e "storage_write" storageWriteFn, metered e "storage_read" storageReadFn
  , metered e "storage_remove" storageRemoveFn, metered e "storage_has_key" storageHasKeyFn
  , metered e "validator_stake" validatorStakeFn
  , metered e "validator_total_stake" validatorTotalStakeFn ]

set_option maxRecDepth 100000 in
theorem resolve_wPrepared (cfg : RuntimeConfig) :
    resolveMetered cfg wPrepared = .ok { funcs := wHosts cfg } := by
  rfl

end WNear.Binary
