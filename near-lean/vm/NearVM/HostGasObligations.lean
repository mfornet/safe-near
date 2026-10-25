import NearVM.PromiseGas
import NearVM.FunctionKeyValidation

namespace Wasm.Near

/-- Decode the action carried by a batch-action ABI invocation. Validation and
charging remain in the host; this parser records the exact bytes and amounts. -/
def batchActionInput? (name : String) (st : HostStore NearState) : List Value → Option (UInt64 × PromiseAction)
  | [.i64 index] =>
    if name == "promise_batch_action_create_account" then some (index, .createAccount) else none
  | [.i64 index, .i64 ptr] => do
    if name != "promise_batch_action_transfer" then none else
      let amount ← readU128Mem st ptr
      some (index, .transfer amount)
  | [.i64 index, .i64 len, .i64 ptr] => do
    let bytes ← getMemOrReg st ptr len
    if name == "promise_batch_action_deploy_contract" then some (index, .deployContract bytes)
    else if name == "promise_batch_action_delete_key" then some (index, .deleteKey bytes)
    else if name == "promise_batch_action_delete_account" then some (index, .deleteAccount bytes)
    else if name == "promise_batch_action_use_global_contract" then
      some (index, .useGlobalContract (.codeHash bytes))
    else if name == "promise_batch_action_use_global_contract_by_account_id" then
      some (index, .useGlobalContract (.accountId bytes))
    else if name == "promise_batch_action_deploy_global_contract" then
      some (index, .deployGlobalContract bytes .codeHash)
    else if name == "promise_batch_action_deploy_global_contract_by_account_id" then
      some (index, .deployGlobalContract bytes .accountId)
    else none
  | [.i64 index, .i64 a, .i64 b, .i64 c] =>
    if name == "promise_batch_action_stake" then do
      let amount ← readU128Mem st a
      let pk ← getMemOrReg st c b
      some (index, .stake amount pk)
    else if name == "promise_batch_action_add_key_with_full_access" then do
      let pk ← getMemOrReg st b a
      some (index, .addKey pk c .fullAccess)
    else if name == "promise_batch_action_add_gas_key_with_full_access" then do
      let pk ← getMemOrReg st b a
      some (index, .addKey pk 0 (.gasKeyFullAccess c.toNat))
    else if name == "promise_batch_action_transfer_to_gas_key" then do
      let pk ← getMemOrReg st b a
      let amount ← readU128Mem st c
      some (index, .transferToGasKey pk amount)
    else none
  | [.i64 index, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] => do
    if name != "promise_batch_action_function_call" then none else
      let action ← readFunctionCallAction? st ml mp al ap amount gas
      some (index, action)
  | [.i64 index, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas, .i64 _weight] => do
    if name != "promise_batch_action_function_call" then none else
      let action ← readFunctionCallAction? st ml mp al ap amount gas
      some (index, action)
  | [.i64 index, .i64 kl, .i64 kp, .i64 nonce, .i64 allowancePtr,
      .i64 rl, .i64 rp, .i64 ml, .i64 mp] => do
    if name != "promise_batch_action_add_key_with_function_call" &&
        name != "promise_batch_action_add_gas_key_with_function_call" then none else
      let pk ← getMemOrReg st kp kl
      let allowance ← readU128Mem st allowancePtr
      let receiver ← getMemOrReg st rp rl
      let methods ← getMemOrReg st mp ml
      if name == "promise_batch_action_add_key_with_function_call" then
        some (index, .addKey pk nonce (.functionCall (functionCallAllowance allowance) receiver methods))
      else
        some (index, .addKey pk 0
          (.gasKeyFunctionCall nonce.toNat (functionCallAllowance allowance) receiver methods))
  | _ => none

/-- The successful raw host creates exactly the action decoded from its ABI.
The gas counter is deliberately absent: the metered wrapper pays this obligation. -/
def HostResultAppendsGas (fees : ActionFees) (ethEnabled : Bool) (name : String)
    (st : HostStore NearState) (args : List Value) : HostResult NearState → Prop
  | .Return _ after => ∃ index action,
      batchActionInput? name st args = some (index, action) ∧
      promisesGas fees ethEnabled after.host.promises = promisesGas fees ethEnabled st.host.promises +
        actionExecutionGas fees ethEnabled ((promiseReceiver? st index.toNat).getD []) action
  | .Trap .. => True

def HostAppendsGas (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ fees ethEnabled st args, HostResultAppendsGas fees ethEnabled name st args (fn.invoke st args)

theorem appendPromiseActionResult_gas_input {weight : UInt64} (fees : ActionFees) (ethEnabled : Bool)
    (name : String) (st : HostStore NearState) (args : List Value) (index : UInt64) (action : PromiseAction)
    (hinput : batchActionInput? name st args = some (index, action)) :
    HostResultAppendsGas fees ethEnabled name st args (appendPromiseActionResult name st index action weight) := by
  unfold appendPromiseActionResult
  split
  · exact ⟨index, action, hinput, appendPromiseAction_gas fees ethEnabled st _ _ _ (by assumption)⟩
  · trivial

theorem promiseBatchActionCreateAccountFn_gasObligation : HostAppendsGas "promise_batch_action_create_account" promiseBatchActionCreateAccountFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionDeployContractFn_gasObligation : HostAppendsGas "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionFunctionCallFn_gasObligation : HostAppendsGas "promise_batch_action_function_call" promiseBatchActionFunctionCallFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionFunctionCallWeightFn_gasObligation : HostAppendsGas "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionFunctionCallWeightFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionTransferFn_gasObligation : HostAppendsGas "promise_batch_action_transfer" promiseBatchActionTransferFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionTransferToGasKeyFn_gasObligation : HostAppendsGas "promise_batch_action_transfer_to_gas_key" promiseBatchActionTransferToGasKeyFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionTransferToGasKeyFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionStakeFn_gasObligation : HostAppendsGas "promise_batch_action_stake" promiseBatchActionStakeFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_gasObligation : HostAppendsGas "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionAddGasKeyWithFullAccessFn_gasObligation : HostAppendsGas "promise_batch_action_add_gas_key_with_full_access" promiseBatchActionAddGasKeyWithFullAccessFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionAddGasKeyWithFullAccessFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_gasObligation : HostAppendsGas "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionAddGasKeyWithFunctionCallFn_gasObligation : HostAppendsGas "promise_batch_action_add_gas_key_with_function_call" promiseBatchActionAddGasKeyWithFunctionCallFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionAddGasKeyWithFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionDeleteKeyFn_gasObligation : HostAppendsGas "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionDeleteAccountFn_gasObligation : HostAppendsGas "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionUseGlobalContractFn_gasObligation : HostAppendsGas "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionDeployGlobalContractFn_gasObligation : HostAppendsGas "promise_batch_action_deploy_global_contract" promiseBatchActionDeployGlobalContractFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionDeployGlobalContractFn deployGlobalContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionUseGlobalContractByAccountIdFn_gasObligation : HostAppendsGas "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

theorem promiseBatchActionDeployGlobalContractByAccountIdFn_gasObligation : HostAppendsGas "promise_batch_action_deploy_global_contract_by_account_id" promiseBatchActionDeployGlobalContractByAccountIdFn := by
  intro fees ethEnabled st args
  unfold promiseBatchActionDeployGlobalContractByAccountIdFn deployGlobalContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat (first
    | trivial
    | (apply appendPromiseActionResult_gas_input; simp_all [batchActionInput?])
    | split)

/-- Receipt-producing ABIs, including joins which create no action receipt. -/
def promiseInput? (name : String) (st : HostStore NearState) : List Value → Option NearPromise
  | [.i64 len, .i64 ptr] =>
    if name == "promise_batch_create" then do
      let account ← getMemOrReg st ptr len
      some (.batch account [])
    else if name == "promise_and" then do
      let deps ← readU64Array st len ptr.toNat
      some (.and deps)
    else none
  | [.i64 base, .i64 len, .i64 ptr] => do
    if name != "promise_batch_then" then none else
      let account ← getMemOrReg st ptr len
      some (.callback base.toNat account [])
  | [.i64 nl, .i64 np, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] => do
    if name != "promise_create" then none else
      let account ← getMemOrReg st np nl
      let action ← readFunctionCallAction? st ml mp al ap amount gas
      some (.batch account [action])
  | [.i64 base, .i64 nl, .i64 np, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] => do
    if name != "promise_then" then none else
      let account ← getMemOrReg st np nl
      let action ← readFunctionCallAction? st ml mp al ap amount gas
      some (.callback base.toNat account [action])
  | _ => none

def HostResultCreatesGas (fees : ActionFees) (ethEnabled : Bool) (name : String)
    (st : HostStore NearState) (args : List Value) : HostResult NearState → Prop
  | .Return _ after => ∃ promise,
      promiseInput? name st args = some promise ∧
      promisesGas fees ethEnabled after.host.promises = promisesGas fees ethEnabled st.host.promises +
        promiseValue (receiptGasValue fees ethEnabled) promise
  | .Trap .. => True

def HostCreatesGas (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ fees ethEnabled st args, HostResultCreatesGas fees ethEnabled name st args (fn.invoke st args)

theorem appendPromise_gas_input (fees : ActionFees) (ethEnabled : Bool)
    (name : String) (st : HostStore NearState) (args values : List Value) (promise : NearPromise)
    (hinput : promiseInput? name st args = some promise) :
    HostResultCreatesGas fees ethEnabled name st args (.Return values (appendPromise st promise)) :=
  ⟨promise, hinput, appendPromise_gas fees ethEnabled st promise⟩

theorem promiseCreateFn_gasObligation : HostCreatesGas "promise_create" promiseCreateFn := by
  intro fees ethEnabled st args
  unfold promiseCreateFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat (first
    | trivial
    | (apply appendPromise_gas_input; simp_all [promiseInput?])
    | split)

theorem promiseThenFn_gasObligation : HostCreatesGas "promise_then" promiseThenFn := by
  intro fees ethEnabled st args
  unfold promiseThenFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat (first
    | trivial
    | (apply appendPromise_gas_input; simp_all [promiseInput?])
    | split)

theorem promiseBatchCreateFn_gasObligation : HostCreatesGas "promise_batch_create" promiseBatchCreateFn := by
  intro fees ethEnabled st args
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat (first
    | trivial
    | (apply appendPromise_gas_input; simp_all [promiseInput?])
    | split)

theorem promiseBatchThenFn_gasObligation : HostCreatesGas "promise_batch_then" promiseBatchThenFn := by
  intro fees ethEnabled st args
  unfold promiseBatchThenFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat (first
    | trivial
    | (apply appendPromise_gas_input; simp_all [promiseInput?])
    | split)

theorem promiseAndFn_gasObligation : HostCreatesGas "promise_and" promiseAndFn := by
  intro fees ethEnabled st args
  unfold promiseAndFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat (first
    | trivial
    | (apply appendPromise_gas_input; simp_all [promiseInput?])
    | split)

end Wasm.Near
