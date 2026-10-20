import NearVM.PromiseAccounting
import NearVM.ChargeReservations

namespace Wasm.Near

/-- Execution/prepaid obligation of an action as created by the VM ABI. -/
def actionExecutionGas (fees : ActionFees) (ethEnabled : Bool) (receiver : List UInt8) : PromiseAction → Nat
  | .createAccount => fees.createAccount.execution
  | .deployContract bytes => fees.deployContractBase.execution + fees.deployContractByte.execution * bytes.length
  | .functionCall method args _ gas =>
    fees.functionCallBase.execution + fees.functionCallByte.execution * (method.length + args.length) + gas.toNat
  | .transfer _ => (transferFees fees ethEnabled receiver).execution
  | .stake .. => fees.stake.execution
  | .addKey _ _ .fullAccess => fees.addFullAccessKey.execution
  | .addKey _ _ (.functionCall _ _ methods) =>
    fees.addFunctionCallKeyBase.execution + fees.addFunctionCallKeyByte.execution * methodNamesGasBytes methods
  | .deleteKey _ => fees.deleteKey.execution
  | .deleteAccount _ => fees.deleteAccount.execution

def receiptGasValue (fees : ActionFees) (ethEnabled : Bool) : ReceiptValuation := fun receiver actions =>
  fees.newActionReceipt.execution + (actions.map (actionExecutionGas fees ethEnabled receiver)).sum

def promisesGas (fees : ActionFees) (ethEnabled : Bool) (promises : List NearPromise) : Nat :=
  promisesValue (receiptGasValue fees ethEnabled) promises

def receiptsGas (fees : ActionFees) (ethEnabled : Bool) (receipts : List ReceiptSpec) : Nat :=
  receiptsValue (receiptGasValue fees ethEnabled) receipts

/-- The counter's onward gas has exactly one corresponding raw obligation. -/
def GasBacked (fees : ActionFees) (ethEnabled : Bool) (ns : NearState) : Prop :=
  ns.gas.promises = promisesGas fees ethEnabled ns.promises

@[simp] theorem receiptGasValue_append (fees : ActionFees) (ethEnabled : Bool) (receiver : List UInt8)
    (actions : List PromiseAction) (action : PromiseAction) :
    receiptGasValue fees ethEnabled receiver (actions ++ [action]) =
      receiptGasValue fees ethEnabled receiver actions + actionExecutionGas fees ethEnabled receiver action := by
  simp [receiptGasValue, List.map_append, Nat.add_assoc]

/-- Extending a receipt adds its action obligation without duplicating the
receipt base fee; callback dependency handles do not change its gas backing. -/
theorem appendPromiseAction_gas (fees : ActionFees) (ethEnabled : Bool) (st : Store NearState)
    (result : List NearPromise) (index : Nat) (action : PromiseAction)
    (h : appendPromiseAction? st.host.promises index action = some result) :
    promisesGas fees ethEnabled result = promisesGas fees ethEnabled st.host.promises +
      actionExecutionGas fees ethEnabled ((promiseReceiver? st index).getD []) action := by
  unfold appendPromiseAction? at h
  cases hg : getPromise? st.host.promises index with
  | none => simp [hg] at h
  | some promise =>
    cases promise with
    | batch account actions =>
      have hs : setPromise? st.host.promises index (.batch account (actions ++ [action])) = some result := by
        simpa only [hg] using h
      have hv := setPromise_value (receiptGasValue fees ethEnabled) st.host.promises result index
        (.batch account actions) (.batch account (actions ++ [action])) hg hs
      simp only [promiseValue, receiptGasValue_append] at hv
      simp only [promisesGas, promiseReceiver?, hg, Option.getD_some]
      omega
    | callback base account actions =>
      have hs : setPromise? st.host.promises index (.callback base account (actions ++ [action])) = some result := by
        simpa only [hg] using h
      have hv := setPromise_value (receiptGasValue fees ethEnabled) st.host.promises result index
        (.callback base account actions) (.callback base account (actions ++ [action])) hg hs
      simp only [promiseValue, receiptGasValue_append] at hv
      simp only [promisesGas, promiseReceiver?, hg, Option.getD_some]
      omega
    | and dependencies => simp [hg] at h
    | yielded => simp [hg] at h

theorem appendPromise_gas (fees : ActionFees) (ethEnabled : Bool) (st : Store NearState) (promise : NearPromise) :
    promisesGas fees ethEnabled (appendPromise st promise).host.promises =
      promisesGas fees ethEnabled st.host.promises + promiseValue (receiptGasValue fees ethEnabled) promise := by
  simp [appendPromise, promisesGas, promisesValue]

/-- Conversion preserves gas once per actual receipt, including duplicate and
nested joins. No graph-validity or unique-dependency premise is required. -/
theorem convertPromises_gas (fees : ActionFees) (ethEnabled : Bool) (promises : List NearPromise) (graph : PromiseGraph)
    (h : convertPromises promises = some graph) : receiptsGas fees ethEnabled graph.receipts = promisesGas fees ethEnabled promises :=
  convertPromises_value promises graph h (receiptGasValue fees ethEnabled)

/-- Packing a successful executable result exposes its exact onward gas budget.
Establishing GasBacked from concrete host execution remains a separate obligation. -/
theorem outcomeOfExecution_success_gas_backing (fees : ActionFees) (ethEnabled : Bool)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (final : SmallStep.Config NearState)
    (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (hbacked : GasBacked fees ethEnabled final.store.wasm.host) :
    (outcomeOfExecution ctx storage final error).usedGas =
      (outcomeOfExecution ctx storage final error).burntGas +
        receiptsGas fees ethEnabled (outcomeOfExecution ctx storage final error).receipts := by
  unfold outcomeOfExecution at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · contradiction
  · cases hc : convertPromises final.store.wasm.host.promises with
    | none => simp [hc, VMOutcome.graphIssue] at hsuccess
    | some graph =>
      simp only [hc] at hsuccess ⊢
      split at hsuccess
      · simp [VMOutcome.graphIssue] at hsuccess
      · rw [convertPromises_gas fees ethEnabled _ graph hc]
        exact congrArg (final.store.wasm.host.gas.burnt + ·) hbacked

end Wasm.Near
