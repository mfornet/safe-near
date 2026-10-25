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
  | .addKey pk _ (.gasKeyFullAccess nonces) =>
    fees.addFullAccessKey.execution +
      (fees.gasKeyNonceWriteBase.execution * nonces +
        fees.gasKeyByte.execution * (accessKeyKeyLen receiver.length (gasKeyPublicKeyLen pk) + 2 + 8) * nonces)
  | .addKey pk _ (.gasKeyFunctionCall nonces _ _ methods) =>
    fees.addFunctionCallKeyBase.execution + fees.addFunctionCallKeyByte.execution * methodNamesGasBytes methods +
      (fees.gasKeyNonceWriteBase.execution * nonces +
        fees.gasKeyByte.execution * (accessKeyKeyLen receiver.length (gasKeyPublicKeyLen pk) + 2 + 8) * nonces)
  | .deleteKey _ => fees.deleteKey.execution
  | .deleteAccount _ => fees.deleteAccount.execution
  | .useGlobalContract id =>
    fees.useGlobalContractBase.execution + fees.useGlobalContractByte.execution * id.length
  | .deployGlobalContract code _ =>
    fees.deployGlobalContractBase.execution + fees.deployGlobalContractByte.execution * code.length
  | .transferToGasKey pk _ =>
    fees.gasKeyTransferBase.execution +
      fees.gasKeyByte.execution * (accessKeyKeyLen receiver.length (gasKeyPublicKeyLen pk) + minGasKeyBorshLen)

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
theorem appendPromiseAction_gas (fees : ActionFees) (ethEnabled : Bool) (st : HostStore NearState)
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
    | yielded account actions dataId =>
      have hs : setPromise? st.host.promises index (.yielded account (actions ++ [action]) dataId) = some result := by
        simpa only [hg] using h
      have hv := setPromise_value (receiptGasValue fees ethEnabled) st.host.promises result index
        (.yielded account actions dataId) (.yielded account (actions ++ [action]) dataId) hg hs
      simp only [promiseValue, receiptGasValue_append] at hv
      simp only [promisesGas, promiseReceiver?, hg, Option.getD_some]
      omega

theorem appendPromise_gas (fees : ActionFees) (ethEnabled : Bool) (st : HostStore NearState) (promise : NearPromise) :
    promisesGas fees ethEnabled (appendPromise st promise).host.promises =
      promisesGas fees ethEnabled st.host.promises + promiseValue (receiptGasValue fees ethEnabled) promise := by
  simp [appendPromise, promisesGas, promisesValue]

/-- Conversion preserves gas once per actual receipt, including duplicate and
nested joins. No graph-validity or unique-dependency premise is required. -/
theorem convertPromises_gas (fees : ActionFees) (ethEnabled : Bool) (promises : List NearPromise) (graph : PromiseGraph)
    (h : convertPromises promises = some graph) : receiptsGas fees ethEnabled graph.receipts = promisesGas fees ethEnabled promises :=
  convertPromises_value promises graph h (receiptGasValue fees ethEnabled)

theorem actionExecutionGas_addGas (fees : ActionFees) (ethEnabled : Bool) (receiver : List UInt8)
    {g : Nat} {a a' : PromiseAction} (h : a.addGas? g = some a') :
    actionExecutionGas fees ethEnabled receiver a' = actionExecutionGas fees ethEnabled receiver a + g := by
  cases a with
  | functionCall method args amount gas =>
    simp only [PromiseAction.addGas?] at h
    split at h
    · rename_i hlt
      cases h
      simp only [actionExecutionGas, UInt64.toNat_ofNat_of_lt' hlt]
      omega
    · cases h
  | _ => simp [PromiseAction.addGas?] at h

theorem applyGasShare_gas (fees : ActionFees) (ethEnabled : Bool) (receipts : List ReceiptSpec)
    (receipt action g : Nat) :
    receiptsGas fees ethEnabled (applyGasShare receipts receipt action g).1 =
      receiptsGas fees ethEnabled receipts + (applyGasShare receipts receipt action g).2 := by
  unfold applyGasShare
  split
  · rename_i spec hspec
    split
    · rename_i a ha
      split
      · rename_i a' hadd
        have hr := map_sum_set (fun r : ReceiptSpec => receiptGasValue fees ethEnabled r.receiverId r.actions)
          receipts receipt spec { spec with actions := spec.actions.set action a' } hspec
        have ha' := map_sum_set (actionExecutionGas fees ethEnabled spec.receiverId) spec.actions action a a' ha
        rw [actionExecutionGas_addGas fees ethEnabled spec.receiverId hadd] at ha'
        simp only [receiptsGas, receiptsValue, receiptGasValue] at hr ⊢
        omega
      · rfl
    · rfl
  · rfl

theorem distributeStep_gas (fees : ActionFees) (ethEnabled : Bool)
    (unused total : Nat) (weights : List (Nat × Nat × Nat)) (handles : List PromiseHandle)
    (acc : List ReceiptSpec × Nat) (entry : (Nat × Nat × Nat) × Nat) :
    receiptsGas fees ethEnabled (distributeStep unused total weights handles acc entry).1 + acc.2 =
      receiptsGas fees ethEnabled acc.1 + (distributeStep unused total weights handles acc entry).2 := by
  unfold distributeStep
  split
  · rename_i receipt _
    have := applyGasShare_gas fees ethEnabled acc.1 receipt entry.1.2.1
      (gasShare unused total weights entry.2 entry.1.2.2)
    dsimp only
    omega
  · rfl

theorem foldl_distributeStep_gas (fees : ActionFees) (ethEnabled : Bool)
    (unused total : Nat) (weights : List (Nat × Nat × Nat)) (handles : List PromiseHandle)
    (entries : List ((Nat × Nat × Nat) × Nat)) (acc : List ReceiptSpec × Nat) :
    receiptsGas fees ethEnabled (entries.foldl (distributeStep unused total weights handles) acc).1 + acc.2 =
      receiptsGas fees ethEnabled acc.1 + (entries.foldl (distributeStep unused total weights handles) acc).2 := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.foldl_cons]
    have h1 := ih (distributeStep unused total weights handles acc entry)
    have h2 := distributeStep_gas fees ethEnabled unused total weights handles acc entry
    omega

/-- Distribution adds to the receipts exactly the gas it reports. -/
theorem distributeGas_gas (fees : ActionFees) (ethEnabled : Bool) (unused : Nat)
    (handles : List PromiseHandle) (weights : List (Nat × Nat × Nat)) (receipts : List ReceiptSpec) :
    receiptsGas fees ethEnabled (distributeGas unused handles weights receipts).1 =
      receiptsGas fees ethEnabled receipts + (distributeGas unused handles weights receipts).2 := by
  unfold distributeGas
  dsimp only
  split
  · rfl
  · have := foldl_distributeStep_gas fees ethEnabled unused (gasWeightTotal weights) weights handles
      weights.zipIdx (receipts, 0)
    simpa using this

/-- Packing a successful executable result exposes its exact onward gas budget.
Establishing GasBacked from concrete host execution remains a separate obligation. -/
theorem outcomeOfExecution_success_gas_backing (fees : ActionFees) (ethEnabled : Bool)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (final : Machine)
    (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (hbacked : GasBacked fees ethEnabled final.host) :
    (outcomeOfExecution ctx storage final error).usedGas =
      (outcomeOfExecution ctx storage final error).burntGas +
        receiptsGas fees ethEnabled (outcomeOfExecution ctx storage final error).receipts := by
  unfold outcomeOfExecution at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · contradiction
  · cases hc : convertPromises final.host.promises with
    | none => simp [hc, VMOutcome.graphIssue] at hsuccess
    | some graph =>
      simp only [hc] at hsuccess ⊢
      split at hsuccess
      · simp [VMOutcome.graphIssue] at hsuccess
      · dsimp only
        rw [distributeGas_gas, convertPromises_gas fees ethEnabled _ graph hc]
        have hu : final.host.gas.used = final.host.gas.burnt + final.host.gas.promises := rfl
        unfold GasBacked at hbacked
        omega

end Wasm.Near
