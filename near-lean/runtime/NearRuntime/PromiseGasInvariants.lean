import NearRuntime.FunctionCallInvariants
import NearVM.PromiseGas
import Interpreter.Wasm.ByteEncoding

namespace Near

/-- Receipt execution always uses the real runtime external's UTF-8 policy. -/
theorem functionCallContext_validates_method_utf8 (c : ReceiptCtx) (account : Account)
    (args : Bytes) (gas deposit : Nat) (isLast : Bool) :
    (functionCallContext c account args gas deposit isLast).validateActionMethodUtf8 = true := rfl
open Wasm Wasm.Near Wasm.ByteEncoding

@[simp] theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.utf8ByteSize :=
  string_utf8_length s

@[simp] theorem stringOfBytes_bytesOfString (s : String) : stringOfBytes (bytesOfString s) = s := by
  unfold stringOfBytes bytesOfString
  rw [byteArray_of_toList, string_fromUTF8_toUTF8]
  rfl

/-- Size is fixed by the actual promise payload, independent of decoder metadata. -/
theorem actionOfPromise_deploy_size (decoder : Bytes → ContractCode) (bytes : Bytes) :
    actionOfPromise decoder (.deployContract bytes) =
      .deployContract { decoder bytes with size := bytes.length } := rfl

theorem deployPromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (bytes : Bytes) :
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actionOfPromise decoder (.deployContract bytes)) =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) (.deployContract bytes) := rfl

/-- Byte-preserving UTF-8 method encoding supplies the exact runtime billing
length. No gas or financial equation is assumed. -/
theorem functionCallPromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver method : String) (args : Bytes) (deposit : Nat) (gas : UInt64) :
    let action := actionOfPromise decoder (.functionCall (bytesOfString method) args deposit gas)
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver action + action.attachedGas =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver)
        (.functionCall (bytesOfString method) args deposit gas) := by
  simp [actionOfPromise, Fees.exec, Action.attachedGas, actionExecutionGas]

theorem functionCallPromise_executionGas_of_utf8 (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (method args : Bytes) (decoded : String) (deposit : Nat) (gas : UInt64)
    (hutf8 : String.fromUTF8? (ByteArray.mk method.toArray) = some decoded) :
    let action := actionOfPromise decoder (.functionCall method args deposit gas)
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver action + action.attachedGas =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver)
        (.functionCall method args deposit gas) := by
  have hb := congrArg ByteArray.toList (string_fromUTF8_some_bytes _ decoded hutf8)
  have he : bytesOfString decoded = method := by
    simpa only [bytesOfString, byteArray_toList_ofArray] using hb
  rw [← he]
  exact functionCallPromise_executionGas cfg decoder receiver decoded args deposit gas

/-- Per-field UTF-8 decoding preserves the raw key ABI's exact terminator bill. -/
theorem functionKeyPromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (pk : Bytes) (nonce : UInt64) (allowance : Option Nat)
    (keyReceiver methods : Bytes) (hutf8 : methodNameFieldsUtf8 methods = true) :
    let action := actionOfPromise decoder (.addKey pk nonce (.functionCall allowance keyReceiver methods))
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver action + action.attachedGas =
      actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver)
        (.addKey pk nonce (.functionCall allowance keyReceiver methods)) := by
  simp only [actionOfPromise, Fees.exec, Action.attachedGas, actionExecutionGas, Nat.add_zero]
  rw [decodeMethodNames_billed_length methods hutf8]
  rfl

/-- Encoding facts only: the method bytes can be decoded without fallback. -/
def PromiseActionMethodsUtf8 : PromiseAction → Prop
  | .functionCall method .. => (String.fromUTF8? ⟨method.toArray⟩).isSome = true
  | .addKey _ _ (.functionCall _ _ methods) => methodNameFieldsUtf8 methods = true
  | _ => True

/-- All supported action variants share one gas bridge. The premises concern
actual decoding, rather than assuming a financial/gas equation. -/
theorem promiseAction_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (action : PromiseAction) (h : PromiseActionMethodsUtf8 action) :
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actionOfPromise decoder action) +
      (actionOfPromise decoder action).attachedGas =
        actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) action := by
  cases action with
  | functionCall method args deposit gas =>
    cases he : String.fromUTF8? ⟨method.toArray⟩ with
    | none => simp [PromiseActionMethodsUtf8, he] at h
    | some decoded => exact functionCallPromise_executionGas_of_utf8 cfg decoder receiver method args decoded deposit gas he
  | addKey pk nonce permission =>
    cases permission with
    | fullAccess => rfl
    | functionCall allowance keyReceiver methods =>
      exact functionKeyPromise_executionGas cfg decoder receiver pk nonce allowance keyReceiver methods h
  | _ => rfl

/-- These action variants have no method-list encoding obligation. Deployment
uses actual byte length; transfers share the implicit-account fee calculation. -/
def SimpleGasAction : PromiseAction → Prop
  | .functionCall .. => False
  | .addKey _ _ (.functionCall ..) => False
  | _ => True

theorem simplePromise_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (action : PromiseAction) (h : SimpleGasAction action) :
    Fees.exec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actionOfPromise decoder action) +
      (actionOfPromise decoder action).attachedGas =
        actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) action := by
  cases action <;> try contradiction
  case addKey pk nonce permission =>
    cases permission <;> first | rfl | contradiction
  all_goals rfl

/-- Summing the action bridge retains every execution/prepaid obligation. -/
theorem promiseActions_executionGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (actions : List PromiseAction)
    (h : ∀ action ∈ actions, PromiseActionMethodsUtf8 action) :
    Fees.totalExec cfg.fees.actionFees cfg.wasm.ethImplicitAccounts receiver (actions.map (actionOfPromise decoder)) +
      Fees.totalPrepaid (actions.map (actionOfPromise decoder)) =
        (actions.map (actionExecutionGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver))).sum := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    have ha := promiseAction_executionGas cfg decoder receiver action (h action (by simp))
    have hr := ih (by intro a hm; exact h a (by simp [hm]))
    simp only [Fees.totalExec, Fees.totalPrepaid] at hr
    simp only [Fees.totalExec, Fees.totalPrepaid, List.map_cons, List.sum_cons]
    omega

/-- The runtime receipt budget and raw VM valuation agree, including the one
receipt base, once actual action-method decoding is established. -/
theorem promiseReceipt_gasBudget (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (receiver : AccountId) (actions : List PromiseAction)
    (h : ∀ action ∈ actions, PromiseActionMethodsUtf8 action) :
    Fees.receiptGasBudget cfg receiver (actions.map (actionOfPromise decoder)) =
      receiptGasValue cfg.fees.actionFees cfg.wasm.ethImplicitAccounts (bytesOfString receiver) actions := by
  have he := promiseActions_executionGas cfg decoder receiver actions h
  unfold Fees.receiptGasBudget receiptGasValue
  omega

/-- Encoding facts required for gas valuation; this is not full action validity. -/
def ReceiptGasEncodingValid (spec : ReceiptSpec) : Prop :=
  (String.fromUTF8? ⟨spec.receiverId.toArray⟩).isSome = true ∧
    ∀ action ∈ spec.actions, PromiseActionMethodsUtf8 action

def decodedReceiptGas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode) (spec : ReceiptSpec) : Nat :=
  Fees.receiptGasBudget cfg (stringOfBytes spec.receiverId) (spec.actions.map (actionOfPromise decoder))

/-- Runtime materialization's actual string conversion has the same receipt
budget; the premises are decoding facts, never assumed gas/fund equations. -/
theorem decodedReceiptGas_eq_raw (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (spec : ReceiptSpec) (h : ReceiptGasEncodingValid spec) :
    decodedReceiptGas cfg decoder spec = receiptGasValue cfg.fees.actionFees cfg.wasm.ethImplicitAccounts spec.receiverId spec.actions := by
  cases he : String.fromUTF8? ⟨spec.receiverId.toArray⟩ with
  | none => simp [ReceiptGasEncodingValid, he] at h
  | some receiver =>
    have hb := congrArg ByteArray.toList (string_fromUTF8_some_bytes _ receiver he)
    have hr : bytesOfString receiver = spec.receiverId := by
      simpa only [bytesOfString, byteArray_toList_ofArray] using hb
    have hs : stringOfBytes spec.receiverId = receiver := by simp [stringOfBytes, he]
    unfold decodedReceiptGas
    rw [hs]
    have hg := promiseReceipt_gasBudget cfg decoder receiver spec.actions h.2
    rw [hr] at hg
    exact hg

theorem decodedReceiptsGas_eq_raw (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (specs : List ReceiptSpec) (h : ∀ spec ∈ specs, ReceiptGasEncodingValid spec) :
    (specs.map (decodedReceiptGas cfg decoder)).sum = receiptsGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts specs := by
  unfold receiptsGas receiptsValue
  congr 1
  apply List.map_congr_left
  intro spec hm
  exact decodedReceiptGas_eq_raw cfg decoder spec (h spec hm)

/-- Public VM gas backing transfers to decoded runtime action budgets under
explicit byte-decoding facts. Deriving these facts for every emitted receipt
from the concrete runtime execution remains a separate invariant obligation. -/
theorem run_success_decoded_receipt_gas (cfg : RuntimeConfig) (decoder : Bytes → ContractCode)
    (code : Module) (codeSize : Nat) (method : String) (ctx : VMContext)
    (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hsuccess : (Wasm.Near.run cfg code codeSize method ctx storage fuel).aborted = none)
    (hencoding : ∀ spec ∈ (Wasm.Near.run cfg code codeSize method ctx storage fuel).receipts,
      ReceiptGasEncodingValid spec) :
    (Wasm.Near.run cfg code codeSize method ctx storage fuel).usedGas =
      (Wasm.Near.run cfg code codeSize method ctx storage fuel).burntGas +
        ((Wasm.Near.run cfg code codeSize method ctx storage fuel).receipts.map (decodedReceiptGas cfg decoder)).sum := by
  rw [decodedReceiptsGas_eq_raw cfg decoder _ hencoding]
  exact run_success_gas_backing cfg code codeSize method ctx storage fuel hsuccess

/-- Ordinary contract receipts carry gas funds at their inherited gas price. -/
theorem functionCallGasFunds_eq_decoded (c : ReceiptCtx) (outcome : VMOutcome)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    functionCallGasFunds c outcome =
      (outcome.receipts.map (decodedReceiptGas c.cfg c.codeOf)).sum * c.action.gasPrice := by
  simp only [functionCallGasFunds, beq_eq_false_iff_ne.mpr hreceiver, Bool.false_eq_true, ite_false]
  exact List.sum_map_mul_right (l := outcome.receipts) (f := decodedReceiptGas c.cfg c.codeOf) (r := c.action.gasPrice)

/-- For an actual successful VM call, materialized onward gas funds are exactly
the public counter's reservation, under the explicit encoding conditions. -/
theorem run_functionCallGasFunds (c : ReceiptCtx) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hsuccess : (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).aborted = none)
    (hencoding : ∀ spec ∈ (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).receipts,
      ReceiptGasEncodingValid spec) :
    functionCallGasFunds c (Wasm.Near.run c.cfg code codeSize method ctx storage fuel) =
      ((Wasm.Near.run c.cfg code codeSize method ctx storage fuel).usedGas -
        (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).burntGas) * c.action.gasPrice := by
  rw [functionCallGasFunds_eq_decoded c _ hreceiver, decodedReceiptsGas_eq_raw c.cfg c.codeOf _ hencoding]
  rw [run_success_receipts_gas_eq_reserved c.cfg code codeSize method ctx storage fuel hsuccess]

/-- The real materializer's complete new-receipt funds split into outgoing
deposits and gas reservation purchased at the inherited price. -/
theorem materialize_run_funds (c : ReceiptCtx) (isLast : Bool) (initial : ChainState)
    (code : Module) (codeSize : Nat) (method : String) (ctx : VMContext)
    (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hsuccess : (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).aborted = none)
    (hencoding : ∀ spec ∈ (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).receipts,
      ReceiptGasEncodingValid spec) :
    receiptsFunds c.cfg (materializeFunctionCall c isLast (Wasm.Near.run c.cfg code codeSize method ctx storage fuel) initial).receipts =
      receiptsDeposits (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).receipts +
        ((Wasm.Near.run c.cfg code codeSize method ctx storage fuel).usedGas -
          (Wasm.Near.run c.cfg code codeSize method ctx storage fuel).burntGas) * c.action.gasPrice := by
  rw [materializeFunctionCall_funds_split, run_functionCallGasFunds c code codeSize method ctx storage fuel hreceiver hsuccess hencoding]

end Near
