import NearVM.ReceiptPredicates
import NearVM.HostGasObligations
import NearVM.HostPromises
import NearVM.LiveInvariant
import NearVM.MethodEncoding

namespace Wasm.Near

/-- Only decoding facts needed by the raw-to-runtime action gas bridge. -/
def ActionMethodsUtf8 : PromiseAction → Prop
  | .functionCall method .. => (String.fromUTF8? ⟨method.toArray⟩).isSome = true
  | .addKey _ _ (.functionCall _ _ methods) => methodNameFieldsUtf8 methods = true
  | _ => True

instance (action : PromiseAction) : Decidable (ActionMethodsUtf8 action) := by
  cases action with
  | functionCall => exact inferInstanceAs (Decidable (_ = true))
  | addKey pk nonce permission =>
    cases permission with
    | fullAccess => exact isTrue trivial
    | functionCall => exact inferInstanceAs (Decidable (_ = true))
  | _ => exact isTrue trivial

/-- This is encoding validity, not account syntax, authorization or action validity. -/
def ReceiptEncoding (receiver : List UInt8) (actions : List PromiseAction) : Prop :=
  (String.fromUTF8? ⟨receiver.toArray⟩).isSome = true ∧ ∀ action ∈ actions, ActionMethodsUtf8 action

instance : DecidableRel ReceiptEncoding := fun _ _ => inferInstanceAs (Decidable (_ ∧ ∀ a ∈ _, ActionMethodsUtf8 a))

/-- Adding prepaid gas to a function call keeps its method bytes. -/
theorem actionMethodsUtf8_addGas {g : Nat} {a a' : PromiseAction} (h : a.addGas? g = some a') :
    ActionMethodsUtf8 a' ↔ ActionMethodsUtf8 a := by
  cases a with
  | functionCall method args amount gas =>
    simp only [PromiseAction.addGas?] at h
    split at h
    · cases h; rfl
    · cases h
  | _ => simp [PromiseAction.addGas?] at h

theorem forall_mem_set_iff {α : Type} (P : α → Prop) (l : List α) (i : Nat) (x y : α)
    (hx : l[i]? = some x) (hxy : P y ↔ P x) : (∀ z ∈ l.set i y, P z) ↔ ∀ z ∈ l, P z := by
  induction l generalizing i with
  | nil => simp at hx
  | cons head tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp only [List.set_cons_zero, List.forall_mem_cons, hxy]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.set_cons_succ, List.forall_mem_cons, ih i hx]

theorem receiptEncoding_gasInsensitive : PredicateGasInsensitive ReceiptEncoding := by
  intro g receiver actions i a a' ha hadd
  simp only [ReceiptEncoding]
  rw [forall_mem_set_iff ActionMethodsUtf8 actions i a a' ha (actionMethodsUtf8_addGas hadd)]

/-- All raw receipt payloads have byte-preserving runtime decoding. -/
def PromisesEncoding (promises : List NearPromise) : Prop :=
  ∀ promise ∈ promises, PromiseSatisfies ReceiptEncoding promise

private theorem lookup_encoding (promises : List NearPromise) (index : Nat) (promise : NearPromise)
    (h : PromisesEncoding promises) (hget : getPromise? promises index = some promise) :
    PromiseSatisfies ReceiptEncoding promise := by
  rw [getPromise_eq_getElem?] at hget
  exact h promise (List.mem_of_getElem? hget)

/-- A concrete append retains the receiver witness and all earlier action
witnesses. Only the new action requires a new decoding proof. -/
theorem appendPromiseAction_encoding (promises result : List NearPromise) (index : Nat) (action : PromiseAction)
    (h : PromisesEncoding promises) (ha : ActionMethodsUtf8 action)
    (happend : appendPromiseAction? promises index action = some result) : PromisesEncoding result := by
  unfold appendPromiseAction? at happend
  cases hg : getPromise? promises index with
  | none => simp [hg] at happend
  | some promise =>
    have hp := lookup_encoding promises index promise h hg
    cases promise with
    | batch receiver actions =>
      apply setPromise_preserves_predicate ReceiptEncoding promises result index (.batch receiver actions)
        (.batch receiver (actions ++ [action])) hg (by simpa only [hg] using happend) h
      exact ⟨hp.1, by simpa [List.mem_append, List.mem_singleton, or_imp, forall_and] using And.intro hp.2 ha⟩
    | callback base receiver actions =>
      apply setPromise_preserves_predicate ReceiptEncoding promises result index (.callback base receiver actions)
        (.callback base receiver (actions ++ [action])) hg (by simpa only [hg] using happend) h
      exact ⟨hp.1, by simpa [List.mem_append, List.mem_singleton, or_imp, forall_and] using And.intro hp.2 ha⟩
    | and dependencies => simp [hg] at happend
    | yielded => simp [hg] at happend

/-- The raw append host preserves receipt encoding once the appended payload
has passed method validation. Terminal traps have no committed receipt output. -/
theorem appendPromiseActionResult_encoding {weight : UInt64} (name : String) (st : HostStore NearState) (index : UInt64)
    (action : PromiseAction) (h : PromisesEncoding st.host.promises) (ha : ActionMethodsUtf8 action) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (appendPromiseActionResult name st index action weight) := by
  unfold appendPromiseActionResult
  split
  · exact appendPromiseAction_encoding _ _ _ _ h ha (by assumption)
  · trivial

/-- The new action is read from the actual ABI. Method-bearing hosts must
supply its decoding witness from successful metered external validation. -/
def HostPreservesEncoding (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ st args, PromisesEncoding st.host.promises →
    (∀ index action, batchActionInput? name st args = some (index, action) → ActionMethodsUtf8 action) →
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises) (fn.invoke st args)

/-- Close each branch of a batch action host: the appended action encodes its input. -/
local macro "action_input_encoding_tac" h:ident hnew:ident : tactic => `(tactic| (
    dsimp only [disallowInView, checkAccountId, checkPublicKey]
    repeat (first
      | trivial
      | (apply appendPromiseActionResult_encoding _ _ _ _ $h; apply $hnew; simp_all [batchActionInput?])
      | split)))

theorem promiseBatchActionCreateAccountFn_encoding :
    HostPreservesEncoding "promise_batch_action_create_account" promiseBatchActionCreateAccountFn := by
  intro st args h hnew
  unfold promiseBatchActionCreateAccountFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionDeployContractFn_encoding :
    HostPreservesEncoding "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn := by
  intro st args h hnew
  unfold promiseBatchActionDeployContractFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionFunctionCallFn_encoding :
    HostPreservesEncoding "promise_batch_action_function_call" promiseBatchActionFunctionCallFn := by
  intro st args h hnew
  unfold promiseBatchActionFunctionCallFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionFunctionCallWeightFn_encoding :
    HostPreservesEncoding "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn := by
  intro st args h hnew
  unfold promiseBatchActionFunctionCallWeightFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionTransferFn_encoding :
    HostPreservesEncoding "promise_batch_action_transfer" promiseBatchActionTransferFn := by
  intro st args h hnew
  unfold promiseBatchActionTransferFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionStakeFn_encoding :
    HostPreservesEncoding "promise_batch_action_stake" promiseBatchActionStakeFn := by
  intro st args h hnew
  unfold promiseBatchActionStakeFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionAddKeyWithFullAccessFn_encoding :
    HostPreservesEncoding "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args h hnew
  unfold promiseBatchActionAddKeyWithFullAccessFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionAddKeyWithFunctionCallFn_encoding :
    HostPreservesEncoding "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args h hnew
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionDeleteKeyFn_encoding :
    HostPreservesEncoding "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn := by
  intro st args h hnew
  unfold promiseBatchActionDeleteKeyFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionDeleteAccountFn_encoding :
    HostPreservesEncoding "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn := by
  intro st args h hnew
  unfold promiseBatchActionDeleteAccountFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionUseGlobalContractFn_encoding :
    HostPreservesEncoding "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn := by
  intro st args h hnew
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  action_input_encoding_tac h hnew

theorem promiseBatchActionUseGlobalContractByAccountIdFn_encoding :
    HostPreservesEncoding "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn := by
  intro st args h hnew
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  action_input_encoding_tac h hnew

/-- Close each branch of a batch action host: the appended action encodes. -/
local macro "action_encoding_tac" h:ident : tactic => `(tactic| (
    dsimp only [disallowInView, checkAccountId, checkPublicKey]
    repeat (first
      | trivial
      | (apply appendPromiseActionResult_encoding _ _ _ _ $h; trivial)
      | split)))

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionCreateAccountFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionCreateAccountFn.invoke st args) := by
  unfold promiseBatchActionCreateAccountFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionDeployContractFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionDeployContractFn.invoke st args) := by
  unfold promiseBatchActionDeployContractFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionTransferFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionTransferFn.invoke st args) := by
  unfold promiseBatchActionTransferFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionStakeFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionStakeFn.invoke st args) := by
  unfold promiseBatchActionStakeFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionAddKeyWithFullAccessFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionAddKeyWithFullAccessFn.invoke st args) := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionDeleteKeyFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionDeleteKeyFn.invoke st args) := by
  unfold promiseBatchActionDeleteKeyFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionDeleteAccountFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionDeleteAccountFn.invoke st args) := by
  unfold promiseBatchActionDeleteAccountFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionUseGlobalContractFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionUseGlobalContractFn.invoke st args) := by
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  action_encoding_tac h

/-- This action introduces no method-decoding obligation. -/
theorem promiseBatchActionUseGlobalContractByAccountIdFn_preserves_encoding (st : HostStore NearState) (args : List Value)
    (h : PromisesEncoding st.host.promises) :
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises)
      (promiseBatchActionUseGlobalContractByAccountIdFn.invoke st args) := by
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  action_encoding_tac h

end Wasm.Near
