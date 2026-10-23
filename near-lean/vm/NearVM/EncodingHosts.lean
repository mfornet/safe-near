import NearVM.PolicyEncoding

namespace Wasm.Near

/-- Charging affects neither the strict decoding policy nor raw payloads. -/
theorem applyCharges_encodingFrame (ns : NearState) (charges : List Charge) :
    encodingFrame (applyCharges ns charges).1 = encodingFrame ns := by
  have h := applyCharges_abiFrame ns charges
  exact Prod.ext (congrArg (fun frame => frame.2.1.validateActionMethodUtf8) h)
    (congrArg (fun frame => frame.2.2) h)

theorem deductDeposit_encodingFrame (name : String) (before after : HostStore NearState) (args : List Value) :
    encodingFrame (deductDeposit name before after args).1.host = encodingFrame after.host :=
  Prod.ext (deductDeposit_encodingPolicy name before after args)
    (congrArg (fun view => view.1.2.2) (deductDeposit_reservationView name before after args))

theorem updateStorageUsage_encodingFrame (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) :
    encodingFrame (updateStorageUsage extra name before after args).host = encodingFrame after.host :=
  Prod.ext (updateStorageUsage_encodingPolicy extra name before after args)
    (congrArg (fun view => view.1.2.2) (updateStorageUsage_reservationView extra name before after args))

/-- Post-call accounting preserves encoding on all live results. -/
theorem finishMeteredCall_encodingInvariant (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState)
    (hraw : HostResult.LiveSatisfies EncodingInvariant result) :
    HostResult.LiveSatisfies EncodingInvariant (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st message => trivial
  | Return values st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk paid error =>
      cases error with
      | some error => trivial
      | none =>
        have hf := applyCharges_encodingFrame st.host (chargesAfter name before st args)
        rw [hc] at hf
        have hp := EncodingInvariant.of_frame_eq hf hraw
        cases hd : deductDeposit name before { st with host := paid } args with
        | mk final error =>
          cases error with
          | some error => trivial
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => trivial
            | none =>
              have hf := deductDeposit_encodingFrame name before { st with host := paid } args
              rw [hd] at hf
              exact EncodingInvariant.of_frame_eq (updateStorageUsage_encodingFrame extra name before final args)
                (EncodingInvariant.of_frame_eq hf hp)

/-- Generic lifting for raw hosts whose payloads are already encoding-safe.
Method-bearing hosts instead use their successful-return guard proofs below. -/
theorem metered_raw_encodingInvariant (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hraw : ∀ st args, EncodingInvariant st.host →
      (applyCharges st.host (chargesBefore name st args)).2 = none →
      preInvokeError name (prechargedStore name st args) args = none →
      (prepareStorageCall name (prechargedStore name st args) args).2 = none →
      HostResult.LiveSatisfies EncodingInvariant
        (fn.invoke (prepareStorageCall name (prechargedStore name st args) args).1 args)) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra name fn) := by
  intro st args h
  unfold metered
  dsimp only
  split
  · trivial
  · split
    · trivial
    · cases hc : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => trivial
      | none =>
        let paid := prechargedStore name st args
        change HostResult.LiveSatisfies _
          (match preInvokeError name paid args with
          | some error => trapWith paid error
          | none => invokeStorageCall extra name fn paid args)
        cases hp : preInvokeError name paid args with
        | some error => trivial
        | none =>
          unfold invokeStorageCall
          dsimp only
          let ready := (prepareStorageCall name paid args).1
          cases hs : (prepareStorageCall name paid args).2 with
          | some error => cases error <;> trivial
          | none => exact finishMeteredCall_encodingInvariant extra name ready args _ (hraw st args h hc hp hs)

/-- Local host frame proofs preserve the invariant for arbitrary metering plans. -/
theorem meteredNeutral_encodingInvariant (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesEncodingFrame fn) : NearHostFn.PreservesLive EncodingInvariant (metered extra name fn) := by
  apply metered_raw_encodingInvariant
  intro st args h _ _ _
  have hf : encodingFrame (prechargedStore name st args).host = encodingFrame st.host :=
    applyCharges_encodingFrame st.host (chargesBefore name st args)
  have hp := EncodingInvariant.of_frame_eq hf h
  let ready := (prepareStorageCall name (prechargedStore name st args) args).1
  have hp : EncodingInvariant ready.host := hp
  have hr := hfn ready args
  cases he : fn.invoke ready args <;> rw [he] at hr <;>
    first | trivial | exact EncodingInvariant.of_frame_eq hr hp

/-- Combine policy preservation and concrete successful-return encoding.
Terminal errors carry no speculative invariant. -/
theorem meteredPromise_encodingInvariant (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hpolicy : HostPreservesEncodingPolicy fn)
    (hsuccess : ∀ st args values after, PromisesEncoding st.host.promises →
      st.host.config.validateActionMethodUtf8 = true →
      (metered extra name fn).invoke st args = .Return values after → PromisesEncoding after.host.promises) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra name fn) := by
  intro st args h
  have hp := metered_encodingPolicy extra name fn hpolicy st args
  cases hr : (metered extra name fn).invoke st args with
  | Trap after message => trivial
  | Return values after =>
    rw [hr] at hp
    exact ⟨hp.trans h.1, hsuccess st args values after h.2 h.1 hr⟩

theorem meteredCreate_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_create" promiseCreateFn) :=
  meteredPromise_encodingInvariant extra "promise_create" promiseCreateFn
    promiseCreateFn_encodingPolicy (meteredCreate_success_encoding extra)

theorem meteredThen_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_then" promiseThenFn) :=
  meteredPromise_encodingInvariant extra "promise_then" promiseThenFn
    promiseThenFn_encodingPolicy (meteredThen_success_encoding extra)

theorem meteredJoin_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_and" promiseAndFn) :=
  meteredPromise_encodingInvariant extra "promise_and" promiseAndFn
    promiseAndFn_encodingPolicy (meteredAnd_success_encoding extra)

theorem meteredBatchCreate_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_create" promiseBatchCreateFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_create" promiseBatchCreateFn
    promiseBatchCreateFn_encodingPolicy (meteredBatchCreate_success_encoding extra)

theorem meteredBatchThen_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_then" promiseBatchThenFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_then" promiseBatchThenFn
    promiseBatchThenFn_encodingPolicy (meteredBatchThen_success_encoding extra)

theorem meteredActionCreateAccount_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn
    promiseBatchActionCreateAccountFn_encodingPolicy (meteredActionCreateAccount_success_encoding extra)

theorem meteredActionDeployContract_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn
    promiseBatchActionDeployContractFn_encodingPolicy (meteredActionDeployContract_success_encoding extra)

theorem meteredActionFunctionCall_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn
    promiseBatchActionFunctionCallFn_encodingPolicy (meteredActionFunctionCall_success_encoding extra)

theorem meteredActionTransfer_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_transfer" promiseBatchActionTransferFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_transfer" promiseBatchActionTransferFn
    promiseBatchActionTransferFn_encodingPolicy (meteredActionTransfer_success_encoding extra)

theorem meteredActionStake_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_stake" promiseBatchActionStakeFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_stake" promiseBatchActionStakeFn
    promiseBatchActionStakeFn_encodingPolicy (meteredActionStake_success_encoding extra)

theorem meteredActionAddKeyWithFullAccess_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn
    promiseBatchActionAddKeyWithFullAccessFn_encodingPolicy (meteredActionAddKeyWithFullAccess_success_encoding extra)

theorem meteredActionAddKeyWithFunctionCall_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn
    promiseBatchActionAddKeyWithFunctionCallFn_encodingPolicy (meteredActionAddKeyWithFunctionCall_success_encoding extra)

theorem meteredActionDeleteKey_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn
    promiseBatchActionDeleteKeyFn_encodingPolicy (meteredActionDeleteKey_success_encoding extra)

theorem meteredActionDeleteAccount_encodingInvariant (extra : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (metered extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn) :=
  meteredPromise_encodingInvariant extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn
    promiseBatchActionDeleteAccountFn_encodingPolicy (meteredActionDeleteAccount_success_encoding extra)

end Wasm.Near
