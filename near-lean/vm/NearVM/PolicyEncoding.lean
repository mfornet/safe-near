import NearVM.NeutralEncoding

namespace Wasm.Near

/-- Host calls cannot silently disable the runtime external's decoding policy. -/
def HostPreservesEncodingPolicy (fn : HostFn NearState) : Prop :=
  ∀ st args, HostResult.LiveSatisfies
    (fun ns => ns.config.validateActionMethodUtf8 = st.host.config.validateActionMethodUtf8) (fn.invoke st args)

theorem deductDeposit_encodingPolicy (name : String) (before after : Store NearState) (args : List Value) :
    (deductDeposit name before after args).1.host.config.validateActionMethodUtf8 = after.host.config.validateActionMethodUtf8 := by
  unfold deductDeposit deductPromiseDeposit
  repeat' (first | rfl | split | (dsimp only; split))

theorem updateStorageUsage_encodingPolicy (extra : Nat) (name : String) (before after : Store NearState)
    (args : List Value) :
    (updateStorageUsage extra name before after args).host.config.validateActionMethodUtf8 = after.host.config.validateActionMethodUtf8 := by
  unfold updateStorageUsage
  repeat' (first | rfl | split | (dsimp only; split))

/-- Post-call fees, deposit charging and local storage usage keep the policy. -/
theorem finishMeteredCall_encodingPolicy (extra : Nat) (name : String) (before : Store NearState)
    (args : List Value) (result : HostResult NearState)
    (hraw : HostResult.LiveSatisfies
      (fun ns => ns.config.validateActionMethodUtf8 = before.host.config.validateActionMethodUtf8) result) :
    HostResult.LiveSatisfies (fun ns => ns.config.validateActionMethodUtf8 = before.host.config.validateActionMethodUtf8)
      (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st message => trivial
  | Throw st tag values => exact hraw
  | Return values st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk paid error =>
      cases error with
      | some error => trivial
      | none =>
        have hp := congrArg (fun frame => frame.2.1.validateActionMethodUtf8)
          (applyCharges_abiFrame st.host (chargesAfter name before st args))
        rw [hc] at hp
        cases hd : deductDeposit name before { st with host := paid } args with
        | mk final error =>
          cases error with
          | some error => trivial
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => trivial
            | none =>
              have hdv := deductDeposit_encodingPolicy name before { st with host := paid } args
              rw [hd] at hdv
              exact (updateStorageUsage_encodingPolicy extra name before final args).trans
                (hdv.trans (hp.trans hraw))

/-- Precharging also preserves the policy, so arbitrary sequences of metered
calls cannot opt out of method decoding. -/
theorem metered_encodingPolicy (extra : Nat) (name : String) (fn : HostFn NearState)
    (hraw : HostPreservesEncodingPolicy fn) : HostPreservesEncodingPolicy (metered extra name fn) := by
  intro st args
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
          | none =>
            have hr := finishMeteredCall_encodingPolicy extra name ready args _ (hraw ready args)
            change HostResult.LiveSatisfies
              (fun (ns : NearState) => ns.config.validateActionMethodUtf8 =
                (prechargedStore name st args).host.config.validateActionMethodUtf8) _ at hr
            simpa only [prechargedStore_config] using hr

theorem promiseCreateFn_encodingPolicy : HostPreservesEncodingPolicy promiseCreateFn := by
  intro st args
  unfold promiseCreateFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseThenFn_encodingPolicy : HostPreservesEncodingPolicy promiseThenFn := by
  intro st args
  unfold promiseThenFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseAndFn_encodingPolicy : HostPreservesEncodingPolicy promiseAndFn := by
  intro st args
  unfold promiseAndFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchCreateFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchCreateFn := by
  intro st args
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchThenFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchThenFn := by
  intro st args
  unfold promiseBatchThenFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionCreateAccountFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionCreateAccountFn := by
  intro st args
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionDeployContractFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionDeployContractFn := by
  intro st args
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionFunctionCallFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionFunctionCallFn := by
  intro st args
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionTransferFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionTransferFn := by
  intro st args
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionStakeFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionStakeFn := by
  intro st args
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionAddKeyWithFullAccessFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionAddKeyWithFunctionCallFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionDeleteKeyFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionDeleteKeyFn := by
  intro st args
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

theorem promiseBatchActionDeleteAccountFn_encodingPolicy : HostPreservesEncodingPolicy promiseBatchActionDeleteAccountFn := by
  intro st args
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey, appendPromise,
    appendPromiseActionResult, createBatchPromiseResult, createCallbackPromiseResult]
  repeat' (first | trivial | rfl | split)

end Wasm.Near
