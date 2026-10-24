import NearVM.CreationEncoding

namespace Wasm.Near

/-- Successful postprocessing retains exactly the raw host's promise payloads.
Charges, deposit deductions and storage accounting cannot change their encoding. -/
theorem finishMeteredCall_success_promises (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (values : List Value) (after : HostStore NearState)
    (hreturn : finishMeteredCall extra name before args result = .Return values after) :
    ∃ rawValues rawAfter, result = .Return rawValues rawAfter ∧ after.host.promises = rawAfter.host.promises := by
  cases result with
  | Trap st message => simp [finishMeteredCall] at hreturn
  | Return vals st =>
    unfold finishMeteredCall at hreturn
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk paid error =>
      cases error with
      | some error => simp [hc, trapWith] at hreturn
      | none =>
        simp only [hc] at hreturn
        cases hd : deductDeposit name before { st with host := paid } args with
        | mk final error =>
          cases error with
          | some error => simp [hd, trapWith] at hreturn
          | none =>
            simp only [hd] at hreturn
            cases he : actionMethodEncodingError name before args with
            | some error => simp [he, trapWith] at hreturn
            | none =>
              simp only [he, HostResult.Return.injEq] at hreturn
              refine ⟨vals, st, rfl, ?_⟩
              rw [← hreturn.2]
              have hp := congrArg (fun frame => frame.2.2) (applyCharges_reservationFrame st.host (chargesAfter name before st args))
              rw [hc] at hp
              have hdv := congrArg (fun view => view.1.2.2) (deductDeposit_reservationView name before { st with host := paid } args)
              rw [hd] at hdv
              have huv := congrArg (fun view => view.1.2.2) (updateStorageUsage_reservationView extra name before final args)
              exact huv.trans (hdv.trans hp)

/-- A successful post-call result can use the actual method validation fact to
establish the raw encoding invariant; speculative invalid methods need not satisfy it. -/
theorem finishMeteredCall_success_encoding_state (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (values : List Value) (after : HostStore NearState)
    (hraw : actionMethodEncodingError name before args = none →
      HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises) result)
    (hreturn : finishMeteredCall extra name before args result = .Return values after) :
    PromisesEncoding after.host.promises := by
  obtain ⟨rawValues, rawAfter, hr, hp⟩ := finishMeteredCall_success_promises extra name before args result values after hreturn
  have hv := hraw (finishMeteredCall_success_encoding extra name before args result values after hreturn)
  rw [hr] at hv
  rw [hp]
  exact hv

/-- Successful invocation has passed its ordered pre-call argument guard. -/
theorem preInvokeError_invocation_valid (name : String) (st : HostStore NearState) (args : List Value)
    (h : preInvokeError name st args = none) : invocationArgumentError name st args = none := by
  cases he : invocationArgumentError name st args with
  | none => rfl
  | some error => simp [preInvokeError, he] at h

/-- The receiver guard is part of successful creation argument validation. -/
theorem preInvokeError_creationAccount_valid (name : String) (st : HostStore NearState) (args : List Value)
    (h : preInvokeError name st args = none) : creationAccountError name st args = none := by
  have hi := preInvokeError_invocation_valid name st args h
  by_cases hw : name = "storage_write"
  · simp [hw, creationAccountError, creationAccountArgs]
  by_cases hr : name = "storage_remove"
  · simp [hr, creationAccountError, creationAccountArgs]
  have hs : storageMutationPlan? name st args = none := by simp [storageMutationPlan?, hw, hr]
  by_cases hj : name = "promise_and"
  · simp [hj, creationAccountError, creationAccountArgs]
  by_cases ht : name = "promise_batch_action_transfer"
  · simp [ht, creationAccountError, creationAccountArgs]
  by_cases hk : name = "promise_batch_action_add_key_with_function_call"
  · simp [hk, creationAccountError, creationAccountArgs]
  by_cases hg : name = "promise_batch_action_use_global_contract"
  · simp [hg, creationAccountError, creationAccountArgs]
  by_cases hga : name = "promise_batch_action_use_global_contract_by_account_id"
  · simp [hga, creationAccountError, creationAccountArgs]
  by_cases hv : spanInputHost name = true
  · simp only [spanInputHost, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [creationAccountError, creationAccountArgs]
  by_cases hl8 : name = "log_utf8"
  · simp [hl8, creationAccountError, creationAccountArgs]
  by_cases hl16 : name = "log_utf16"
  · simp [hl16, creationAccountError, creationAccountArgs]
  have hgi : globalContractInputs? name = none := by
    simp [globalContractInputs?, beq_eq_false_iff_ne.mpr hg, beq_eq_false_iff_ne.mpr hga]
  simp only [invocationArgumentError, hs, beq_eq_false_iff_ne.mpr hj,
    beq_eq_false_iff_ne.mpr ht, beq_eq_false_iff_ne.mpr hk, Bool.not_eq_true _ ▸ hv,
    beq_eq_false_iff_ne.mpr hl8, beq_eq_false_iff_ne.mpr hl16, Bool.or_false,
    Bool.false_eq_true, ite_false, hgi] at hi
  cases he : creationAccountError name st args with
  | none => rfl
  | some error => simp [creationPrefixError, he] at hi

/-- A raw host may establish encoding using both ordered validation seams.
Invalid speculative method payloads need no witness because postprocessing traps. -/
def HostValidatedEncoding (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ st args, PromisesEncoding st.host.promises → st.host.config.validateActionMethodUtf8 = true →
    preInvokeError name st args = none → actionMethodEncodingError name st args = none →
    HostResult.LiveSatisfies (fun ns => PromisesEncoding ns.promises) (fn.invoke st args)

@[simp] theorem prepareStorageCall_getMemOrReg (name : String) (st : HostStore NearState)
    (args : List Value) (ptr len : UInt64) :
    getMemOrReg (prepareStorageCall name st args).1 ptr len = getMemOrReg st ptr len := rfl

@[simp] theorem prepareStorageCall_config (name : String) (st : HostStore NearState) (args : List Value) :
    (prepareStorageCall name st args).1.host.config = st.host.config := rfl

/-- External storage fees and cache state cannot change ABI validation. -/
theorem prepareStorageCall_preInvokeError (name : String) (st : HostStore NearState) (args : List Value) :
    preInvokeError name (prepareStorageCall name st args).1 args = preInvokeError name st args := by
  by_cases hr : name = "storage_read"
  · subst name; rfl
  by_cases hh : name = "storage_has_key"
  · subst name; rfl
  by_cases hw : name = "storage_write"
  · subst name
    cases hk : getMemOrReg st (argU64 args 1) (argU64 args 0)
    all_goals cases hl : st.host.config.maxStorageKeyLen
    all_goals cases hv : getMemOrReg st (argU64 args 3) (argU64 args 2)
    all_goals cases hvl : st.host.config.maxStorageValueLen
    all_goals simp [preInvokeError, invocationArgumentError, storageMutationPlan?,
      hk, hl, hv, hvl, functionCallInputError, functionCallInputs?, allocatesPromise]
    all_goals split_ifs <;> rfl
  by_cases hd : name = "storage_remove"
  · subst name
    cases hk : getMemOrReg st (argU64 args 1) (argU64 args 0)
    all_goals cases hl : st.host.config.maxStorageKeyLen
    all_goals simp [preInvokeError, invocationArgumentError, storageMutationPlan?,
      hk, hl, functionCallInputError, functionCallInputs?, allocatesPromise]
    all_goals split_ifs <;> rfl
  rw [prepareStorageCall_other name st args (by simp [hr, hh, hw, hd])]

/-- Actual successful metered returns preserve encoding from their input state.
The concrete raw-host proof must use the validation guards, not assume a valid output. -/
theorem metered_success_encoding (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hraw : HostValidatedEncoding name fn) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra name fn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises := by
  unfold metered at hreturn
  dsimp only at hreturn
  split at hreturn
  · simp [trapWith] at hreturn
  · split at hreturn
    · simp [trapWith] at hreturn
    · cases hc : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => simp [hc, trapWith] at hreturn
      | none =>
        simp only [hc] at hreturn
        let paid := prechargedStore name st args
        change (match preInvokeError name paid args with
          | some error => trapWith paid error
          | none => invokeStorageCall extra name fn paid args) = .Return values after at hreturn
        cases hg : preInvokeError name paid args with
        | some error => simp [hg, trapWith] at hreturn
        | none =>
          simp only [hg] at hreturn
          unfold invokeStorageCall at hreturn
          dsimp only at hreturn
          let ready := (prepareStorageCall name paid args).1
          cases hs : (prepareStorageCall name paid args).2 with
          | some error => cases error <;> simp [hs, trapWith] at hreturn
          | none =>
            simp only [hs] at hreturn
            apply finishMeteredCall_success_encoding_state extra name ready args _ values after ?_ hreturn
            intro hm
            apply hraw ready args
            · change PromisesEncoding (prechargedStore name st args).host.promises
              simpa only [prechargedStore_promises] using h
            · change (prechargedStore name st args).host.config.validateActionMethodUtf8 = true
              simpa only [prechargedStore_config] using hpolicy
            · exact (prepareStorageCall_preInvokeError name paid args).trans hg
            · exact hm

/-- Creation host validation is supplied by the actual metered wrapper. -/
theorem metered_creator_success_encoding (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hraw : HostCreatesEncoding name fn) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra name fn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises := by
  apply metered_success_encoding extra name fn ?_ st args values after h hpolicy hreturn
  intro before input hb hp hg hm
  exact hraw before input hb hp (preInvokeError_creationAccount_valid name before input hg) hm

theorem meteredCreate_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_create" promiseCreateFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_creator_success_encoding extra "promise_create" promiseCreateFn
    promiseCreateFn_encoding st args values after h hpolicy hreturn

theorem meteredThen_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_then" promiseThenFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_creator_success_encoding extra "promise_then" promiseThenFn
    promiseThenFn_encoding st args values after h hpolicy hreturn

theorem meteredBatchCreate_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_create" promiseBatchCreateFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_creator_success_encoding extra "promise_batch_create" promiseBatchCreateFn
    promiseBatchCreateFn_encoding st args values after h hpolicy hreturn

theorem meteredBatchThen_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_then" promiseBatchThenFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_creator_success_encoding extra "promise_batch_then" promiseBatchThenFn
    promiseBatchThenFn_encoding st args values after h hpolicy hreturn

theorem meteredAnd_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_and" promiseAndFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_creator_success_encoding extra "promise_and" promiseAndFn
    promiseAndFn_encoding st args values after h hpolicy hreturn

/-- The batch function-call host obtains its new method witness from the
actual external guard applied after fees and deposit deduction. -/
theorem promiseBatchActionFunctionCallFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_function_call" promiseBatchActionFunctionCallFn := by
  intro st args h hpolicy _ hmethod
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPromiseActionResult_encoding _ _ _ _ h
       apply readFunctionCallAction_encoding _ _ _ _ _ _ _ _ _ _ hpolicy hmethod ?_ (by assumption)
       simp [actionMethodBytes?, functionCallInputs?, functionCallInputs, argU64])
    | split)

/-- The batch function-call host obtains its new method witness from the
actual external guard applied after fees and deposit deduction. -/
theorem promiseBatchActionFunctionCallWeightFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn := by
  intro st args h hpolicy _ hmethod
  unfold promiseBatchActionFunctionCallWeightFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPromiseActionResult_encoding _ _ _ _ h
       apply readFunctionCallAction_encoding _ _ _ _ _ _ _ _ _ _ hpolicy hmethod ?_ (by assumption)
       simp [actionMethodBytes?, functionCallInputs?, functionCallInputs, argU64])
    | split)

/-- The access-key host obtains per-field CSV witnesses from the actual
external guard, retaining multibyte names and the empty unrestricted CSV case. -/
theorem promiseBatchActionAddKeyWithFunctionCallFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn := by
  intro st args h hpolicy _ hmethod
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, checkAccountId, checkPublicKey]
  repeat' (first
    | trivial
    | (apply appendPromiseActionResult_encoding _ _ _ _ h
       apply actionMethodEncodingError_none_key_fields _ _ _ hpolicy ?_ hmethod
       simpa only [actionMethodBytes?, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
         Option.getD_some] using (by assumption))
    | split)

theorem promiseBatchActionCreateAccountFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_create_account" promiseBatchActionCreateAccountFn := by
  intro st args h _ _ _
  exact promiseBatchActionCreateAccountFn_preserves_encoding st args h

theorem meteredActionCreateAccount_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn
    promiseBatchActionCreateAccountFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionDeployContractFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn := by
  intro st args h _ _ _
  exact promiseBatchActionDeployContractFn_preserves_encoding st args h

theorem meteredActionDeployContract_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn
    promiseBatchActionDeployContractFn_validated_encoding st args values after h hpolicy hreturn

theorem meteredActionFunctionCall_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn
    promiseBatchActionFunctionCallFn_validated_encoding st args values after h hpolicy hreturn

theorem meteredActionFunctionCallWeight_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn
    promiseBatchActionFunctionCallWeightFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionTransferFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_transfer" promiseBatchActionTransferFn := by
  intro st args h _ _ _
  exact promiseBatchActionTransferFn_preserves_encoding st args h

theorem meteredActionTransfer_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_transfer" promiseBatchActionTransferFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_transfer" promiseBatchActionTransferFn
    promiseBatchActionTransferFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionStakeFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_stake" promiseBatchActionStakeFn := by
  intro st args h _ _ _
  exact promiseBatchActionStakeFn_preserves_encoding st args h

theorem meteredActionStake_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_stake" promiseBatchActionStakeFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_stake" promiseBatchActionStakeFn
    promiseBatchActionStakeFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionAddKeyWithFullAccessFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn := by
  intro st args h _ _ _
  exact promiseBatchActionAddKeyWithFullAccessFn_preserves_encoding st args h

theorem meteredActionAddKeyWithFullAccess_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn
    promiseBatchActionAddKeyWithFullAccessFn_validated_encoding st args values after h hpolicy hreturn

theorem meteredActionAddKeyWithFunctionCall_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn
    promiseBatchActionAddKeyWithFunctionCallFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionDeleteKeyFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn := by
  intro st args h _ _ _
  exact promiseBatchActionDeleteKeyFn_preserves_encoding st args h

theorem meteredActionDeleteKey_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn
    promiseBatchActionDeleteKeyFn_validated_encoding st args values after h hpolicy hreturn

theorem promiseBatchActionDeleteAccountFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn := by
  intro st args h _ _ _
  exact promiseBatchActionDeleteAccountFn_preserves_encoding st args h

theorem promiseBatchActionUseGlobalContractFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn := by
  intro st args h _ _ _
  exact promiseBatchActionUseGlobalContractFn_preserves_encoding st args h

theorem promiseBatchActionUseGlobalContractByAccountIdFn_validated_encoding :
    HostValidatedEncoding "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn := by
  intro st args h _ _ _
  exact promiseBatchActionUseGlobalContractByAccountIdFn_preserves_encoding st args h

theorem meteredActionDeleteAccount_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn
    promiseBatchActionDeleteAccountFn_validated_encoding st args values after h hpolicy hreturn

theorem meteredActionUseGlobalContract_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn
    promiseBatchActionUseGlobalContractFn_validated_encoding st args values after h hpolicy hreturn

theorem meteredActionUseGlobalContractByAccountId_success_encoding (extra : Nat) (st : HostStore NearState) (args values : List Value)
    (after : HostStore NearState) (h : PromisesEncoding st.host.promises)
    (hpolicy : st.host.config.validateActionMethodUtf8 = true)
    (hreturn : (metered extra "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn).invoke st args = .Return values after) :
    PromisesEncoding after.host.promises :=
  metered_success_encoding extra "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn
    promiseBatchActionUseGlobalContractByAccountIdFn_validated_encoding st args values after h hpolicy hreturn

end Wasm.Near
