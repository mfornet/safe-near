import NearVM.MeteredBatchReservations

namespace Wasm.Near

@[simp] theorem prechargedStore_creationAccountError (name : String) (st : HostStore NearState) (args : List Value) :
    creationAccountError name (prechargedStore name st args) args = creationAccountError name st args := by
  unfold creationAccountError
  simp only [prechargedStore_getMemOrReg, prechargedStore_config]

@[simp] theorem prechargedStore_creationPrefixError (name : String) (st : HostStore NearState) (args : List Value) :
    creationPrefixError name (prechargedStore name st args) args = creationPrefixError name st args := by
  simp only [creationPrefixError, prechargedStore_creationAccountError, promiseIndexValid, prechargedStore_promises]
  rfl

@[simp] theorem prechargedStore_promiseCapacityError (name : String) (st : HostStore NearState) (args : List Value) :
    promiseCapacityError (prechargedStore name st args) = promiseCapacityError st := by
  simp only [promiseCapacityError, prechargedStore_config, prechargedStore_promises]

@[simp] theorem prechargedStore_functionCallInputError (name : String) (st : HostStore NearState) (args : List Value) :
    functionCallInputError name (prechargedStore name st args) args = functionCallInputError name st args := by
  unfold functionCallInputError
  cases functionCallInputs? name args <;> simp only [Option.bind, prechargedStore_functionCallPlan_error]

/-- Receiver/index, capacity and function-call validation use the same inputs
before and after successful precharging. The join/transfer/key/storage guards have
separate validation paths and are excluded from this creation lemma. -/
theorem prechargedStore_creation_guard (name : String) (st : HostStore NearState) (args : List Value)
    (hjoin : (name == "promise_and") = false)
    (htransfer : (name == "promise_batch_action_transfer") = false)
    (hkey : (name == "promise_batch_action_add_key_with_function_call") = false)
    (hwrite : name ≠ "storage_write") (hremove : name ≠ "storage_remove") :
    preInvokeError name (prechargedStore name st args) args = preInvokeError name st args := by
  have hs (store : HostStore NearState) : storageMutationPlan? name store args = none := by
    simp [storageMutationPlan?, hwrite, hremove]
  simp only [preInvokeError, invocationArgumentError, hs, hjoin, htransfer, hkey, Bool.false_eq_true, ite_false,
    prechargedStore_creationPrefixError, prechargedStore_promiseCapacityError, prechargedStore_functionCallInputError,
    prechargedStore_globalContractPlan_error, prechargedStore_getMemOrReg]

/-- A new raw promise consumes the gas reserved by its public charge plan.
The concrete creator proofs below discharge the plan equality from ABI reads. -/
theorem appendPrechargedPromise_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (name : String) (st : HostStore NearState) (args values : List Value) (promise : NearPromise)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore name st args)).2 = none)
    (hreservation : ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum =
      promiseValue (receiptGasValue st.host.fees st.host.config.ethImplicitAccounts) promise) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (.Return values (appendPromise (prechargedStore name st args) promise)) := by
  let paid := prechargedStore name st args
  have hf := prechargedStore_frame name st args
  have hfees := congrArg Prod.fst hf
  have heth := congrArg (fun frame => frame.2.1) hf
  have hpromises := congrArg (fun frame => frame.2.2) hf
  change paid.host.fees = st.host.fees at hfees
  change paid.host.config.ethImplicitAccounts = st.host.config.ethImplicitAccounts at heth
  change paid.host.promises = st.host.promises at hpromises
  have hgas := prechargedStore_reservation name st args hsuccess
  change paid.host.gas.promises = _ at hgas
  change ReservationInvariant fees ethEnabled (appendPromise paid promise).host
  refine ⟨hfees.trans h.1, heth.trans h.2.1, ?_⟩
  change paid.host.gas.promises = promisesGas fees ethEnabled (appendPromise paid promise).host.promises
  rw [appendPromise_gas]
  rw [hreservation] at hgas
  have hbefore := h.2.2
  change st.host.gas.promises = promisesGas fees ethEnabled st.host.promises at hbefore
  simpa only [hpromises, h.1, h.2.1, hbefore] using hgas

/-- Function-call action fees depend on method/argument bytes and prepaid gas,
not on the receiver whose receipt carries the call. -/
theorem readFunctionCallAction_gas_receiver (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (ml mp al ap amount gas : UInt64) (action : PromiseAction)
    (hread : readFunctionCallAction? st ml mp al ap amount gas = some action)
    (left right : List UInt8) :
    actionExecutionGas fees ethEnabled left action = actionExecutionGas fees ethEnabled right action := by
  unfold readFunctionCallAction? at hread
  obtain ⟨method, _, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨arguments, _, hread⟩ := Option.bind_eq_some_iff.mp hread
  obtain ⟨deposit, _, hread⟩ := Option.bind_eq_some_iff.mp hread
  have he := Option.some.inj hread
  subst action
  rfl

theorem prechargedBatchCreate_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_create" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_create" (prechargedStore "promise_batch_create" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchCreateFn.invoke (prechargedStore "promise_batch_create" st args) args) := by
  rw [prechargedStore_creation_guard _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)] at hguard
  unfold promiseBatchCreateFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedPromise_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       simp only [promiseValue, receiptGasValue, List.map_nil, List.sum_nil, Nat.add_zero]
       apply chargesBefore_batchCreate_reservation
       exact hguard )
    | split)

theorem meteredBatchCreate_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_create" promiseBatchCreateFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedBatchCreate_reservationInvariant fees ethEnabled st args h hs hg

theorem prechargedBatchThen_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_then" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_then" (prechargedStore "promise_batch_then" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchThenFn.invoke (prechargedStore "promise_batch_then" st args) args) := by
  rw [prechargedStore_creation_guard _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)] at hguard
  unfold promiseBatchThenFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedPromise_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       simp only [promiseValue, receiptGasValue, List.map_nil, List.sum_nil, Nat.add_zero]
       apply chargesBefore_batchThen_reservation
       exact hguard )
    | split)

theorem meteredBatchThen_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_then" promiseBatchThenFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedBatchThen_reservationInvariant fees ethEnabled st args h hs hg

theorem prechargedJoin_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_and" st args)).2 = none)
    (hguard : preInvokeError "promise_and" (prechargedStore "promise_and" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseAndFn.invoke (prechargedStore "promise_and" st args) args) := by
  unfold promiseAndFn
  dsimp only [disallowInView, createBatchPromiseResult, createCallbackPromiseResult, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedPromise_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       simp only [promiseValue]
       apply chargesBefore_join_reservation )
    | split)

theorem meteredJoin_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_and" promiseAndFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedJoin_reservationInvariant fees ethEnabled st args h hs hg

theorem chargesBefore_createPromise_reservation (st : HostStore NearState)
    (len ptr ml mp al ap amount gas : UInt64) (account : List UInt8) (action : PromiseAction)
    (hread : readFunctionCallAction? st ml mp al ap amount gas = some action)
    (hguard : preInvokeError "promise_create" st [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] = none) :
    ((chargesBefore "promise_create" st [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas]).map (fun charge => charge.reservation st.host.fees)).sum =
      promiseValue (receiptGasValue st.host.fees st.host.config.ethImplicitAccounts) (.batch account [action]) := by
  obtain ⟨parsed, hp, hres⟩ := chargesBefore_create_reservation st len ptr ml mp al ap amount gas hguard
  have he : parsed = action := Option.some.inj (hp.symm.trans hread)
  subst parsed
  rw [hres]
  simp only [promiseValue, receiptGasValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [readFunctionCallAction_gas_receiver st.host.fees st.host.config.ethImplicitAccounts st ml mp al ap amount gas action hread [] account]

theorem prechargedCreate_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_create" st args)).2 = none)
    (hguard : preInvokeError "promise_create" (prechargedStore "promise_create" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseCreateFn.invoke (prechargedStore "promise_create" st args) args) := by
  rw [prechargedStore_creation_guard _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)] at hguard
  unfold promiseCreateFn
  dsimp only [disallowInView, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedPromise_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       apply chargesBefore_createPromise_reservation
       · simp_all only [prechargedStore_readFunctionCallAction]
       · exact hguard)
    | split)

theorem meteredCreate_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_create" promiseCreateFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedCreate_reservationInvariant fees ethEnabled st args h hs hg

theorem chargesBefore_thenPromise_reservation (st : HostStore NearState)
    (base len ptr ml mp al ap amount gas : UInt64) (account : List UInt8) (action : PromiseAction)
    (hread : readFunctionCallAction? st ml mp al ap amount gas = some action)
    (hguard : preInvokeError "promise_then" st [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] = none) :
    ((chargesBefore "promise_then" st [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas]).map (fun charge => charge.reservation st.host.fees)).sum =
      promiseValue (receiptGasValue st.host.fees st.host.config.ethImplicitAccounts) (.callback base.toNat account [action]) := by
  obtain ⟨parsed, hp, hres⟩ := chargesBefore_then_reservation st base len ptr ml mp al ap amount gas hguard
  have he : parsed = action := Option.some.inj (hp.symm.trans hread)
  subst parsed
  rw [hres]
  simp only [promiseValue, receiptGasValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [readFunctionCallAction_gas_receiver st.host.fees st.host.config.ethImplicitAccounts st ml mp al ap amount gas action hread [] account]

theorem prechargedThen_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_then" st args)).2 = none)
    (hguard : preInvokeError "promise_then" (prechargedStore "promise_then" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseThenFn.invoke (prechargedStore "promise_then" st args) args) := by
  rw [prechargedStore_creation_guard _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)] at hguard
  unfold promiseThenFn
  dsimp only [disallowInView, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedPromise_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       apply chargesBefore_thenPromise_reservation
       · simp_all only [prechargedStore_readFunctionCallAction]
       · exact hguard)
    | split)

theorem meteredThen_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_then" promiseThenFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedThen_reservationInvariant fees ethEnabled st args h hs hg

end Wasm.Near
