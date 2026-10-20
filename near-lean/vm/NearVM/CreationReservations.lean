import NearVM.ActionReservations

namespace Wasm.Near

/-- Successful creation dispatch passes receiver/index validation and the
allocation limit. These facts are derived from the actual pre-invocation guard. -/
theorem preInvokeError_creation_checks (name : String) (st : Store NearState) (args : List Value)
    (hjoin : (name == "promise_and") = false)
    (htransfer : (name == "promise_batch_action_transfer") = false)
    (hkey : (name == "promise_batch_action_add_key_with_function_call") = false)
    (halloc : allocatesPromise name = true)
    (h : preInvokeError name st args = none) :
    creationAccountError name st args = none ∧ creationPrefixError name st args = none ∧ promiseCapacityError st = none := by
  have hp : creationPrefixError name st args = none := by
    cases he : creationPrefixError name st args with
    | none => rfl
    | some error => simp [preInvokeError, invocationArgumentError, hjoin, htransfer, hkey, he] at h
  have hc : promiseCapacityError st = none := by
    cases he : promiseCapacityError st with
    | none => rfl
    | some error => simp [preInvokeError, invocationArgumentError, hjoin, htransfer, hkey, hp, halloc, he] at h
  refine ⟨?_, hp, hc⟩
  cases he : creationAccountError name st args with
  | none => rfl
  | some error => simp [creationPrefixError, he] at hp

theorem chargesBefore_valid_creation (name : String) (st : Store NearState) (args : List Value)
    (len ptr : UInt64)
    (hjoin : (name == "promise_and") = false)
    (htransfer : (name == "promise_batch_action_transfer") = false)
    (hkey : (name == "promise_batch_action_add_key_with_function_call") = false)
    (halloc : allocatesPromise name = true)
    (hargs : creationAccountArgs name args = some (len, ptr))
    (h : preInvokeError name st args = none) :
    chargesBefore name st args = chargesBeforeUnvalidated name st args := by
  obtain ⟨ha, hp, hc⟩ := preInvokeError_creation_checks name st args hjoin htransfer hkey halloc h
  simp only [chargesBefore, hjoin, Bool.false_and, Bool.false_eq_true, ite_false, hargs, ha, hp, hc,
    Option.isSome_none, Bool.false_eq_true, ite_false]

/-- Empty action batches reserve only their one action-receipt execution fee. -/
theorem chargesBefore_batchCreate_reservation (st : Store NearState) (len ptr : UInt64)
    (h : preInvokeError "promise_batch_create" st [.i64 len, .i64 ptr] = none) :
    ((chargesBefore "promise_batch_create" st [.i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum = st.host.fees.newActionReceipt.execution := by
  rw [chargesBefore_valid_creation _ _ _ len ptr (by decide) (by decide) (by decide) (by decide) (by rfl) h]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, utf8]
  simp [Charge.reservation]

theorem chargesBefore_batchThen_reservation (st : Store NearState) (base len ptr : UInt64)
    (h : preInvokeError "promise_batch_then" st [.i64 base, .i64 len, .i64 ptr] = none) :
    ((chargesBefore "promise_batch_then" st [.i64 base, .i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum = st.host.fees.newActionReceipt.execution := by
  rw [chargesBefore_valid_creation _ _ _ len ptr (by decide) (by decide) (by decide) (by decide) (by rfl) h]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, utf8]
  simp [Charge.reservation]

/-- A join creates a handle, with no extra action-receipt obligation. This also
covers the overflowing-count early charge prefix, which cannot reserve gas. -/
theorem chargesBefore_join_reservation (st : Store NearState) (ptr count : UInt64) :
    ((chargesBefore "promise_and" st [.i64 ptr, .i64 count]).map
      (fun charge => charge.reservation st.host.fees)).sum = 0 := by
  simp [chargesBefore, chargesBeforeUnvalidated, creationAccountArgs, argU64, readMem]
  split <;> simp [Charge.reservation]

/-- A new function-call receipt reserves one dispatch fee plus its action and
prepaid gas. Callback dependency fees are local burn, not duplicated backing. -/
theorem chargesBefore_create_reservation (st : Store NearState)
    (len ptr ml mp al ap amount gas : UInt64)
    (h : preInvokeError "promise_create" st [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] = none) :
    ∃ action, readFunctionCallAction? st ml mp al ap amount gas = some action ∧
      ((chargesBefore "promise_create" st [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas]).map
        (fun charge => charge.reservation st.host.fees)).sum =
        st.host.fees.newActionReceipt.execution +
          actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts [] action := by
  have he := preInvokeError_functionCall_valid h
  change (functionCallPlan st (functionCallInputs [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] 2) false).error = none at he
  have he' : (functionCallPlan st (functionCallInputs [.i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] 2) (sirOfSpan st len ptr)).error = none := by
    rw [functionCallPlan_error_sir st _ _ false]
    exact he
  obtain ⟨action, ha, hg⟩ := functionCallPlan_reservation he' []
  refine ⟨action, ha, ?_⟩
  rw [chargesBefore_valid_creation _ _ _ len ptr (by decide) (by decide) (by decide) (by decide) (by rfl) h]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, utf8]
  rw [hg]
  simp [Charge.reservation]

/-- A new function-call receipt reserves one dispatch fee plus its action and
prepaid gas. Callback dependency fees are local burn, not duplicated backing. -/
theorem chargesBefore_then_reservation (st : Store NearState)
    (base len ptr ml mp al ap amount gas : UInt64)
    (h : preInvokeError "promise_then" st [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] = none) :
    ∃ action, readFunctionCallAction? st ml mp al ap amount gas = some action ∧
      ((chargesBefore "promise_then" st [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas]).map
        (fun charge => charge.reservation st.host.fees)).sum =
        st.host.fees.newActionReceipt.execution +
          actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts [] action := by
  have he := preInvokeError_functionCall_valid h
  change (functionCallPlan st (functionCallInputs [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] 3) false).error = none at he
  have he' : (functionCallPlan st (functionCallInputs [.i64 base, .i64 len, .i64 ptr, .i64 ml, .i64 mp, .i64 al, .i64 ap, .i64 amount, .i64 gas] 3) (sirOfSpan st len ptr)).error = none := by
    rw [functionCallPlan_error_sir st _ _ false]
    exact he
  obtain ⟨action, ha, hg⟩ := functionCallPlan_reservation he' []
  refine ⟨action, ha, ?_⟩
  rw [chargesBefore_valid_creation _ _ _ len ptr (by decide) (by decide) (by decide) (by decide) (by rfl) h]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, utf8]
  rw [hg]
  simp [Charge.reservation]

end Wasm.Near
