import NearVM.FunctionCallValidation
import NearVM.ChargeReservations

namespace Wasm.Near

/-- A successful key plan establishes the actual ABI reads, receiver syntax,
method-list shape, target and serialized key, with no caller-supplied oracle. -/
theorem functionKeyPlan_valid_inputs {st : Store NearState} {input : FunctionKeyInputs} {sir : Bool}
    (h : (functionKeyPlan st input sir).error = none) :
    ∃ publicKey allowance receiver methods,
      getMemOrReg st input.publicKeyPtr input.publicKeyLen = some publicKey ∧
      readU128Mem st input.allowancePtr = some allowance ∧
      getMemOrReg st input.receiverPtr input.receiverLen = some receiver ∧
      (String.fromUTF8? ⟨receiver.toArray⟩).isNone = false ∧
      st.host.config.validAccountId receiver = true ∧
      getMemOrReg st input.methodsPtr input.methodsLen = some methods ∧
      methodNamesValid methods = true ∧
      functionCallTargetError st input.target = none ∧ serializedPublicKeyValid publicKey = true := by
  have option_not_none {α : Type} (o : Option α) (hne : o ≠ none) : o.isNone = false := by
    cases o <;> simp_all
  unfold functionKeyPlan at h
  repeat (first | contradiction | (dsimp only at h; split at h))
  all_goals aesop (add safe option_not_none)

theorem functionKeyPlan_valid_target {st : Store NearState} {input : FunctionKeyInputs} {sir : Bool}
    (h : (functionKeyPlan st input sir).error = none) :
    (promiseReceiver? st input.target).isSome = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := functionKeyPlan_valid_inputs h
  exact (functionCallTargetError_none_iff st input.target).mp ht

/-- Reading/UTF-8 charges reserve no onward gas. -/
theorem readSpan_reservation (fees : ActionFees) (st : Store NearState) (len ptr : UInt64) :
    ((readSpan st len ptr).map (fun charge => charge.reservation fees)).sum = 0 := by
  unfold readSpan
  repeat (first | rfl | split)

/-- Once inputs are valid, the plan reserves exactly the encoded key action's
execution gas. Sending fees and all reads remain local burn. -/
theorem functionKeyPlan_reservation {st : Store NearState} {input : FunctionKeyInputs} {sir : Bool}
    (h : (functionKeyPlan st input sir).error = none) :
    ∃ publicKey allowance receiver methods,
      getMemOrReg st input.publicKeyPtr input.publicKeyLen = some publicKey ∧
      readU128Mem st input.allowancePtr = some allowance ∧
      getMemOrReg st input.receiverPtr input.receiverLen = some receiver ∧
      getMemOrReg st input.methodsPtr input.methodsLen = some methods ∧
      ((functionKeyPlan st input sir).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        st.host.fees.addFunctionCallKeyBase.execution +
          st.host.fees.addFunctionCallKeyByte.execution * methodNamesGasBytes methods := by
  obtain ⟨pk, allowance, receiver, methods, hp, ha, hr, hu, hv, hm, hmv, ht, hk⟩ := functionKeyPlan_valid_inputs h
  refine ⟨pk, allowance, receiver, methods, hp, ha, hr, hm, ?_⟩
  simp [functionKeyPlan, hp, ha, hr, hu, hv, hm, hmv, ht,
    List.map_append, readSpan_reservation, readMem, utf8]
  simp [Charge.reservation]

/-- The concrete metered pre-invocation guard supplies plan validity. -/
theorem preInvokeError_functionKey_valid (st : Store NearState) (args : List Value)
    (h : preInvokeError "promise_batch_action_add_key_with_function_call" st args = none) :
    (functionKeyPlan st (functionKeyInputs args) false).error = none := by
  unfold preInvokeError at h
  cases he : invocationArgumentError "promise_batch_action_add_key_with_function_call" st args with
  | some error => simp [he] at h
  | none => simpa [invocationArgumentError, storageMutationPlan?] using he

end Wasm.Near
