import NearVM.HostGasObligations

namespace Wasm.Near

/-- A valid batch target reaches the full action charge plan. -/
theorem chargesBefore_valid_batch_target (name : String) (st : HostStore NearState) (args : List Value)
    (hjoin : (name == "promise_and") = false)
    (hcreation : creationAccountArgs name args = none)
    (htarget : (promiseReceiver? st (argU64 args 0).toNat).isSome = true)
    (hwrite : name ≠ "storage_write") (hremove : name ≠ "storage_remove") :
    chargesBefore name st args = chargesBeforeUnvalidated name st args := by
  have hs : storageMutationPlan? name st args = none := by simp [storageMutationPlan?, hwrite, hremove]
  have hn : (promiseReceiver? st (argU64 args 0).toNat).isNone = false := by
    cases he : promiseReceiver? st (argU64 args 0).toNat <;> simp_all
  simp only [chargesBefore, hs, hjoin, Bool.false_and, Bool.false_eq_true, ite_false, hcreation, hn, Bool.and_false]

/-- The length billed by a successful ABI span is the bytes actually read. -/
theorem spanLen_of_read {st : HostStore NearState} {len ptr : UInt64} {bytes : List UInt8}
    (hread : getMemOrReg st ptr len = some bytes) : spanLen st len ptr = bytes.length := by
  by_cases hl : len = u64Max
  · simp only [getMemOrReg, hl, ite_true] at hread
    simp [spanLen, hl, hread]
  · simp only [getMemOrReg, hl, ite_false] at hread
    split at hread
    · contradiction
    · have he := Option.some.inj hread
      subst bytes
      simp [spanLen, hl]

/-- Receipt creation is charged once, independently of dependency-data costs. -/
theorem newReceipt_reservation (fees : ActionFees) (sir : Bool) (dependencies : List Bool) :
    (Charge.newReceipt sir dependencies).reservation fees = fees.newActionReceipt.execution := rfl

theorem chargesBefore_createAccount_reservation (st : HostStore NearState) (index : UInt64)
    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_create_account" st [.i64 index]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) .createAccount := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, Charge.reservation, actionExecutionGas]

theorem chargesBefore_deploy_reservation (st : HostStore NearState) (index len ptr : UInt64) (bytes : List UInt8)
    (hread : getMemOrReg st ptr len = some bytes)
    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_deploy_contract" st [.i64 index, .i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.deployContract bytes) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, spanLen_of_read hread]
  simp [Charge.reservation, actionExecutionGas]

theorem chargesBefore_stake_reservation (st : HostStore NearState) (index amountPtr len ptr : UInt64) (amount : Nat) (pk : List UInt8)

    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_stake" st [.i64 index, .i64 amountPtr, .i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.stake amount pk) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, readMem]
  simp [Charge.reservation, actionExecutionGas]

theorem chargesBefore_fullAccessKey_reservation (st : HostStore NearState) (index len ptr nonce : UInt64) (pk : List UInt8)

    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_add_key_with_full_access" st [.i64 index, .i64 len, .i64 ptr, .i64 nonce]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.addKey pk nonce .fullAccess) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation]
  simp [Charge.reservation, actionExecutionGas]

theorem chargesBefore_deleteKey_reservation (st : HostStore NearState) (index len ptr : UInt64) (pk : List UInt8)

    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_delete_key" st [.i64 index, .i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.deleteKey pk) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation]
  simp [Charge.reservation, actionExecutionGas]

theorem chargesBefore_deleteAccount_reservation (st : HostStore NearState) (index len ptr : UInt64) (beneficiary : List UInt8)

    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_delete_account" st [.i64 index, .i64 len, .i64 ptr]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.deleteAccount beneficiary) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, List.map_append, readSpan_reservation, utf8]
  simp [Charge.reservation, actionExecutionGas]

theorem chargesBefore_transfer_reservation (st : HostStore NearState) (index amountPtr : UInt64) (amount : Nat)
    (hread : readU128Mem st amountPtr = some amount)
    (htarget : (promiseReceiver? st index.toNat).isSome = true) :
    ((chargesBefore "promise_batch_action_transfer" st [.i64 index, .i64 amountPtr]).map
      (fun charge => charge.reservation st.host.fees)).sum =
      actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
        ((promiseReceiver? st index.toNat).getD []) (.transfer amount) := by
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) (by simpa [argU64] using htarget) (by decide) (by decide)]
  simp [chargesBeforeUnvalidated, argU64, transferCharges, hread, readMem]
  simp [Charge.reservation, actionExecutionGas]

/-- Same-receiver status changes sending costs, never input validity. -/
theorem functionCallPlan_error_sir (st : HostStore NearState) (input : FunctionCallInputs) (a b : Bool) :
    (functionCallPlan st input a).error = (functionCallPlan st input b).error := by
  cases ha : readU128Mem st input.amountPtr with
  | none => simp [functionCallPlan, ha]
  | some amount =>
    cases hm : getMemOrReg st input.methodPtr input.methodLen with
    | none => simp [functionCallPlan, ha, hm]
    | some method =>
      cases hx : getMemOrReg st input.argsPtr input.argsLen with
      | none => simp [functionCallPlan, ha, hm, hx]
      | some arguments =>
        cases ht : input.target.bind (functionCallTargetError st) <;>
          (by_cases he : method.isEmpty = true <;> simp [functionCallPlan, ha, hm, hx, ht, he])

/-- Validated function calls reserve base/byte execution costs and the actual
prepaid gas; the amount and raw method/argument bytes come from guest reads. -/
theorem functionCallPlan_reservation {st : HostStore NearState} {input : FunctionCallInputs} {sir : Bool}
    (h : (functionCallPlan st input sir).error = none) (receiver : List UInt8) :
    ∃ action,
      readFunctionCallAction? st input.methodLen input.methodPtr input.argsLen input.argsPtr input.amountPtr input.gas =
        some action ∧
      ((functionCallPlan st input sir).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts receiver action := by
  obtain ⟨amount, method, arguments, ha, hm, hnonempty, hargs⟩ := functionCallPlan_valid_inputs h
  have hempty : method.isEmpty = false := by cases method <;> simp_all
  refine ⟨.functionCall method arguments amount input.gas, by simp [readFunctionCallAction?, ha, hm, hargs], ?_⟩
  cases ht : input.target.bind (functionCallTargetError st) with
  | some error => simp [functionCallPlan, ha, hm, hempty, hargs, ht] at h
  | none =>
    simp [functionCallPlan, ha, hm, hempty, hargs, ht, List.map_append, readSpan_reservation, readMem]
    simp [Charge.reservation, actionExecutionGas, Nat.add_assoc]

theorem chargesBefore_functionCall_reservation (st : HostStore NearState) (args : List Value)
    (h : (functionCallPlan st (functionCallInputs args 1 (some (argU64 args 0).toNat))
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ action,
      readFunctionCallAction? st (argU64 args 1) (argU64 args 2) (argU64 args 3) (argU64 args 4)
        (argU64 args 5) (argU64 args 6) = some action ∧
      ((chargesBefore "promise_batch_action_function_call" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) action := by
  have ht := functionCallPlan_valid_target h rfl
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  exact functionCallPlan_reservation h _

theorem chargesBefore_functionKey_reservation (st : HostStore NearState) (args : List Value)
    (h : (functionKeyPlan st (functionKeyInputs args)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ publicKey allowance receiver methods,
      getMemOrReg st (argU64 args 2) (argU64 args 1) = some publicKey ∧
      readU128Mem st (argU64 args 4) = some allowance ∧
      getMemOrReg st (argU64 args 6) (argU64 args 5) = some receiver ∧
      getMemOrReg st (argU64 args 8) (argU64 args 7) = some methods ∧
      ((chargesBefore "promise_batch_action_add_key_with_function_call" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD [])
          (.addKey publicKey (argU64 args 3) (.functionCall (functionCallAllowance allowance) receiver methods)) := by
  have ht := functionKeyPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  exact functionKeyPlan_reservation h

/-- A valid `use_global_contract` plan read the identifier, found the target
and reserves exactly the action's execution gas. -/
theorem globalContractPlan_valid {st : HostStore NearState} {byAccount : Bool} {target : Nat}
    {len ptr : UInt64} {sir : Bool} (h : (globalContractPlan st byAccount target len ptr sir).error = none)
    (receiver : List UInt8) :
    ∃ bytes, getMemOrReg st ptr len = some bytes ∧ functionCallTargetError st target = none ∧
      ((globalContractPlan st byAccount target len ptr sir).charges.map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts receiver
          (.useGlobalContract (if byAccount then .accountId bytes else .codeHash bytes)) := by
  unfold globalContractPlan at h ⊢
  cases hm : getMemOrReg st ptr len with
  | none => simp [hm] at h
  | some bytes =>
    simp only [hm] at h ⊢
    split at h
    · simp at h
    · rename_i hid
      split at h
      · simp at h
      · rename_i ht
        refine ⟨bytes, rfl, ht, ?_⟩
        cases byAccount <;>
          simp only [Bool.false_eq_true, ite_true, ite_false, List.map_append, List.sum_append,
            readSpan_reservation] <;>
          simp [utf8, Charge.reservation, actionExecutionGas, GlobalContractId.length]

theorem globalContractPlan_valid_target {st : HostStore NearState} {byAccount : Bool} {target : Nat}
    {len ptr : UInt64} {sir : Bool} (h : (globalContractPlan st byAccount target len ptr sir).error = none) :
    (promiseReceiver? st target).isSome = true := by
  obtain ⟨_, _, ht, _⟩ := globalContractPlan_valid h []
  exact (functionCallTargetError_none_iff st target).mp ht

theorem chargesBefore_useGlobalContract_reservation (st : HostStore NearState) (args : List Value)
    (h : (globalContractPlan st false (argU64 args 0).toNat (argU64 args 1) (argU64 args 2)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ bytes, getMemOrReg st (argU64 args 2) (argU64 args 1) = some bytes ∧
      ((chargesBefore "promise_batch_action_use_global_contract" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) (.useGlobalContract (.codeHash bytes)) := by
  have ht := globalContractPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  obtain ⟨bytes, hm, _, hr⟩ := globalContractPlan_valid h ((promiseReceiver? st (argU64 args 0).toNat).getD [])
  exact ⟨bytes, hm, hr⟩

theorem chargesBefore_useGlobalContractByAccountId_reservation (st : HostStore NearState) (args : List Value)
    (h : (globalContractPlan st true (argU64 args 0).toNat (argU64 args 1) (argU64 args 2)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ bytes, getMemOrReg st (argU64 args 2) (argU64 args 1) = some bytes ∧
      ((chargesBefore "promise_batch_action_use_global_contract_by_account_id" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) (.useGlobalContract (.accountId bytes)) := by
  have ht := globalContractPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  obtain ⟨bytes, hm, _, hr⟩ := globalContractPlan_valid h ((promiseReceiver? st (argU64 args 0).toNat).getD [])
  exact ⟨bytes, hm, hr⟩

/-- Same-receiver status affects sending fees, never identifier validation. -/
theorem globalContractPlan_error_sir (st : HostStore NearState) (byAccount : Bool) (target : Nat)
    (len ptr : UInt64) (a b : Bool) :
    (globalContractPlan st byAccount target len ptr a).error =
      (globalContractPlan st byAccount target len ptr b).error := by
  unfold globalContractPlan
  repeat' (first | rfl | split)

/-- The concrete metered pre-invocation guard supplies plan validity. -/
theorem preInvokeError_useGlobalContract_valid (name : String) (byAccount : Bool)
    (hname : globalContractInputs? name = some byAccount) (st : HostStore NearState) (args : List Value)
    (hstorage : storageMutationPlan? name st args = none) (hjoin : (name == "promise_and") = false)
    (htransfer : (name == "promise_batch_action_transfer") = false)
    (hkey : (name == "promise_batch_action_add_key_with_function_call") = false)
    (h : preInvokeError name st args = none) :
    (globalContractPlan st byAccount (argU64 args 0).toNat (argU64 args 1) (argU64 args 2) false).error = none := by
  unfold preInvokeError at h
  cases he : invocationArgumentError name st args with
  | some error => simp [he] at h
  | none =>
    simp only [invocationArgumentError, hstorage, hjoin, htransfer, hkey, hname, Bool.false_eq_true,
      ite_false] at he
    exact he

end Wasm.Near
