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

theorem promiseReceiverLen_eq (st : HostStore NearState) (index : Nat) :
    promiseReceiverLen st index = ((promiseReceiver? st index).getD []).length := by
  unfold promiseReceiverLen
  cases promiseReceiver? st index <;> rfl

theorem deployGlobalContractPlan_error_sir (st : HostStore NearState) (target : Nat) (len ptr : UInt64)
    (a b : Bool) :
    (deployGlobalContractPlan st target len ptr a).error = (deployGlobalContractPlan st target len ptr b).error := by
  unfold deployGlobalContractPlan
  repeat' (first | rfl | split)

set_option maxHeartbeats 2000000 in
theorem addGasKeyFunctionCallPlan_error_sir (st : HostStore NearState) (args : List Value) (a b : Bool) :
    (addGasKeyFunctionCallPlan st args a).error = (addGasKeyFunctionCallPlan st args b).error := by
  unfold addGasKeyFunctionCallPlan
  dsimp only
  repeat' (first | rfl | split)

/-- A valid `promise_batch_action_transfer_to_gas_key` plan read both operands, found the target
and reserves exactly the action's execution gas. -/
theorem transferToGasKeyPlan_valid {st : HostStore NearState} {args : List Value}
    (h : (transferToGasKeyPlan st args).error = none) :
    ∃ pk amount, getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      readU128Mem st (argU64 args 3) = some amount ∧
      functionCallTargetError st (argU64 args 0).toNat = none ∧
      ((transferToGasKeyPlan st args).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) (.transferToGasKey pk amount) := by
  unfold transferToGasKeyPlan at h ⊢
  cases hm : getMemOrReg st (argU64 args 2) (argU64 args 1) with
  | none => simp [hm] at h
  | some pk =>
    cases ha : readU128Mem st (argU64 args 3) with
    | none => simp [hm, ha] at h
    | some amount =>
      cases ht : functionCallTargetError st (argU64 args 0).toNat with
      | some error => simp [hm, ha, ht] at h
      | none =>
        refine ⟨pk, amount, rfl, rfl, rfl, ?_⟩
        dsimp only
        simp only [hm, ha, ht, List.map_append, List.sum_append, readSpan_reservation]
        simp [Charge.reservation, actionExecutionGas, readMem, promiseReceiverLen_eq, Nat.add_comm]

theorem transferToGasKeyPlan_valid_target {st : HostStore NearState} {args : List Value}
    (h : (transferToGasKeyPlan st args).error = none) :
    (promiseReceiver? st (argU64 args 0).toNat).isSome = true := by
  obtain ⟨_, _, _, _, ht, _⟩ := transferToGasKeyPlan_valid h
  exact (functionCallTargetError_none_iff st _).mp ht

theorem chargesBefore_transferToGasKey_reservation (st : HostStore NearState) (args : List Value)
    (h : (transferToGasKeyPlan st args).error = none) :
    ∃ pk amount, getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      readU128Mem st (argU64 args 3) = some amount ∧
      ((chargesBefore "promise_batch_action_transfer_to_gas_key" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) (.transferToGasKey pk amount) := by
  have ht := transferToGasKeyPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  obtain ⟨pk, amount, hm, ha, _, hr⟩ := transferToGasKeyPlan_valid h
  exact ⟨pk, amount, hm, ha, hr⟩

/-- The metered guard passes only when the argument plan does. -/
theorem preInvokeError_argument_none {name : String} {st : HostStore NearState} {args : List Value}
    (h : preInvokeError name st args = none) : invocationArgumentError name st args = none := by
  unfold preInvokeError at h
  cases he : invocationArgumentError name st args with
  | some error => simp [he] at h
  | none => rfl

theorem preInvokeError_transferToGasKey_valid {st : HostStore NearState} {args : List Value}
    (h : preInvokeError "promise_batch_action_transfer_to_gas_key" st args = none) :
    (transferToGasKeyPlan st args).error = none := by
  have he := preInvokeError_argument_none h
  simpa [invocationArgumentError, storageMutationPlan?, globalContractInputs?] using he

/-- A valid deploy-global plan read the code, found the target and reserves exactly the
action's execution gas, whatever the deploy mode. -/
theorem deployGlobalContractPlan_valid {st : HostStore NearState} {target : Nat} {len ptr : UInt64}
    {sir : Bool} (h : (deployGlobalContractPlan st target len ptr sir).error = none)
    (receiver : List UInt8) (mode : GlobalContractDeployMode) :
    ∃ code, getMemOrReg st ptr len = some code ∧ functionCallTargetError st target = none ∧
      ((deployGlobalContractPlan st target len ptr sir).charges.map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts receiver
          (.deployGlobalContract code mode) := by
  unfold deployGlobalContractPlan at h ⊢
  cases hm : getMemOrReg st ptr len with
  | none => simp [hm] at h
  | some code =>
    simp only [hm] at h ⊢
    cases hl : st.host.config.maxContractSize with
    | none =>
      simp only [hl] at h ⊢
      cases ht : functionCallTargetError st target with
      | some error => simp [ht] at h
      | none =>
        refine ⟨code, rfl, rfl, ?_⟩
        simp only [List.map_append, List.sum_append, readSpan_reservation]
        simp [Charge.reservation, actionExecutionGas]
    | some limit =>
      simp only [hl] at h ⊢
      by_cases hc : code.length > limit
      · simp [hc] at h
      · cases ht : functionCallTargetError st target with
        | some error => simp [hc, ht] at h
        | none =>
          refine ⟨code, rfl, rfl, ?_⟩
          simp only [hc, ↓reduceIte, List.map_append, List.sum_append, readSpan_reservation]
          simp [Charge.reservation, actionExecutionGas]

theorem deployGlobalContractPlan_valid_target {st : HostStore NearState} {target : Nat} {len ptr : UInt64}
    {sir : Bool} (h : (deployGlobalContractPlan st target len ptr sir).error = none) :
    (promiseReceiver? st target).isSome = true := by
  obtain ⟨_, _, ht, _⟩ := deployGlobalContractPlan_valid h [] .codeHash
  exact (functionCallTargetError_none_iff st target).mp ht

theorem chargesBefore_deployGlobalContract_reservation (name : String) (mode : GlobalContractDeployMode)
    (hname : name = "promise_batch_action_deploy_global_contract" ∨
      name = "promise_batch_action_deploy_global_contract_by_account_id")
    (st : HostStore NearState) (args : List Value)
    (h : (deployGlobalContractPlan st (argU64 args 0).toNat (argU64 args 1) (argU64 args 2)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ code, getMemOrReg st (argU64 args 2) (argU64 args 1) = some code ∧
      ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD []) (.deployGlobalContract code mode) := by
  have ht := deployGlobalContractPlan_valid_target h
  obtain ⟨code, hm, _, hr⟩ := deployGlobalContractPlan_valid h ((promiseReceiver? st (argU64 args 0).toNat).getD []) mode
  refine ⟨code, hm, ?_⟩
  rcases hname with rfl | rfl
  · rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
    exact hr
  · rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
    exact hr

theorem preInvokeError_deployGlobalContract_valid (name : String)
    (hname : name = "promise_batch_action_deploy_global_contract" ∨
      name = "promise_batch_action_deploy_global_contract_by_account_id")
    {st : HostStore NearState} {args : List Value} (h : preInvokeError name st args = none) :
    (deployGlobalContractPlan st (argU64 args 0).toNat (argU64 args 1) (argU64 args 2) false).error = none := by
  have he := preInvokeError_argument_none h
  rcases hname with rfl | rfl <;>
    simpa [invocationArgumentError, storageMutationPlan?, globalContractInputs?] using he

theorem preInvokeError_addGasKeyFull_valid {st : HostStore NearState} {args : List Value}
    (h : preInvokeError "promise_batch_action_add_gas_key_with_full_access" st args = none) :
    (addGasKeyFullAccessPlan st args).error = none := by
  have he := preInvokeError_argument_none h
  simpa [invocationArgumentError, storageMutationPlan?, globalContractInputs?] using he

theorem preInvokeError_addGasKeyFunction_valid {st : HostStore NearState} {args : List Value}
    (h : preInvokeError "promise_batch_action_add_gas_key_with_function_call" st args = none) :
    (addGasKeyFunctionCallPlan st args false).error = none := by
  have he := preInvokeError_argument_none h
  simpa [invocationArgumentError, storageMutationPlan?, globalContractInputs?] using he

/-- A valid gas-key full-access plan read the key, bounded the nonce count and reserves exactly the
action's execution gas. -/
theorem addGasKeyFullAccessPlan_valid {st : HostStore NearState} {args : List Value}
    (h : (addGasKeyFullAccessPlan st args).error = none) :
    ∃ pk, getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      functionCallTargetError st (argU64 args 0).toNat = none ∧
      ((addGasKeyFullAccessPlan st args).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD [])
          (.addKey pk 0 (.gasKeyFullAccess (argU64 args 3).toNat)) := by
  unfold addGasKeyFullAccessPlan at h ⊢
  try simp only [ge_iff_le, Nat.reducePow] at h ⊢
  cases hm : getMemOrReg st (argU64 args 2) (argU64 args 1) with
  | none => simp [hm] at h
  | some pk =>
    simp only [hm] at h ⊢
    by_cases hn : 65536 ≤ (argU64 args 3).toNat
    · simp [hn] at h
    · cases ht : functionCallTargetError st (argU64 args 0).toNat with
      | some error => simp [hn, ht] at h
      | none =>
        refine ⟨pk, rfl, rfl, ?_⟩
        simp only [hn, ↓reduceIte, List.map_append, List.sum_append, readSpan_reservation]
        simp [Charge.reservation, actionExecutionGas, gasKeyAddCharges, promiseReceiverLen_eq, Nat.add_assoc]

theorem addGasKeyFullAccessPlan_valid_target {st : HostStore NearState} {args : List Value}
    (h : (addGasKeyFullAccessPlan st args).error = none) :
    (promiseReceiver? st (argU64 args 0).toNat).isSome = true := by
  obtain ⟨_, _, ht, _⟩ := addGasKeyFullAccessPlan_valid h
  exact (functionCallTargetError_none_iff st _).mp ht

theorem chargesBefore_addGasKeyFull_reservation (st : HostStore NearState) (args : List Value)
    (h : (addGasKeyFullAccessPlan st args).error = none) :
    ∃ pk, getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      ((chargesBefore "promise_batch_action_add_gas_key_with_full_access" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD [])
          (.addKey pk 0 (.gasKeyFullAccess (argU64 args 3).toNat)) := by
  have ht := addGasKeyFullAccessPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  obtain ⟨pk, hm, _, hr⟩ := addGasKeyFullAccessPlan_valid h
  exact ⟨pk, hm, hr⟩

/-- A valid gas-key function-call plan reserves exactly the action's execution gas. -/
theorem addGasKeyFunctionCallPlan_valid {st : HostStore NearState} {args : List Value} {sir : Bool}
    (h : (addGasKeyFunctionCallPlan st args sir).error = none) :
    ∃ pk allowance receiver methods,
      getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      readU128Mem st (argU64 args 4) = some allowance ∧
      getMemOrReg st (argU64 args 6) (argU64 args 5) = some receiver ∧
      getMemOrReg st (argU64 args 8) (argU64 args 7) = some methods ∧
      functionCallTargetError st (argU64 args 0).toNat = none ∧
      ((addGasKeyFunctionCallPlan st args sir).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD [])
          (.addKey pk 0 (.gasKeyFunctionCall (argU64 args 3).toNat (functionCallAllowance allowance)
            receiver methods)) := by
  unfold addGasKeyFunctionCallPlan at h ⊢
  simp only [functionKeyInputs, ge_iff_le, Nat.reducePow] at h ⊢
  try dsimp only at h ⊢
  cases hp : getMemOrReg st (argU64 args 2) (argU64 args 1) with
  | none => simp [hp] at h
  | some pk =>
    simp only [hp] at h ⊢
    by_cases hn : 65536 ≤ (argU64 args 3).toNat
    · simp [hn] at h
    · simp only [hn, ↓reduceIte] at h ⊢
      cases ha : readU128Mem st (argU64 args 4) with
      | none => simp [ha] at h
      | some allowance =>
        simp only [ha] at h ⊢
        cases hr : getMemOrReg st (argU64 args 6) (argU64 args 5) with
        | none => simp [hr] at h
        | some receiver =>
          simp only [hr] at h ⊢
          by_cases hu : (String.fromUTF8? ⟨receiver.toArray⟩).isNone = true
          · simp [hu] at h
          · by_cases hv : (!st.host.config.validAccountId receiver) = true
            · simp [hu, hv] at h
            · simp only [hu, hv, Bool.false_eq_true, ↓reduceIte]
              simp only [hu, hv, Bool.false_eq_true, ↓reduceIte] at h
              cases hmt : getMemOrReg st (argU64 args 8) (argU64 args 7) with
              | none => simp [hmt] at h
              | some methods =>
                simp only [hmt] at h ⊢
                by_cases hmv : (!methodNamesValid methods) = true
                · simp [hmv] at h
                · simp only [hmv, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  cases ht : functionCallTargetError st (argU64 args 0).toNat with
                  | some error => simp [ht] at h
                  | none =>
                    refine ⟨pk, allowance, receiver, methods, rfl, rfl, rfl, rfl, rfl, ?_⟩
                    simp only [List.map_append, List.sum_append, readSpan_reservation]
                    simp [Charge.reservation, actionExecutionGas, gasKeyAddCharges, promiseReceiverLen_eq,
                      readMem, utf8, Nat.add_assoc]

theorem addGasKeyFunctionCallPlan_valid_target {st : HostStore NearState} {args : List Value} {sir : Bool}
    (h : (addGasKeyFunctionCallPlan st args sir).error = none) :
    (promiseReceiver? st (argU64 args 0).toNat).isSome = true := by
  obtain ⟨_, _, _, _, _, _, _, _, ht, _⟩ := addGasKeyFunctionCallPlan_valid h
  exact (functionCallTargetError_none_iff st _).mp ht

theorem chargesBefore_addGasKeyFunction_reservation (st : HostStore NearState) (args : List Value)
    (h : (addGasKeyFunctionCallPlan st args (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none) :
    ∃ pk allowance receiver methods,
      getMemOrReg st (argU64 args 2) (argU64 args 1) = some pk ∧
      readU128Mem st (argU64 args 4) = some allowance ∧
      getMemOrReg st (argU64 args 6) (argU64 args 5) = some receiver ∧
      getMemOrReg st (argU64 args 8) (argU64 args 7) = some methods ∧
      ((chargesBefore "promise_batch_action_add_gas_key_with_function_call" st args).map
        (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st (argU64 args 0).toNat).getD [])
          (.addKey pk 0 (.gasKeyFunctionCall (argU64 args 3).toNat (functionCallAllowance allowance)
            receiver methods)) := by
  have ht := addGasKeyFunctionCallPlan_valid_target h
  rw [chargesBefore_valid_batch_target _ _ _ (by decide) (by rfl) ht (by decide) (by decide)]
  obtain ⟨pk, allowance, receiver, methods, hp, ha, hr, hm, _, hres⟩ := addGasKeyFunctionCallPlan_valid h
  exact ⟨pk, allowance, receiver, methods, hp, ha, hr, hm, hres⟩

theorem chargesBefore_yieldCreate_eq (st : HostStore NearState) (args : List Value) :
    chargesBefore "promise_yield_create" st args = (yieldCreatePlan st args).charges := by
  simp [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated]

theorem chargesBefore_yieldResume_eq (st : HostStore NearState) (args : List Value) :
    chargesBefore "promise_yield_resume" st args = (yieldResumePlan st args).charges := by
  simp [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated]

theorem preInvokeError_yieldCreate_valid {st : HostStore NearState} {args : List Value}
    (h : preInvokeError "promise_yield_create" st args = none) :
    (yieldCreatePlan st args).error = none := by
  have he := preInvokeError_argument_none h
  simpa [invocationArgumentError, storageMutationPlan?, globalContractInputs?] using he

/-- A valid `promise_yield_create` plan read both inputs and reserves the receipt, the callback's
prepaid gas and its function-call fees. -/
theorem yieldCreatePlan_valid {st : HostStore NearState} {args : List Value}
    (h : (yieldCreatePlan st args).error = none) :
    ∃ method arguments, getMemOrReg st (argU64 args 1) (argU64 args 0) = some method ∧
      getMemOrReg st (argU64 args 3) (argU64 args 2) = some arguments ∧
      ((yieldCreatePlan st args).charges.map (fun charge => charge.reservation st.host.fees)).sum =
        st.host.fees.newActionReceipt.execution +
          (st.host.fees.functionCallBase.execution +
            st.host.fees.functionCallByte.execution * (method.length + arguments.length) +
            (argU64 args 4).toNat) := by
  unfold yieldCreatePlan at h ⊢
  cases hm : getMemOrReg st (argU64 args 1) (argU64 args 0) with
  | none => simp [hm] at h
  | some method =>
    simp only [hm] at h ⊢
    by_cases he : method.isEmpty = true
    · simp [he] at h
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hc : getMemOrReg st (argU64 args 3) (argU64 args 2) with
      | none => simp [hc] at h
      | some arguments =>
        simp only [hc] at h ⊢
        cases hp : promiseCapacityError st with
        | some error => simp [hp] at h
        | none =>
          refine ⟨method, arguments, rfl, rfl, ?_⟩
          simp only [List.map_append, List.sum_append, readSpan_reservation]
          simp [Charge.reservation, writeReg]
          omega

theorem chargesBefore_yieldCreate_reservation (st : HostStore NearState) (args : List Value)
    (h : (yieldCreatePlan st args).error = none) :
    ∃ method arguments, getMemOrReg st (argU64 args 1) (argU64 args 0) = some method ∧
      getMemOrReg st (argU64 args 3) (argU64 args 2) = some arguments ∧
      ((chargesBefore "promise_yield_create" st args).map (fun charge => charge.reservation st.host.fees)).sum =
        st.host.fees.newActionReceipt.execution +
          (st.host.fees.functionCallBase.execution +
            st.host.fees.functionCallByte.execution * (method.length + arguments.length) +
            (argU64 args 4).toNat) := by
  rw [chargesBefore_yieldCreate_eq]
  exact yieldCreatePlan_valid h

/-- Resuming a yield reserves no gas: every charge is a metered read. -/
theorem chargesBefore_yieldResume_reservation (st : HostStore NearState) (args : List Value) :
    ((chargesBefore "promise_yield_resume" st args).map (fun charge => charge.reservation st.host.fees)).sum = 0 := by
  rw [chargesBefore_yieldResume_eq]
  unfold yieldResumePlan
  dsimp only
  repeat' split
  all_goals
    simp only [List.map_append, List.sum_append, readSpan_reservation]
    simp [Charge.reservation]

end Wasm.Near
