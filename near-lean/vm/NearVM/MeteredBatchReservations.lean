import NearVM.MeteredReservations

namespace Wasm.Near

/-- The actual store prepared by the metered wrapper before raw invocation. -/
def prechargedStore (name : String) (st : HostStore NearState) (args : List Value) : HostStore NearState :=
  let ns := (applyCharges st.host (chargesBefore name st args)).1
  { st with host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }

theorem prechargedStore_frame (name : String) (st : HostStore NearState) (args : List Value) :
    reservationFrame (prechargedStore name st args).host = reservationFrame st.host :=
  applyCharges_reservationFrame st.host (chargesBefore name st args)

theorem prechargedStore_reservation (name : String) (st : HostStore NearState) (args : List Value)
    (hsuccess : (applyCharges st.host (chargesBefore name st args)).2 = none) :
    (prechargedStore name st args).host.gas.promises = st.host.gas.promises +
      ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum :=
  applyCharges_success_reservation st.host (chargesBefore name st args) hsuccess

/-- Charging leaves guest input registers, protocol validation and promises fixed. -/
theorem applyCharges_abiFrame (ns : NearState) (charges : List Charge) :
    ((applyCharges ns charges).1.registers, (applyCharges ns charges).1.config,
      (applyCharges ns charges).1.promises) = (ns.registers, ns.config, ns.promises) := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge rest ih =>
    have hp : ((applyCharge ns charge).1.registers, (applyCharge ns charge).1.config,
        (applyCharge ns charge).1.promises) = (ns.registers, ns.config, ns.promises) := by
      cases charge <;> rfl
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | some error => simpa only [applyCharges, hc] using hp
      | none => simpa only [applyCharges, hc] using (ih paid).trans hp

@[simp] theorem prechargedStore_getMemOrReg (name : String) (st : HostStore NearState) (args : List Value)
    (ptr len : UInt64) : getMemOrReg (prechargedStore name st args) ptr len = getMemOrReg st ptr len := by
  have hr := congrArg Prod.fst (applyCharges_abiFrame st.host (chargesBefore name st args))
  change (prechargedStore name st args).host.registers = st.host.registers at hr
  have hm : (prechargedStore name st args).mem = st.mem := rfl
  simp only [getMemOrReg, hr, hm]

/-- Charging leaves the logs fixed. -/
theorem applyCharges_logs (ns : NearState) (charges : List Charge) :
    (applyCharges ns charges).1.logs = ns.logs := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge rest ih =>
    have hp : (applyCharge ns charge).1.logs = ns.logs := by cases charge <;> rfl
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | some error => simpa only [applyCharges, hc] using hp
      | none => simpa only [applyCharges, hc] using (ih paid).trans hp

@[simp] theorem prechargedStore_readSpan (name : String) (st : HostStore NearState) (args : List Value)
    (len ptr : UInt64) : readSpan (prechargedStore name st args) len ptr = readSpan st len ptr := by
  have hr := congrArg Prod.fst (applyCharges_abiFrame st.host (chargesBefore name st args))
  change (prechargedStore name st args).host.registers = st.host.registers at hr
  simp only [readSpan, hr]

@[simp] theorem prechargedStore_readU128Mem (name : String) (st : HostStore NearState) (args : List Value)
    (ptr : UInt64) : readU128Mem (prechargedStore name st args) ptr = readU128Mem st ptr := rfl

@[simp] theorem prechargedStore_readFunctionCallAction (name : String) (st : HostStore NearState) (args : List Value)
    (ml mp al ap amount gas : UInt64) :
    readFunctionCallAction? (prechargedStore name st args) ml mp al ap amount gas =
      readFunctionCallAction? st ml mp al ap amount gas := by
  simp only [readFunctionCallAction?, prechargedStore_getMemOrReg, prechargedStore_readU128Mem]

@[simp] theorem prechargedStore_config (name : String) (st : HostStore NearState) (args : List Value) :
    (prechargedStore name st args).host.config = st.host.config :=
  congrArg (fun frame => frame.2.1) (applyCharges_abiFrame st.host (chargesBefore name st args))

@[simp] theorem prechargedStore_promises (name : String) (st : HostStore NearState) (args : List Value) :
    (prechargedStore name st args).host.promises = st.host.promises :=
  congrArg (fun frame => frame.2.2) (applyCharges_abiFrame st.host (chargesBefore name st args))

@[simp] theorem prechargedStore_accountIdError (name : String) (st : HostStore NearState) (args : List Value)
    (len ptr : UInt64) : accountIdError (prechargedStore name st args) len ptr = accountIdError st len ptr := by
  simp only [accountIdError, prechargedStore_getMemOrReg, prechargedStore_config]

/-- Charging leaves the cryptographic oracles fixed. -/
theorem applyCharges_crypto (ns : NearState) (charges : List Charge) :
    (applyCharges ns charges).1.crypto = ns.crypto := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge rest ih =>
    have hp : (applyCharge ns charge).1.crypto = ns.crypto := by cases charge <;> rfl
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | some error => simpa only [applyCharges, hc] using hp
      | none => simpa only [applyCharges, hc] using (ih paid).trans hp

/-- The signature hosts' plans read only memory, registers and the oracles. -/
@[simp] theorem prechargedStore_cryptoPlan (name : String) (st : HostStore NearState) (args : List Value)
    (host : String) : cryptoPlan? host (prechargedStore name st args) args = cryptoPlan? host st args := by
  have hc : (prechargedStore name st args).host.crypto = st.host.crypto :=
    applyCharges_crypto st.host (chargesBefore name st args)
  simp only [cryptoPlan?, hc, prechargedStore_getMemOrReg, prechargedStore_readSpan]

/-- A log host's plan reads only logs, configuration, memory and registers. -/
@[simp] theorem prechargedStore_logPlan (name : String) (st : HostStore NearState) (args : List Value)
    (host : String) : logPlan host (prechargedStore name st args) args = logPlan host st args := by
  have hl : (prechargedStore name st args).host.logs = st.host.logs :=
    applyCharges_logs st.host (chargesBefore name st args)
  simp only [logPlan, hl, prechargedStore_config, prechargedStore_getMemOrReg, prechargedStore_readSpan]

@[simp] theorem prechargedStore_targetError (name : String) (st : HostStore NearState) (args : List Value) (index : Nat) :
    functionCallTargetError (prechargedStore name st args) index = functionCallTargetError st index := by
  simp only [functionCallTargetError, prechargedStore_promises]

@[simp] theorem prechargedStore_functionCallPlan_error (name : String) (st : HostStore NearState)
    (args : List Value) (input : FunctionCallInputs) (sir : Bool) :
    (functionCallPlan (prechargedStore name st args) input sir).error = (functionCallPlan st input sir).error := by
  have ht : functionCallTargetError (prechargedStore name st args) = functionCallTargetError st := by
    funext index
    exact prechargedStore_targetError name st args index
  unfold functionCallPlan
  simp only [prechargedStore_readU128Mem, prechargedStore_getMemOrReg, ht]
  repeat' (first | rfl | split)

@[simp] theorem prechargedStore_functionKeyPlan_error (name : String) (st : HostStore NearState)
    (args : List Value) (input : FunctionKeyInputs) (sir : Bool) :
    (functionKeyPlan (prechargedStore name st args) input sir).error = (functionKeyPlan st input sir).error := by
  unfold functionKeyPlan
  simp only [prechargedStore_readU128Mem, prechargedStore_getMemOrReg, prechargedStore_targetError, prechargedStore_config]
  repeat' (first | rfl | split)

/-- Same-receiver status affects sending fees, never key validation. -/
theorem functionKeyPlan_error_sir (st : HostStore NearState) (input : FunctionKeyInputs) (a b : Bool) :
    (functionKeyPlan st input a).error = (functionKeyPlan st input b).error := by
  unfold functionKeyPlan
  repeat' (first | rfl | split)

/-- A successful append must target a batch/callback, never a join or missing handle. -/
theorem appendPromiseAction_valid_target (st : HostStore NearState) (index : Nat) (action : PromiseAction)
    (promises : List NearPromise) (h : appendPromiseAction? st.host.promises index action = some promises) :
    (promiseReceiver? st index).isSome = true := by
  unfold appendPromiseAction? at h
  unfold promiseReceiver?
  cases hg : getPromise? st.host.promises index with
  | none => simp [hg] at h
  | some promise => cases promise <;> simp_all

/-- Compose a concrete public charge plan with the actual raw append. The plan
premise is discharged by per-ABI reservation lemmas, never by an outcome equation. -/
theorem appendPrechargedAction_reservationInvariant {weight : UInt64} (fees : ActionFees) (ethEnabled : Bool)
    (name : String) (st : HostStore NearState) (args : List Value) (index : UInt64) (action : PromiseAction)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore name st args)).2 = none)
    (hreservation : (promiseReceiver? st index.toNat).isSome = true →
      ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum =
        actionExecutionGas st.host.fees st.host.config.ethImplicitAccounts
          ((promiseReceiver? st index.toNat).getD []) action) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (appendPromiseActionResult name (prechargedStore name st args) index action weight) := by
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
  change HostResult.LiveSatisfies _ (appendPromiseActionResult name paid index action weight)
  unfold appendPromiseActionResult
  split
  · rename_i promises happend
    have ht := appendPromiseAction_valid_target paid index.toNat action promises happend
    have htarget : (promiseReceiver? st index.toNat).isSome = true := by
      simpa only [promiseReceiver?, hpromises] using ht
    have hcreated := appendPromiseAction_gas fees ethEnabled paid promises index.toNat action happend
    change ReservationInvariant fees ethEnabled _
    refine ⟨hfees.trans h.1, heth.trans h.2.1, ?_⟩
    change paid.host.gas.promises = promisesGas fees ethEnabled promises
    rw [hcreated]
    rw [hreservation htarget] at hgas
    have hbefore := h.2.2
    change st.host.gas.promises = promisesGas fees ethEnabled st.host.promises at hbefore
    simpa only [promiseReceiver?, hpromises, h.1, h.2.1, hbefore] using hgas
  · trivial

/-- Compose precharging, raw execution and all postprocessing. Concrete host
instances discharge the precharged raw-call premise below. -/
theorem metered_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat)
    (name : String) (fn : NearHostFn NearState)
    (hraw : ∀ st args, ReservationInvariant fees ethEnabled st.host →
      (applyCharges st.host (chargesBefore name st args)).2 = none →
      preInvokeError name (prechargedStore name st args) args = none →
      (prepareStorageCall name (prechargedStore name st args) args).2 = none →
      HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
        (fn.invoke (prepareStorageCall name (prechargedStore name st args) args).1 args)) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) (metered extra name fn) := by
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
          | none =>
            exact finishMeteredCall_reservationInvariant fees ethEnabled extra name ready args _
              (hraw st args h hc hp hs)

theorem prechargedCreateAccount_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_create_account" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionCreateAccountFn.invoke (prechargedStore "promise_batch_action_create_account" st args) args) := by
  unfold promiseBatchActionCreateAccountFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_createAccount_reservation
       exact ht)
    | split)

theorem meteredCreateAccount_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_create_account" promiseBatchActionCreateAccountFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedCreateAccount_reservationInvariant fees ethEnabled st args h hs

theorem prechargedStake_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_stake" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionStakeFn.invoke (prechargedStore "promise_batch_action_stake" st args) args) := by
  unfold promiseBatchActionStakeFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_stake_reservation
       exact ht)
    | split)

theorem meteredStake_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_stake" promiseBatchActionStakeFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedStake_reservationInvariant fees ethEnabled st args h hs

theorem prechargedFullAccessKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_add_key_with_full_access" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionAddKeyWithFullAccessFn.invoke (prechargedStore "promise_batch_action_add_key_with_full_access" st args) args) := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_fullAccessKey_reservation
       exact ht)
    | split)

theorem meteredFullAccessKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_add_key_with_full_access" promiseBatchActionAddKeyWithFullAccessFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedFullAccessKey_reservationInvariant fees ethEnabled st args h hs

theorem prechargedDeleteKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_delete_key" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionDeleteKeyFn.invoke (prechargedStore "promise_batch_action_delete_key" st args) args) := by
  unfold promiseBatchActionDeleteKeyFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_deleteKey_reservation
       exact ht)
    | split)

theorem meteredDeleteKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_delete_key" promiseBatchActionDeleteKeyFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedDeleteKey_reservationInvariant fees ethEnabled st args h hs

theorem prechargedDeleteAccount_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_delete_account" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionDeleteAccountFn.invoke (prechargedStore "promise_batch_action_delete_account" st args) args) := by
  unfold promiseBatchActionDeleteAccountFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_deleteAccount_reservation
       exact ht)
    | split)

theorem meteredDeleteAccount_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_delete_account" promiseBatchActionDeleteAccountFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedDeleteAccount_reservationInvariant fees ethEnabled st args h hs

theorem prechargedDeploy_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_deploy_contract" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionDeployContractFn.invoke (prechargedStore "promise_batch_action_deploy_contract" st args) args) := by
  unfold promiseBatchActionDeployContractFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_deploy_reservation
       · simp_all only [prechargedStore_getMemOrReg]
       · exact ht)
    | split)

theorem meteredDeploy_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_deploy_contract" promiseBatchActionDeployContractFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedDeploy_reservationInvariant fees ethEnabled st args h hs

theorem prechargedTransfer_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_transfer" st args)).2 = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionTransferFn.invoke (prechargedStore "promise_batch_action_transfer" st args) args) := by
  unfold promiseBatchActionTransferFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro ht
       apply chargesBefore_transfer_reservation
       · simp_all only [prechargedStore_readU128Mem]
       · exact ht)
    | split)

theorem meteredTransfer_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_transfer" promiseBatchActionTransferFn) := by
  apply metered_reservationInvariant
  intro st args h hs _ _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedTransfer_reservationInvariant fees ethEnabled st args h hs

theorem prechargedFunctionCall_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_function_call" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_action_function_call"
      (prechargedStore "promise_batch_action_function_call" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionFunctionCallFn.invoke (prechargedStore "promise_batch_action_function_call" st args) args) := by
  have he := preInvokeError_functionCall_valid hguard
  change (functionCallPlan (prechargedStore "promise_batch_action_function_call" st args)
    (functionCallInputs args 1 (some (argU64 args 0).toNat)) false).error = none at he
  rw [prechargedStore_functionCallPlan_error] at he
  have he' : (functionCallPlan st (functionCallInputs args 1 (some (argU64 args 0).toNat))
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none := by
    rw [functionCallPlan_error_sir st _ _ false]
    exact he
  obtain ⟨action, hread, hreserved⟩ := chargesBefore_functionCall_reservation st args he'
  unfold promiseBatchActionFunctionCallFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro _
       simp_all [argU64])
    | split)

theorem prechargedFunctionCallWeight_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_function_call" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_action_function_call"
      (prechargedStore "promise_batch_action_function_call" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionFunctionCallWeightFn.invoke (prechargedStore "promise_batch_action_function_call" st args) args) := by
  have he := preInvokeError_functionCall_valid hguard
  change (functionCallPlan (prechargedStore "promise_batch_action_function_call" st args)
    (functionCallInputs args 1 (some (argU64 args 0).toNat)) false).error = none at he
  rw [prechargedStore_functionCallPlan_error] at he
  have he' : (functionCallPlan st (functionCallInputs args 1 (some (argU64 args 0).toNat))
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none := by
    rw [functionCallPlan_error_sir st _ _ false]
    exact he
  obtain ⟨action, hread, hreserved⟩ := chargesBefore_functionCall_reservation st args he'
  unfold promiseBatchActionFunctionCallWeightFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro _
       simp_all [argU64])
    | split)

theorem meteredFunctionCall_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedFunctionCall_reservationInvariant fees ethEnabled st args h hs hg

theorem meteredFunctionCallWeight_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_function_call" promiseBatchActionFunctionCallWeightFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedFunctionCallWeight_reservationInvariant fees ethEnabled st args h hs hg

theorem prechargedFunctionKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_add_key_with_function_call" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_action_add_key_with_function_call"
      (prechargedStore "promise_batch_action_add_key_with_function_call" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionAddKeyWithFunctionCallFn.invoke (prechargedStore "promise_batch_action_add_key_with_function_call" st args) args) := by
  have he := preInvokeError_functionKey_valid _ _ hguard
  rw [prechargedStore_functionKeyPlan_error] at he
  have he' : (functionKeyPlan st (functionKeyInputs args)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none := by
    rw [functionKeyPlan_error_sir st _ _ false]
    exact he
  obtain ⟨pk, allowance, receiver, methods, hpk, ha, hr, hm, hreserved⟩ := chargesBefore_functionKey_reservation st args he'
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  dsimp only [disallowInView, checkPublicKey, checkAccountId]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro _
       simp_all [argU64])
    | split)

theorem meteredFunctionKey_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_add_key_with_function_call" promiseBatchActionAddKeyWithFunctionCallFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedFunctionKey_reservationInvariant fees ethEnabled st args h hs hg

@[simp] theorem prechargedStore_globalContractPlan_error (name : String) (st : HostStore NearState)
    (args : List Value) (byAccount : Bool) (target : Nat) (len ptr : UInt64) (sir : Bool) :
    (globalContractPlan (prechargedStore name st args) byAccount target len ptr sir).error =
      (globalContractPlan st byAccount target len ptr sir).error := by
  unfold globalContractPlan
  simp only [prechargedStore_getMemOrReg, prechargedStore_targetError, prechargedStore_config]
  repeat' (first | rfl | split)

theorem prechargedUseGlobalContract_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_use_global_contract" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_action_use_global_contract" (prechargedStore "promise_batch_action_use_global_contract" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionUseGlobalContractFn.invoke (prechargedStore "promise_batch_action_use_global_contract" st args) args) := by
  have he := preInvokeError_useGlobalContract_valid "promise_batch_action_use_global_contract" false rfl _ args
    (by simp [storageMutationPlan?]) (by decide) (by decide) (by decide) hguard
  rw [prechargedStore_globalContractPlan_error] at he
  have he' : (globalContractPlan st false (argU64 args 0).toNat (argU64 args 1) (argU64 args 2)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none := by
    rw [globalContractPlan_error_sir st _ _ _ _ _ false]
    exact he
  obtain ⟨bytes, hm, hreserved⟩ := chargesBefore_useGlobalContract_reservation st args he'
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro _
       simp_all [argU64])
    | split)

theorem meteredUseGlobalContract_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_use_global_contract" promiseBatchActionUseGlobalContractFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedUseGlobalContract_reservationInvariant fees ethEnabled st args h hs hg

theorem prechargedUseGlobalContractByAccountId_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (st : HostStore NearState) (args : List Value)
    (h : ReservationInvariant fees ethEnabled st.host)
    (hsuccess : (applyCharges st.host (chargesBefore "promise_batch_action_use_global_contract_by_account_id" st args)).2 = none)
    (hguard : preInvokeError "promise_batch_action_use_global_contract_by_account_id" (prechargedStore "promise_batch_action_use_global_contract_by_account_id" st args) args = none) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled)
      (promiseBatchActionUseGlobalContractByAccountIdFn.invoke (prechargedStore "promise_batch_action_use_global_contract_by_account_id" st args) args) := by
  have he := preInvokeError_useGlobalContract_valid "promise_batch_action_use_global_contract_by_account_id" true rfl _ args
    (by simp [storageMutationPlan?]) (by decide) (by decide) (by decide) hguard
  rw [prechargedStore_globalContractPlan_error] at he
  have he' : (globalContractPlan st true (argU64 args 0).toNat (argU64 args 1) (argU64 args 2)
      (sirOf st (promiseReceiver? st (argU64 args 0).toNat))).error = none := by
    rw [globalContractPlan_error_sir st _ _ _ _ _ false]
    exact he
  obtain ⟨bytes, hm, hreserved⟩ := chargesBefore_useGlobalContractByAccountId_reservation st args he'
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  dsimp only [disallowInView]
  repeat' (first
    | trivial
    | (apply appendPrechargedAction_reservationInvariant fees ethEnabled _ st _ _ _ h hsuccess
       intro _
       simp_all [argU64])
    | split)

theorem meteredUseGlobalContractByAccountId_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled)
      (metered extra "promise_batch_action_use_global_contract_by_account_id" promiseBatchActionUseGlobalContractByAccountIdFn) := by
  apply metered_reservationInvariant
  intro st args h hs hg _
  simp (disch := decide) only [prepareStorageCall_other]
  exact prechargedUseGlobalContractByAccountId_reservationInvariant fees ethEnabled st args h hs hg

end Wasm.Near
