import NearVM.MeteredCreationReservations

namespace Wasm.Near

/-- Raw local-observation hosts preserve all fields used by gas backing.
Terminal traps may discard speculative state; catchable throws may not. -/
def HostPreservesReservationView (fn : NearHostFn NearState) : Prop :=
  ∀ st args, HostResult.LiveSatisfies (fun ns => reservationView ns = reservationView st.host) (fn.invoke st args)

theorem checkedSetRegister_reservationView {st after : HostStore NearState} {register : UInt64} {bytes : List UInt8}
    (h : checkedSetRegister? st register bytes = some after) : reservationView after.host = reservationView st.host := by
  unfold checkedSetRegister? at h
  split_ifs at h <;> simp only [Option.some.injEq] at h
  all_goals subst after; rfl

theorem writeRegisterResult_reservationView (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (values : List Value) :
    HostResult.LiveSatisfies (fun ns => reservationView ns = reservationView st.host)
      (writeRegisterResult name st register bytes values) := by
  unfold writeRegisterResult
  split
  · exact checkedSetRegister_reservationView (by assumption)
  · trivial

theorem inputFn_reservationView : HostPreservesReservationView inputFn := by
  intro st args
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem readRegisterFn_reservationView : HostPreservesReservationView readRegisterFn := by
  intro st args
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem registerLenFn_reservationView : HostPreservesReservationView registerLenFn := by
  intro st args
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem writeRegisterFn_reservationView : HostPreservesReservationView writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem valueReturnFn_reservationView : HostPreservesReservationView valueReturnFn := by
  intro st args
  unfold valueReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem storageWriteFn_reservationView : HostPreservesReservationView storageWriteFn := by
  intro st args
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)
  all_goals aesop (add safe forward checkedSetRegister_reservationView)

theorem storageReadFn_reservationView : HostPreservesReservationView storageReadFn := by
  intro st args
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem storageRemoveFn_reservationView : HostPreservesReservationView storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)
  all_goals aesop (add safe forward checkedSetRegister_reservationView)

theorem storageHasKeyFn_reservationView : HostPreservesReservationView storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem currentAccountIdFn_reservationView : HostPreservesReservationView currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem predecessorAccountIdFn_reservationView : HostPreservesReservationView predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem signerAccountIdFn_reservationView : HostPreservesReservationView signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem attachedDepositFn_reservationView : HostPreservesReservationView attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem logUtf8Fn_reservationView : HostPreservesReservationView logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem signerAccountPkFn_reservationView : HostPreservesReservationView signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem blockIndexFn_reservationView : HostPreservesReservationView blockIndexFn := by
  intro st args
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem blockTimestampFn_reservationView : HostPreservesReservationView blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem epochHeightFn_reservationView : HostPreservesReservationView epochHeightFn := by
  intro st args
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem storageUsageFn_reservationView : HostPreservesReservationView storageUsageFn := by
  intro st args
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem accountBalanceFn_reservationView : HostPreservesReservationView accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem accountLockedBalanceFn_reservationView : HostPreservesReservationView accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem prepaidGasFn_reservationView : HostPreservesReservationView prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem usedGasFn_reservationView : HostPreservesReservationView usedGasFn := by
  intro st args
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem logUtf16Fn_reservationView : HostPreservesReservationView logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem randomSeedFn_reservationView : HostPreservesReservationView randomSeedFn := by
  intro st args
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem promiseResultsCountFn_reservationView : HostPreservesReservationView promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem promiseResultFn_reservationView : HostPreservesReservationView promiseResultFn := by
  intro st args
  unfold promiseResultFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem promiseReturnFn_reservationView : HostPreservesReservationView promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem panicMetered_reservationView : HostPreservesReservationView panicMetered := by
  intro st args
  trivial

theorem panicUtf8Metered_reservationView : HostPreservesReservationView panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_reservationView _ _ _ _ _
    | split)

theorem abortMetered_reservationView : HostPreservesReservationView abortMetered := by
  intro st args
  trivial

/-- These published host names create no onward execution/prepaid obligation. -/
def reservationNeutralNames : List String :=
  ["input", "read_register", "register_len", "write_register", "value_return", "storage_write", "storage_read", "storage_remove", "storage_has_key", "current_account_id", "predecessor_account_id", "signer_account_id", "attached_deposit", "log_utf8", "signer_account_pk", "block_index", "block_height", "block_timestamp", "epoch_height", "storage_usage", "account_balance", "account_locked_balance", "prepaid_gas", "used_gas", "log_utf16", "random_seed", "promise_results_count", "promise_result", "promise_return", "panic", "panic_utf8", "abort"]

@[simp] theorem storageValueCharges_reservation (st : HostStore NearState) (cost : String)
    (key : List UInt8) (fees : ActionFees) :
    ((storageValueCharges st cost key).map (fun charge => charge.reservation fees)).sum = 0 := by
  unfold storageValueCharges
  split
  · cases st.host.storage key <;> rfl
  · rfl

/-- Storage plans contain only local ext-cost burns, including old-value reads. -/
theorem storageMutationPlan_reservation (name : String) (st : HostStore NearState) (args : List Value)
    (plan : StorageMutationPlan) (fees : ActionFees) (h : storageMutationPlan? name st args = some plan) :
    ((plan.charges.map (fun charge => charge.reservation fees)).sum) = 0 := by
  have hext (cost : String) (count : Nat) : (Charge.ext cost count).reservation fees = 0 := rfl
  cases hk : getMemOrReg st (argU64 args 1) (argU64 args 0) <;>
    cases hkl : st.host.config.maxStorageKeyLen <;>
    cases hv : getMemOrReg st (argU64 args 3) (argU64 args 2) <;>
    cases hvl : st.host.config.maxStorageValueLen
  all_goals simp only [storageMutationPlan?, hk, hkl, hv, hvl, pure] at h
  all_goals repeat' (first | contradiction | split at h)
  all_goals have hp := Option.some.inj h
  all_goals cases hp
  all_goals simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, readSpan_reservation, storageValueCharges_reservation, hext, Nat.add_zero]

theorem chargesBefore_storage_reservation (name : String) (st : HostStore NearState) (args : List Value)
    (hname : name = "storage_write" ∨ name = "storage_remove") :
    ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum = 0 := by
  unfold chargesBefore
  split
  · rename_i plan he
    exact storageMutationPlan_reservation name st args plan st.host.fees he
  · rcases hname with h | h <;> subst name <;>
      simp [chargesBeforeUnvalidated, creationAccountArgs, Charge.reservation]

theorem chargesBefore_neutral_reservation (name : String) (st : HostStore NearState) (args : List Value)
    (hname : name ∈ reservationNeutralNames) :
    ((chargesBefore name st args).map (fun charge => charge.reservation st.host.fees)).sum = 0 := by
  simp only [reservationNeutralNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst name
  all_goals first
    | exact chargesBefore_storage_reservation _ _ _ (Or.inl rfl)
    | exact chargesBefore_storage_reservation _ _ _ (Or.inr rfl)
    | skip
  all_goals dsimp only [chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs, argU64,
    readMem, writeMem, writeReg, readSpan, utf8, utf16, Charge.reservation]
  all_goals simp
  all_goals repeat' (first | rfl | contradiction | constructor | split)

/-- Local precharges and raw local hosts compose with the post-call theorem. -/
theorem meteredNeutral_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (extra : Nat)
    (name : String) (fn : NearHostFn NearState) (hname : name ∈ reservationNeutralNames)
    (hfn : HostPreservesReservationView fn) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) (metered extra name fn) := by
  apply metered_reservationInvariant
  intro st args h hs _ hext
  have hv := applyCharges_success_zero_reservation st.host (chargesBefore name st args) hs
    (chargesBefore_neutral_reservation name st args hname)
  have hp : ReservationInvariant fees ethEnabled (prechargedStore name st args).host :=
    ReservationInvariant.of_view_eq hv h
  let ready := (prepareStorageCall name (prechargedStore name st args) args).1
  have hview : reservationView ready.host = reservationView (prechargedStore name st args).host :=
    Prod.ext rfl (prepareStorageCall_success_promisesGas _ _ _ hext)
  have hp : ReservationInvariant fees ethEnabled ready.host := ReservationInvariant.of_view_eq hview hp
  have hr := hfn ready args
  cases he : fn.invoke ready args <;>
    rw [he] at hr <;> first | trivial | exact ReservationInvariant.of_view_eq hr hp

end Wasm.Near
