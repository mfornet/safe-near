import NearVM.MeteredEncoding
import NearVM.NeutralReservations

namespace Wasm.Near

/-- The state carried between calls must retain both strict decoding and the
raw receipt payloads. Gas and local observation fields are independent. -/
def encodingFrame (ns : NearState) : Bool × List NearPromise :=
  (ns.config.validateActionMethodUtf8, ns.promises)

/-- Strict policy remains true and every receipt payload decodes without loss. -/
def EncodingInvariant (ns : NearState) : Prop :=
  ns.config.validateActionMethodUtf8 = true ∧ PromisesEncoding ns.promises

theorem EncodingInvariant.of_frame_eq {before after : NearState}
    (hf : encodingFrame after = encodingFrame before) (h : EncodingInvariant before) : EncodingInvariant after := by
  have hp := congrArg Prod.fst hf
  have hr := congrArg Prod.snd hf
  exact ⟨hp.trans h.1, by
    change after.promises = before.promises at hr
    rw [hr]
    exact h.2⟩


/-- Raw local-observation hosts preserve strict policy and receipt payloads.
Terminal traps may discard speculative state; catchable throws may not. -/
def HostPreservesEncodingFrame (fn : NearHostFn NearState) : Prop :=
  ∀ st args, HostResult.LiveSatisfies (fun ns => encodingFrame ns = encodingFrame st.host) (fn.invoke st args)

theorem checkedSetRegister_encodingFrame {st after : HostStore NearState} {register : UInt64} {bytes : List UInt8}
    (h : checkedSetRegister? st register bytes = some after) : encodingFrame after.host = encodingFrame st.host := by
  unfold checkedSetRegister? at h
  split_ifs at h <;> simp only [Option.some.injEq] at h
  all_goals subst after; rfl

theorem writeRegisterResult_encodingFrame (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (values : List Value) :
    HostResult.LiveSatisfies (fun ns => encodingFrame ns = encodingFrame st.host)
      (writeRegisterResult name st register bytes values) := by
  unfold writeRegisterResult
  split
  · exact checkedSetRegister_encodingFrame (by assumption)
  · trivial

theorem inputFn_encodingFrame : HostPreservesEncodingFrame inputFn := by
  intro st args
  unfold inputFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem readRegisterFn_encodingFrame : HostPreservesEncodingFrame readRegisterFn := by
  intro st args
  unfold readRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem registerLenFn_encodingFrame : HostPreservesEncodingFrame registerLenFn := by
  intro st args
  unfold registerLenFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem writeRegisterFn_encodingFrame : HostPreservesEncodingFrame writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem valueReturnFn_encodingFrame : HostPreservesEncodingFrame valueReturnFn := by
  intro st args
  unfold valueReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem storageWriteFn_encodingFrame : HostPreservesEncodingFrame storageWriteFn := by
  intro st args
  unfold storageWriteFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)
  all_goals aesop (add safe forward checkedSetRegister_encodingFrame)

theorem storageReadFn_encodingFrame : HostPreservesEncodingFrame storageReadFn := by
  intro st args
  unfold storageReadFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem storageRemoveFn_encodingFrame : HostPreservesEncodingFrame storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)
  all_goals aesop (add safe forward checkedSetRegister_encodingFrame)

theorem storageHasKeyFn_encodingFrame : HostPreservesEncodingFrame storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem currentAccountIdFn_encodingFrame : HostPreservesEncodingFrame currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem predecessorAccountIdFn_encodingFrame : HostPreservesEncodingFrame predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem signerAccountIdFn_encodingFrame : HostPreservesEncodingFrame signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem attachedDepositFn_encodingFrame : HostPreservesEncodingFrame attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem logUtf8Fn_encodingFrame : HostPreservesEncodingFrame logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem signerAccountPkFn_encodingFrame : HostPreservesEncodingFrame signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem blockIndexFn_encodingFrame : HostPreservesEncodingFrame blockIndexFn := by
  intro st args
  unfold blockIndexFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem blockTimestampFn_encodingFrame : HostPreservesEncodingFrame blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem epochHeightFn_encodingFrame : HostPreservesEncodingFrame epochHeightFn := by
  intro st args
  unfold epochHeightFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem storageUsageFn_encodingFrame : HostPreservesEncodingFrame storageUsageFn := by
  intro st args
  unfold storageUsageFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem accountBalanceFn_encodingFrame : HostPreservesEncodingFrame accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem accountLockedBalanceFn_encodingFrame : HostPreservesEncodingFrame accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem prepaidGasFn_encodingFrame : HostPreservesEncodingFrame prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem usedGasFn_encodingFrame : HostPreservesEncodingFrame usedGasFn := by
  intro st args
  unfold usedGasFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem logUtf16Fn_encodingFrame : HostPreservesEncodingFrame logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem randomSeedFn_encodingFrame : HostPreservesEncodingFrame randomSeedFn := by
  intro st args
  unfold randomSeedFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem chainIdFn_encodingFrame : HostPreservesEncodingFrame chainIdFn := by
  intro st args
  unfold chainIdFn contextRegisterFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem promiseYieldResumeFn_encodingFrame : HostPreservesEncodingFrame promiseYieldResumeFn := by
  intro st args
  unfold promiseYieldResumeFn
  dsimp only [disallowInView]
  repeat' (first | trivial | rfl | split)

theorem promiseResultsCountFn_encodingFrame : HostPreservesEncodingFrame promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem promiseResultFn_encodingFrame : HostPreservesEncodingFrame promiseResultFn := by
  intro st args
  unfold promiseResultFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem promiseReturnFn_encodingFrame : HostPreservesEncodingFrame promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem panicMetered_encodingFrame : HostPreservesEncodingFrame panicMetered := by
  intro st args
  trivial

theorem panicUtf8Metered_encodingFrame : HostPreservesEncodingFrame panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
    contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
    checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
    NearState.selectReturnValue, NearState.selectReturnPromise,
    NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
  repeat' (first
    | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
    | split)

theorem abortMetered_encodingFrame : HostPreservesEncodingFrame abortMetered := by
  intro st args
  trivial

end Wasm.Near
