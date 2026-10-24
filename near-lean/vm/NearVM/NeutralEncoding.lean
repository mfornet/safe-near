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

/-- Unfold a register/context host and close each branch: frames are unchanged. -/
local macro "neutral_encoding_tac" : tactic => `(tactic| (
    dsimp only [disallowInView, accountIdRegisterFn, publicKeyRegisterFn, contextU64Fn,
      contextU128MemFn, writeU128, writeMemBytes, appendLogResult, checkDataLimit,
      checkAccountId, checkPublicKey, NearState.setRegister, trapWith,
      NearState.selectReturnValue, NearState.selectReturnPromise,
      NearState.setStorage, NearState.removeStorage, NearState.invalidateIterators]
    repeat' (first
      | trivial | rfl | exact writeRegisterResult_encodingFrame _ _ _ _ _
      | split)))

theorem inputFn_encodingFrame : HostPreservesEncodingFrame inputFn := by
  intro st args
  unfold inputFn
  neutral_encoding_tac

theorem readRegisterFn_encodingFrame : HostPreservesEncodingFrame readRegisterFn := by
  intro st args
  unfold readRegisterFn
  neutral_encoding_tac

theorem registerLenFn_encodingFrame : HostPreservesEncodingFrame registerLenFn := by
  intro st args
  unfold registerLenFn
  neutral_encoding_tac

theorem writeRegisterFn_encodingFrame : HostPreservesEncodingFrame writeRegisterFn := by
  intro st args
  unfold writeRegisterFn
  neutral_encoding_tac

theorem valueReturnFn_encodingFrame : HostPreservesEncodingFrame valueReturnFn := by
  intro st args
  unfold valueReturnFn
  neutral_encoding_tac

theorem storageWriteFn_encodingFrame : HostPreservesEncodingFrame storageWriteFn := by
  intro st args
  unfold storageWriteFn
  neutral_encoding_tac
  all_goals aesop (add safe forward checkedSetRegister_encodingFrame)

theorem storageReadFn_encodingFrame : HostPreservesEncodingFrame storageReadFn := by
  intro st args
  unfold storageReadFn
  neutral_encoding_tac

theorem storageRemoveFn_encodingFrame : HostPreservesEncodingFrame storageRemoveFn := by
  intro st args
  unfold storageRemoveFn
  neutral_encoding_tac
  all_goals aesop (add safe forward checkedSetRegister_encodingFrame)

theorem storageHasKeyFn_encodingFrame : HostPreservesEncodingFrame storageHasKeyFn := by
  intro st args
  unfold storageHasKeyFn
  neutral_encoding_tac

theorem currentAccountIdFn_encodingFrame : HostPreservesEncodingFrame currentAccountIdFn := by
  intro st args
  unfold currentAccountIdFn
  neutral_encoding_tac

theorem predecessorAccountIdFn_encodingFrame : HostPreservesEncodingFrame predecessorAccountIdFn := by
  intro st args
  unfold predecessorAccountIdFn
  neutral_encoding_tac

theorem signerAccountIdFn_encodingFrame : HostPreservesEncodingFrame signerAccountIdFn := by
  intro st args
  unfold signerAccountIdFn
  neutral_encoding_tac

theorem attachedDepositFn_encodingFrame : HostPreservesEncodingFrame attachedDepositFn := by
  intro st args
  unfold attachedDepositFn
  neutral_encoding_tac

theorem logUtf8Fn_encodingFrame : HostPreservesEncodingFrame logUtf8Fn := by
  intro st args
  unfold logUtf8Fn
  neutral_encoding_tac

theorem signerAccountPkFn_encodingFrame : HostPreservesEncodingFrame signerAccountPkFn := by
  intro st args
  unfold signerAccountPkFn
  neutral_encoding_tac

theorem blockIndexFn_encodingFrame : HostPreservesEncodingFrame blockIndexFn := by
  intro st args
  unfold blockIndexFn
  neutral_encoding_tac

theorem blockTimestampFn_encodingFrame : HostPreservesEncodingFrame blockTimestampFn := by
  intro st args
  unfold blockTimestampFn
  neutral_encoding_tac

theorem epochHeightFn_encodingFrame : HostPreservesEncodingFrame epochHeightFn := by
  intro st args
  unfold epochHeightFn
  neutral_encoding_tac

theorem storageUsageFn_encodingFrame : HostPreservesEncodingFrame storageUsageFn := by
  intro st args
  unfold storageUsageFn
  neutral_encoding_tac

theorem accountBalanceFn_encodingFrame : HostPreservesEncodingFrame accountBalanceFn := by
  intro st args
  unfold accountBalanceFn
  neutral_encoding_tac

theorem accountLockedBalanceFn_encodingFrame : HostPreservesEncodingFrame accountLockedBalanceFn := by
  intro st args
  unfold accountLockedBalanceFn
  neutral_encoding_tac

theorem prepaidGasFn_encodingFrame : HostPreservesEncodingFrame prepaidGasFn := by
  intro st args
  unfold prepaidGasFn
  neutral_encoding_tac

theorem usedGasFn_encodingFrame : HostPreservesEncodingFrame usedGasFn := by
  intro st args
  unfold usedGasFn
  neutral_encoding_tac

theorem logUtf16Fn_encodingFrame : HostPreservesEncodingFrame logUtf16Fn := by
  intro st args
  unfold logUtf16Fn
  neutral_encoding_tac

theorem randomSeedFn_encodingFrame : HostPreservesEncodingFrame randomSeedFn := by
  intro st args
  unfold randomSeedFn
  neutral_encoding_tac

theorem ecrecoverFn_encodingFrame : HostPreservesEncodingFrame ecrecoverFn := by
  intro st args
  unfold ecrecoverFn missingOracle
  neutral_encoding_tac

theorem ed25519VerifyFn_encodingFrame : HostPreservesEncodingFrame ed25519VerifyFn := by
  intro st args
  unfold ed25519VerifyFn missingOracle
  neutral_encoding_tac

theorem validatorStakeFn_encodingFrame : HostPreservesEncodingFrame validatorStakeFn := by
  intro st args
  unfold validatorStakeFn
  neutral_encoding_tac

theorem validatorTotalStakeFn_encodingFrame : HostPreservesEncodingFrame validatorTotalStakeFn := by
  intro st args
  unfold validatorTotalStakeFn
  neutral_encoding_tac

theorem sha256Fn_encodingFrame : HostPreservesEncodingFrame sha256Fn := by
  intro st args
  unfold sha256Fn digestFn
  neutral_encoding_tac

theorem keccak256Fn_encodingFrame : HostPreservesEncodingFrame keccak256Fn := by
  intro st args
  unfold keccak256Fn digestFn
  neutral_encoding_tac

theorem keccak512Fn_encodingFrame : HostPreservesEncodingFrame keccak512Fn := by
  intro st args
  unfold keccak512Fn digestFn
  neutral_encoding_tac

theorem ripemd160Fn_encodingFrame : HostPreservesEncodingFrame ripemd160Fn := by
  intro st args
  unfold ripemd160Fn digestFn
  neutral_encoding_tac

theorem promiseResultsCountFn_encodingFrame : HostPreservesEncodingFrame promiseResultsCountFn := by
  intro st args
  unfold promiseResultsCountFn
  neutral_encoding_tac

theorem promiseResultFn_encodingFrame : HostPreservesEncodingFrame promiseResultFn := by
  intro st args
  unfold promiseResultFn
  neutral_encoding_tac

theorem promiseReturnFn_encodingFrame : HostPreservesEncodingFrame promiseReturnFn := by
  intro st args
  unfold promiseReturnFn
  neutral_encoding_tac

theorem panicMetered_encodingFrame : HostPreservesEncodingFrame panicMetered := by
  intro st args
  trivial

theorem panicUtf8Metered_encodingFrame : HostPreservesEncodingFrame panicUtf8Metered := by
  intro st args
  unfold panicUtf8Metered
  neutral_encoding_tac

theorem abortMetered_encodingFrame : HostPreservesEncodingFrame abortMetered := by
  intro st args
  trivial

end Wasm.Near
