import NearVM.EncodingHosts

namespace Wasm.Near

/-- Legacy gas metering changes no encoding field on a live return. -/
theorem gasFn_encodingInvariant (opCost : Nat) :
    NearHostFn.PreservesLive EncodingInvariant (gasFn opCost) := by
  intro st args h
  unfold gasFn
  dsimp only
  split
  · rename_i n
    cases hc : st.host.gas.burn (n.toNat * opCost) with
    | mk gas error =>
      cases error with
      | some error => trivial
      | none => exact h
  · trivial

/-- A host the model rejects (`unsupportedRuntimeHost`) traps before any effect. -/
local macro "unsupported_encoding" : tactic =>
  `(tactic| (
    apply metered_raw_encodingInvariant
    intro st args hwf hs hguard _
    simp (disch := decide) only [prepareStorageCall_other]
    trivial))

/-- Every published metered host preserves strict policy and raw receipt encoding on
live returns. Terminal model/contract/gas errors carry no speculative guarantee. -/
theorem meteredHostFns_encodingInvariant
    (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : NearHostFn.PreservesLive EncodingInvariant entry.2 := by
  revert entry h
  simp only [meteredHostFns, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
  refine ⟨?_, gasFn_encodingInvariant _⟩
  simp only [nearHostFns, List.forall_mem_cons]
  and_intros
  · apply meteredNeutral_encodingInvariant
    · exact inputFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact readRegisterFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact registerLenFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact writeRegisterFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact valueReturnFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact storageWriteFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact storageReadFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact storageRemoveFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact storageHasKeyFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact panicMetered_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact panicUtf8Metered_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact currentAccountIdFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact predecessorAccountIdFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact signerAccountIdFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact attachedDepositFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact logUtf8Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact sha256Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact keccak256Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact signerAccountPkFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact blockIndexFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact blockIndexFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact blockTimestampFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact epochHeightFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact storageUsageFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact accountBalanceFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact accountLockedBalanceFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact prepaidGasFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact usedGasFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact validatorStakeFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact validatorTotalStakeFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact logUtf16Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact abortMetered_encodingFrame
  · intro st args hwf
    trivial
  · intro st args hwf
    trivial
  · intro st args hwf
    trivial
  · apply meteredNeutral_encodingInvariant
    · exact keccak512Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact ripemd160Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact ecrecoverFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact ed25519VerifyFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact p256VerifyFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact randomSeedFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact altBn128G1MultiexpFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact altBn128G1SumFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact altBn128PairingCheckFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381G1MultiexpFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381G2MultiexpFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381MapFpToG1Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381MapFp2ToG2Fn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381P1DecompressFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381P2DecompressFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381P1SumFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381P2SumFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact bls12381PairingCheckFn_encodingFrame
  · exact meteredCreate_encodingInvariant _
  · exact meteredThen_encodingInvariant _
  · exact meteredJoin_encodingInvariant _
  · exact meteredBatchCreate_encodingInvariant _
  · exact meteredBatchThen_encodingInvariant _
  · exact meteredActionCreateAccount_encodingInvariant _
  · exact meteredActionDeployContract_encodingInvariant _
  · exact meteredActionFunctionCall_encodingInvariant _
  · exact meteredActionFunctionCallWeight_encodingInvariant _
  · exact meteredActionTransfer_encodingInvariant _
  · exact meteredActionStake_encodingInvariant _
  · exact meteredActionAddKeyWithFullAccess_encodingInvariant _
  · exact meteredActionAddKeyWithFunctionCall_encodingInvariant _
  · exact meteredActionDeleteKey_encodingInvariant _
  · exact meteredActionDeleteAccount_encodingInvariant _
  · exact meteredActionDeployGlobalContract_encodingInvariant _
  · exact meteredActionDeployGlobalContractByAccountId_encodingInvariant _
  · exact meteredActionUseGlobalContract_encodingInvariant _
  · exact meteredActionUseGlobalContractByAccountId_encodingInvariant _
  · exact meteredYieldCreate_encodingInvariant _
  · exact meteredYieldResume_encodingInvariant _
  · apply meteredNeutral_encodingInvariant
    · exact promiseResultsCountFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact promiseResultFn_encodingFrame
  · apply meteredNeutral_encodingInvariant
    · exact promiseReturnFn_encodingFrame
  · exact meteredActionTransferToGasKey_encodingInvariant _
  · exact meteredActionAddGasKeyWithFullAccess_encodingInvariant _
  · exact meteredActionAddGasKeyWithFunctionCall_encodingInvariant _
  · unsupported_encoding
  · unsupported_encoding
  · unsupported_encoding
  · unsupported_encoding
  · apply meteredNeutral_encodingInvariant
    · exact chainIdFn_encodingFrame
  · simp

end Wasm.Near
