import NearVM.EncodingHosts

namespace Wasm.Near

/-- Legacy gas metering changes no encoding field on a live return. -/
theorem gasFn_encodingInvariant : NearHostFn.PreservesLive EncodingInvariant gasFn := by
  intro st args h
  unfold gasFn
  dsimp only
  split
  · rename_i n
    cases hc : st.host.gas.burn n.toNat with
    | mk gas error =>
      cases error with
      | some error => trivial
      | none => exact h
  · trivial

set_option maxHeartbeats 2000000 in
/-- Every published metered host preserves strict policy and raw receipt encoding on
live returns. Terminal model/contract/gas errors carry no speculative guarantee. -/
theorem meteredHostFns_encodingInvariant
    (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : NearHostFn.PreservesLive EncodingInvariant entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact inputFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact readRegisterFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact registerLenFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact writeRegisterFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact valueReturnFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact storageWriteFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact storageReadFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact storageRemoveFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact storageHasKeyFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact panicMetered_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact panicUtf8Metered_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact currentAccountIdFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact predecessorAccountIdFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact signerAccountIdFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact attachedDepositFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact logUtf8Fn_encodingFrame
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact signerAccountPkFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact blockIndexFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact blockIndexFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact blockTimestampFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact epochHeightFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact storageUsageFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact accountBalanceFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact accountLockedBalanceFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact prepaidGasFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact usedGasFn_encodingFrame
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact logUtf16Fn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact abortMetered_encodingFrame
    · cases h
      intro st args hwf
      trivial
    · cases h
      intro st args hwf
      trivial
    · cases h
      intro st args hwf
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact randomSeedFn_encodingFrame
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      exact meteredCreate_encodingInvariant _
    · cases h
      exact meteredThen_encodingInvariant _
    · cases h
      exact meteredJoin_encodingInvariant _
    · cases h
      exact meteredBatchCreate_encodingInvariant _
    · cases h
      exact meteredBatchThen_encodingInvariant _
    · cases h
      exact meteredActionCreateAccount_encodingInvariant _
    · cases h
      exact meteredActionDeployContract_encodingInvariant _
    · cases h
      exact meteredActionFunctionCall_encodingInvariant _
    · cases h
      exact meteredActionFunctionCallWeight_encodingInvariant _
    · cases h
      exact meteredActionTransfer_encodingInvariant _
    · cases h
      exact meteredActionStake_encodingInvariant _
    · cases h
      exact meteredActionAddKeyWithFullAccess_encodingInvariant _
    · cases h
      exact meteredActionAddKeyWithFunctionCall_encodingInvariant _
    · cases h
      exact meteredActionDeleteKey_encodingInvariant _
    · cases h
      exact meteredActionDeleteAccount_encodingInvariant _
    · cases h
      exact meteredActionDeployGlobalContract_encodingInvariant _
    · cases h
      exact meteredActionDeployGlobalContractByAccountId_encodingInvariant _
    · cases h
      exact meteredActionUseGlobalContract_encodingInvariant _
    · cases h
      exact meteredActionUseGlobalContractByAccountId_encodingInvariant _
    · cases h
      exact meteredYieldCreate_encodingInvariant _
    · cases h
      exact meteredYieldResume_encodingInvariant _
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact promiseResultsCountFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact promiseResultFn_encodingFrame
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact promiseReturnFn_encodingFrame
    · cases h
      exact meteredActionTransferToGasKey_encodingInvariant _
    · cases h
      exact meteredActionAddGasKeyWithFullAccess_encodingInvariant _
    · cases h
      exact meteredActionAddGasKeyWithFunctionCall_encodingInvariant _
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_raw_encodingInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply meteredNeutral_encodingInvariant
      · exact chainIdFn_encodingFrame
  · subst entry
    exact gasFn_encodingInvariant

end Wasm.Near
