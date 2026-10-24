import NearVM.NeutralReservations

namespace Wasm.Near

/-- Legacy instruction metering reserves no additional promise gas on success.
Gas exhaustion traps and discards the speculative counter instead. -/
theorem gasFn_reservationInvariant (fees : ActionFees) (ethEnabled : Bool) (opCost : Nat) :
    NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) (gasFn opCost) := by
  intro st args h
  unfold gasFn
  dsimp only
  split
  · rename_i n
    cases hc : st.host.gas.burn (n.toNat * opCost) with
    | mk gas error =>
      cases error with
      | some error => trivial
      | none =>
        have hp : (st.host.gas.burn (n.toNat * opCost)).1.promises = st.host.gas.promises := by
          have hs : (st.host.gas.burn (n.toNat * opCost)).2 = none := by rw [hc]
          simpa only [GasCounter.burn, Nat.sub_self, Nat.add_zero] using
            (GasCounter.deduct_success st.host.gas (n.toNat * opCost) (n.toNat * opCost) (Nat.le_refl _) hs).2.1
        rw [hc] at hp
        change ReservationInvariant fees ethEnabled _
        exact ⟨h.1, h.2.1, by
          change gas.promises = promisesGas fees ethEnabled st.host.promises
          rw [show gas.promises = st.host.gas.promises from hp]
          exact h.2.2⟩
  · trivial

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
/-- Every published metered host preserves exact raw receipt gas backing on
live returns. Terminal model/contract/gas errors carry no speculative guarantee. -/
theorem meteredHostFns_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact inputFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact readRegisterFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact registerLenFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact writeRegisterFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact valueReturnFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact storageWriteFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact storageReadFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact storageRemoveFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact storageHasKeyFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact panicMetered_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact panicUtf8Metered_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact currentAccountIdFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact predecessorAccountIdFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact signerAccountIdFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact attachedDepositFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact logUtf8Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact sha256Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact keccak256Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact signerAccountPkFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact blockIndexFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact blockIndexFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact blockTimestampFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact epochHeightFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact storageUsageFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact accountBalanceFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact accountLockedBalanceFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact prepaidGasFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact usedGasFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact validatorStakeFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact validatorTotalStakeFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact logUtf16Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact abortMetered_reservationView
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
      apply meteredNeutral_reservationInvariant
      · decide
      · exact keccak512Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact ripemd160Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact ecrecoverFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact ed25519VerifyFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact p256VerifyFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact randomSeedFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact altBn128G1MultiexpFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact altBn128G1SumFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact altBn128PairingCheckFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381G1MultiexpFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381G2MultiexpFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381MapFpToG1Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381MapFp2ToG2Fn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381P1DecompressFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381P2DecompressFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381P1SumFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381P2SumFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact bls12381PairingCheckFn_reservationView
    · cases h
      exact meteredCreate_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredThen_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredJoin_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredBatchCreate_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredBatchThen_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredCreateAccount_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredDeploy_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredFunctionCall_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredFunctionCallWeight_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredTransfer_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredStake_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredFullAccessKey_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredFunctionKey_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredDeleteKey_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredDeleteAccount_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredDeployGlobalContract_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredDeployGlobalContractByAccountId_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredUseGlobalContract_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredUseGlobalContractByAccountId_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredYieldCreate_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredYieldResume_reservationInvariant fees ethEnabled _
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact promiseResultsCountFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact promiseResultFn_reservationView
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact promiseReturnFn_reservationView
    · cases h
      exact meteredTransferToGasKey_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredAddGasKeyFull_reservationInvariant fees ethEnabled _
    · cases h
      exact meteredAddGasKeyFunction_reservationInvariant fees ethEnabled _
    · cases h
      apply metered_reservationInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_reservationInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_reservationInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply metered_reservationInvariant
      intro st args hwf hs hguard _
      simp (disch := decide) only [prepareStorageCall_other]
      trivial
    · cases h
      apply meteredNeutral_reservationInvariant
      · decide
      · exact chainIdFn_reservationView
  · subst entry
    exact gasFn_reservationInvariant fees ethEnabled _

end Wasm.Near
