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

/-- A host the model rejects (`unsupportedRuntimeHost`) traps before any effect. -/
local macro "unsupported_reservation" : tactic =>
  `(tactic| (
    apply metered_reservationInvariant
    intro st args hwf hs hguard _
    simp (disch := decide) only [prepareStorageCall_other]
    trivial))

/-- Every published metered host preserves exact raw receipt gas backing on
live returns. Terminal model/contract/gas errors carry no speculative guarantee. -/
theorem meteredHostFns_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : NearHostFn.PreservesLive (ReservationInvariant fees ethEnabled) entry.2 := by
  revert entry h
  simp only [meteredHostFns, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
  refine ⟨?_, gasFn_reservationInvariant fees ethEnabled _⟩
  simp only [nearHostFns, List.forall_mem_cons]
  and_intros
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact inputFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact readRegisterFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact registerLenFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact writeRegisterFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact valueReturnFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact storageWriteFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact storageReadFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact storageRemoveFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact storageHasKeyFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact panicMetered_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact panicUtf8Metered_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact currentAccountIdFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact predecessorAccountIdFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact signerAccountIdFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact attachedDepositFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact logUtf8Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact sha256Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact keccak256Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact signerAccountPkFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact blockIndexFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact blockIndexFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact blockTimestampFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact epochHeightFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact storageUsageFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact accountBalanceFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact accountLockedBalanceFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact prepaidGasFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact usedGasFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact validatorStakeFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact validatorTotalStakeFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact logUtf16Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact abortMetered_reservationView
  · intro st args hwf
    trivial
  · intro st args hwf
    trivial
  · intro st args hwf
    trivial
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact keccak512Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact ripemd160Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact ecrecoverFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact ed25519VerifyFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact p256VerifyFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact randomSeedFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact altBn128G1MultiexpFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact altBn128G1SumFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact altBn128PairingCheckFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381G1MultiexpFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381G2MultiexpFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381MapFpToG1Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381MapFp2ToG2Fn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381P1DecompressFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381P2DecompressFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381P1SumFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381P2SumFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact bls12381PairingCheckFn_reservationView
  · exact meteredCreate_reservationInvariant fees ethEnabled _
  · exact meteredThen_reservationInvariant fees ethEnabled _
  · exact meteredJoin_reservationInvariant fees ethEnabled _
  · exact meteredBatchCreate_reservationInvariant fees ethEnabled _
  · exact meteredBatchThen_reservationInvariant fees ethEnabled _
  · exact meteredCreateAccount_reservationInvariant fees ethEnabled _
  · exact meteredDeploy_reservationInvariant fees ethEnabled _
  · exact meteredFunctionCall_reservationInvariant fees ethEnabled _
  · exact meteredFunctionCallWeight_reservationInvariant fees ethEnabled _
  · exact meteredTransfer_reservationInvariant fees ethEnabled _
  · exact meteredStake_reservationInvariant fees ethEnabled _
  · exact meteredFullAccessKey_reservationInvariant fees ethEnabled _
  · exact meteredFunctionKey_reservationInvariant fees ethEnabled _
  · exact meteredDeleteKey_reservationInvariant fees ethEnabled _
  · exact meteredDeleteAccount_reservationInvariant fees ethEnabled _
  · exact meteredDeployGlobalContract_reservationInvariant fees ethEnabled _
  · exact meteredDeployGlobalContractByAccountId_reservationInvariant fees ethEnabled _
  · exact meteredUseGlobalContract_reservationInvariant fees ethEnabled _
  · exact meteredUseGlobalContractByAccountId_reservationInvariant fees ethEnabled _
  · exact meteredYieldCreate_reservationInvariant fees ethEnabled _
  · exact meteredYieldResume_reservationInvariant fees ethEnabled _
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact promiseResultsCountFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact promiseResultFn_reservationView
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact promiseReturnFn_reservationView
  · exact meteredTransferToGasKey_reservationInvariant fees ethEnabled _
  · exact meteredAddGasKeyFull_reservationInvariant fees ethEnabled _
  · exact meteredAddGasKeyFunction_reservationInvariant fees ethEnabled _
  · unsupported_reservation
  · unsupported_reservation
  · unsupported_reservation
  · unsupported_reservation
  · apply meteredNeutral_reservationInvariant
    · decide
    · exact chainIdFn_reservationView
  · simp

end Wasm.Near
