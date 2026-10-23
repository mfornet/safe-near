import NearVM.ResolvedReservations
import NearVM.OutcomeGas

namespace Wasm.Near

/-- Successful concrete VM execution backs every unit of used-but-unburnt gas
with a raw emitted receipt obligation. No host-preservation premise is assumed. -/
theorem runAttempt_success_gas_backing (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (runAttempt cfg code codeSize method ctx storage fuel).aborted = none →
    (runAttempt cfg code codeSize method ctx storage fuel).usedGas =
      (runAttempt cfg code codeSize method ctx storage fuel).burntGas +
        receiptsGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
          (runAttempt cfg code codeSize method ctx storage fuel).receipts := by
  rcases runAttempt_cases cfg code codeSize method ctx storage fuel with
    ⟨host1, loadErr, burnt, e, profile, hload, hburnt, heq⟩ |
    ⟨host1, env, store, imports, valid, store', inst, entry, c, hload, hresolve, halloc, hinst,
      hstart, heq⟩
  · rw [heq]; intro hs; cases hs
  · rw [heq]
    have hv := applyCharges_success_zero_reservation (ctx.toNearState cfg storage)
      (loadingCharges codeSize) (by rw [hload]) (by simp [loadingCharges, Charge.reservation])
    rw [hload] at hv
    have hhost : ReservationInvariant cfg.fees.actionFees cfg.wasm.ethImplicitAccounts host1 :=
      ReservationInvariant.of_view_eq hv (ctx.toNearState_reservationInvariant cfg storage)
    have hi := resolvedStart_reservationInvariant hresolve halloc hinst hstart hhost
    intro hs
    exact runInitialized_outcome_gas_backing cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
      cfg.wasm fuel (.next c) ctx storage hi hs

/-- Public receipt validation preserves the exact successful gas-backing law.
The statement covers arbitrary contract code, context, storage and fuel; success
excludes rejected, trapped and incomplete attempts through the executable API. -/
theorem run_success_gas_backing (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hsuccess : (run cfg code codeSize method ctx storage fuel).aborted = none) :
    (run cfg code codeSize method ctx storage fuel).usedGas =
      (run cfg code codeSize method ctx storage fuel).burntGas +
        receiptsGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
          (run cfg code codeSize method ctx storage fuel).receipts := by
  unfold run VMOutcome.checkReceipts at hsuccess ⊢
  split at hsuccess
  · rename_i hvalid
    rw [ite_eq_left hvalid]
    exact runAttempt_success_gas_backing cfg code codeSize method ctx storage fuel hsuccess
  · simp [VMOutcome.graphIssue] at hsuccess

/-- The receipt layer can recover the exact onward reservation from public gas
observations, without reading interpreter internals. -/
theorem run_success_receipts_gas_eq_reserved (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hsuccess : (run cfg code codeSize method ctx storage fuel).aborted = none) :
    receiptsGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
      (run cfg code codeSize method ctx storage fuel).receipts =
        (run cfg code codeSize method ctx storage fuel).usedGas -
          (run cfg code codeSize method ctx storage fuel).burntGas := by
  have h := run_success_gas_backing cfg code codeSize method ctx storage fuel hsuccess
  omega

/-- Burn plus all emitted receipt execution/prepaid obligations fits the actual
call budget. This supplies a concrete bound for receipt-level conservation. -/
theorem run_success_receipt_gas_budget (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hsuccess : (run cfg code codeSize method ctx storage fuel).aborted = none) :
    (run cfg code codeSize method ctx storage fuel).burntGas +
      receiptsGas cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
        (run cfg code codeSize method ctx storage fuel).receipts ≤ ctx.prepaidGas := by
  have he := run_success_gas_backing cfg code codeSize method ctx storage fuel hsuccess
  have hb := (run_gas_bounded cfg code codeSize method ctx storage fuel).2.1
  omega

end Wasm.Near
