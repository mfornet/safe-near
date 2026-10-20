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
  unfold runAttempt
  dsimp only
  split
  · intro hs; cases hs
  · cases hload : applyCharges (ctx.toNearState cfg storage)
      [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"] with
    | mk host loadError =>
      dsimp only
      cases loadError with
      | some error => intro hs; cases hs
      | none =>
        have hv := applyCharges_success_zero_reservation (ctx.toNearState cfg storage)
          [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
          (by rw [hload]) (by simp [Charge.reservation])
        rw [hload] at hv
        have hhost : ReservationInvariant cfg.fees.actionFees cfg.wasm.ethImplicitAccounts host :=
          ReservationInvariant.of_view_eq hv (ctx.toNearState_reservationInvariant cfg storage)
        dsimp only
        cases hexport : code.findExport method with
        | none => intro hs; cases hs
        | some entry =>
          dsimp only
          cases hsig : code.funcSig? entry with
          | none => intro hs; cases hs
          | some signature =>
            dsimp only
            split
            · intro hs; cases hs
            · cases hresolve : resolveMetered cfg code with
              | error message => intro hs; cases hs
              | ok env =>
                dsimp only
                split
                · intro hs; cases hs
                · rename_i config hinit
                  have hi := initResolvedConfig_reservationInvariant hresolve hinit hhost
                  intro hs
                  exact runInitialized_outcome_gas_backing cfg.fees.actionFees cfg.wasm.ethImplicitAccounts
                    cfg.wasm fuel config ctx storage hi hs

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
