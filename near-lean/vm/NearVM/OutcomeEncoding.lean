import NearVM.ExecutionEncoding

namespace Wasm.Near

/-- Successful execution under the runtime policy produces byte-preserving
receipt receiver/method encodings. No final-state decoding premise is assumed. -/
theorem runAttempt_success_encoding (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hpolicy : ctx.validateActionMethodUtf8 = true) :
    (runAttempt cfg code codeSize method ctx storage fuel).aborted = none →
    ∀ spec ∈ (runAttempt cfg code codeSize method ctx storage fuel).receipts,
      ReceiptEncoding spec.receiverId spec.actions := by
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
        have hv := applyCharges_encodingFrame (ctx.toNearState cfg storage)
          [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
        rw [hload] at hv
        have hhost : EncodingInvariant host :=
          EncodingInvariant.of_frame_eq hv (ctx.toNearState_encodingInvariant cfg storage hpolicy)
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
                  have hi := initResolvedConfig_encodingInvariant hresolve hinit hhost
                  intro hs
                  exact runInitialized_outcome_encoding cfg.wasm fuel config ctx storage hi hs

/-- The public VM receipt check retains encoding witnesses derived from the
actual strict-policy execution, for arbitrary code, storage and interpreter fuel. -/
theorem run_success_receipt_encoding (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hpolicy : ctx.validateActionMethodUtf8 = true)
    (hsuccess : (run cfg code codeSize method ctx storage fuel).aborted = none) :
    ∀ spec ∈ (run cfg code codeSize method ctx storage fuel).receipts,
      ReceiptEncoding spec.receiverId spec.actions := by
  unfold run VMOutcome.checkReceipts at hsuccess ⊢
  split at hsuccess
  · rename_i hvalid
    rw [ite_eq_left hvalid]
    exact runAttempt_success_encoding cfg code codeSize method ctx storage fuel hpolicy hsuccess
  · simp [VMOutcome.graphIssue] at hsuccess

end Wasm.Near
