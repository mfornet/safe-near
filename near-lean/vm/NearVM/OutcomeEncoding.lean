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
  rcases runAttempt_cases cfg code codeSize method ctx storage fuel with
    ⟨host1, loadErr, burnt, e, profile, hload, hburnt, heq⟩ |
    ⟨host1, env, store, imports, valid, store', inst, entry, c, hload, hresolve, halloc, hinst,
      hstart, heq⟩
  · rw [heq]; intro hs; cases hs
  · rw [heq]
    have hv := applyCharges_encodingFrame (ctx.toNearState cfg storage) (loadingCharges codeSize)
    rw [hload] at hv
    have hhost : EncodingInvariant host1 :=
      EncodingInvariant.of_frame_eq hv (ctx.toNearState_encodingInvariant cfg storage hpolicy)
    have hi := resolvedStart_encodingInvariant hresolve halloc hinst hstart hhost
    intro hs
    exact runInitialized_outcome_encoding cfg.wasm fuel (.next c) ctx storage hi hs

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
