import NearVM.ExecutionFunding

namespace Wasm.Near

/-- Successful VM observations account for all liquid funds and outgoing deposits. -/
def VMOutcome.Funded (balance : Nat) (outcome : VMOutcome) : Prop :=
  outcome.balance + receiptsDeposits outcome.receipts = balance + outcome.subsidizedAmount

theorem outcomeOfExecution_success_funding (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : SmallStep.Config NearState) (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (hfund : final.LiveHost (Funding (ctx.accountBalance + ctx.attachedDeposit) 0)) :
    (outcomeOfExecution ctx storage final error).Funded (ctx.accountBalance + ctx.attachedDeposit) := by
  unfold outcomeOfExecution at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · contradiction
  · rename_i habort
    have hf : Funding (ctx.accountBalance + ctx.attachedDeposit) 0 final.store.wasm.host := by
      cases he : final.expr with
      | running thread => simpa only [SmallStep.Config.LiveHost, he] using hfund
      | done values => simpa only [SmallStep.Config.LiveHost, he] using hfund
      | trapped reason =>
        cases error <;> simp [he] at habort
    cases hc : convertPromises final.store.wasm.host.promises with
    | none => simp [hc, VMOutcome.graphIssue] at hsuccess
    | some graph =>
      simp only [hc] at hsuccess ⊢
      split at hsuccess
      · simp [VMOutcome.graphIssue] at hsuccess
      · unfold VMOutcome.Funded
        dsimp only
        rw [convertPromises_deposits _ graph hc]
        simpa only [Funding, NearState.liquidFunds, Nat.add_zero] using hf

/-- No contract-specific assumptions: actual successful VM attempts conserve
initial liquid balance plus any explicitly recorded subsidy. -/
theorem runAttempt_success_funding (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (runAttempt cfg code codeSize method ctx storage fuel).aborted = none →
    (runAttempt cfg code codeSize method ctx storage fuel).Funded (ctx.accountBalance + ctx.attachedDeposit) := by
  unfold runAttempt
  dsimp only
  split
  · intro hs; cases hs
  · cases hload : applyCharges (ctx.toNearState cfg storage)
      [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"] with
    | mk host loadError =>
      have hf := applyCharges_fundingState (ctx.toNearState cfg storage)
        [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
      rw [hload] at hf
      have hbalance : host.liquidFunds = ctx.accountBalance + ctx.attachedDeposit := by
        have hp := congrArg Prod.fst hf
        simpa only [fundingState, NearState.liquidFunds, VMContext.toNearState,
          promisesDeposits, promisesValue, List.map_nil, List.sum_nil, Nat.add_zero] using hp
      have hsubsidy : host.subsidizedAmount = 0 := congrArg Prod.snd hf
      dsimp only
      cases loadError with
      | some error => intro hs; cases hs
      | none =>
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
                  have hi := initResolvedConfig_funding hresolve hinit
                  have hfund : ConfigLiveInvariant (Funding (ctx.accountBalance + ctx.attachedDeposit) 0) config := by
                    simpa only [hbalance, hsubsidy] using hi
                  have hfinal := runInitialized_liveFunding cfg.wasm fuel config hfund
                  intro hs
                  exact outcomeOfExecution_success_funding _ _ _ _ hs hfinal.2

/-- Receipt validation cannot turn an invalid graph into a successful outcome. -/
theorem run_success_funding (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat)
    (hsuccess : (run cfg code codeSize method ctx storage fuel).aborted = none) :
    (run cfg code codeSize method ctx storage fuel).Funded (ctx.accountBalance + ctx.attachedDeposit) := by
  unfold run VMOutcome.checkReceipts at hsuccess ⊢
  split at hsuccess
  · rename_i hvalid
    rw [ite_eq_left hvalid]
    exact runAttempt_success_funding cfg code codeSize method ctx storage fuel hsuccess
  · simp [VMOutcome.graphIssue] at hsuccess

end Wasm.Near
