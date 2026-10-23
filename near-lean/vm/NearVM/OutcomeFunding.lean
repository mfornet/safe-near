import NearVM.ExecutionFunding
import NearVM.SuccessInvariant

namespace Wasm.Near

/-- Successful VM observations account for all liquid funds and outgoing deposits. -/
def VMOutcome.Funded (balance : Nat) (outcome : VMOutcome) : Prop :=
  outcome.balance + receiptsDeposits outcome.receipts = balance + outcome.subsidizedAmount

theorem outcomeOfExecution_success_funding (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : Machine) (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (hfund : final.LiveHost (Funding (ctx.accountBalance + ctx.attachedDeposit) 0)) :
    (outcomeOfExecution ctx storage final error).Funded (ctx.accountBalance + ctx.attachedDeposit) := by
  have hf : Funding (ctx.accountBalance + ctx.attachedDeposit) 0 final.host :=
    outcomeOfExecution_success_live ctx storage final error hsuccess hfund
  unfold outcomeOfExecution at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · contradiction
  · cases hc : convertPromises final.host.promises with
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
  rcases runAttempt_cases cfg code codeSize method ctx storage fuel with
    ⟨host1, loadErr, burnt, e, profile, hload, hburnt, heq⟩ |
    ⟨host1, env, store, imports, valid, store', inst, entry, c, hload, hresolve, halloc, hinst,
      hstart, heq⟩
  · rw [heq]; intro hs; cases hs
  · rw [heq]
    have hf := applyCharges_fundingState (ctx.toNearState cfg storage) (loadingCharges codeSize)
    rw [hload] at hf
    have hbalance : host1.liquidFunds = ctx.accountBalance + ctx.attachedDeposit := by
      have hp := congrArg Prod.fst hf
      simpa only [fundingState, NearState.liquidFunds, VMContext.toNearState,
        promisesDeposits, promisesValue, List.map_nil, List.sum_nil, Nat.add_zero] using hp
    have hsubsidy : host1.subsidizedAmount = 0 := congrArg Prod.snd hf
    have hi := resolvedStart_funding hresolve halloc hinst hstart
    have hfund : MachineLiveInvariant (Funding (ctx.accountBalance + ctx.attachedDeposit) 0)
        (.next c) := by
      show ConfigLiveInvariant _ c
      rw [← hbalance, ← hsubsidy]
      exact hi
    have hfinal := runInitialized_liveFunding cfg.wasm fuel (.next c) hfund
    intro hs
    exact outcomeOfExecution_success_funding _ _ _ _ hs hfinal.live

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
