import Skeleton.FundedInputFailures
import Skeleton.CanonicalReceiptSimulation
import Skeleton.CanonicalCost
import Skeleton.StorageFailureGas

/-! Actual pre-storage rejection under arbitrary canonical storage and gas. -/
namespace WNear.Skeleton.CanonicalInputFailures
open Wasm Wasm.Near NearInterface
open MeteredHosts FunctionalInvariant

private theorem matched_logs (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (observed : Observation) (result : NearInterface.StepResult M.Panic M.State M.Ret M.Promise)
    (h : Matches M ctx raw observed result) : observed.logs = result.logs := by
  cases result with
  | ok out => exact h.2.2.2.2.1
  | error failure => exact h.2.2.2.2.1

/-- The funded prefix proves the independent model's first rejection; actual
canonical startup/body replay transfers it to any original gas budget. -/
theorem execOn_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hp : PreparationLimits ctx.protocol) (hfail : FundedInputFailures.PreStorageRejected ctx)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have hhigh := FundedInputFailures.reference_matches gasBound ctx raw st 0
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hp.positive hfail
    (Nat.le_trans (by decide : 8 ≤ 16) (fuelFor_save _ _))
  change Matches (model gasBound) ctx raw.toFinset
    (ReceiptSimulation.referenceObservation ctx raw (FundedInputFailures.referenceBudget ctx raw 0))
    ((model gasBound).step ctx st ()) at hhigh
  have hl := matched_logs (model gasBound) ctx raw.toFinset _ _ hhigh
  have hr := CanonicalReceiptSimulation.execOn_replay ctx raw (FundedInputFailures.referenceBudget ctx raw 0)
    hmethod hwf hp.positive hp.minmax hp.maximum hp.types hp.functions hnodes hproof
  rcases hr with he | hg
  · left
    rw [he]
    exact hhigh
  · right
    rw [hl] at hg
    exact hg

/-- The general canonical budget covers the smaller pre-storage failure costs. -/
theorem saveEmptyCost_le_saveCost (ctx : Context) : saveEmptyCost ctx ≤ CanonicalCost.saveCost ctx := by
  unfold CanonicalCost.saveCost
  omega

/-- Sufficient canonical gas covers the actual early-failure prefix and bounds
its observed gas. These early checks require no trie or proof-size premises. -/
theorem execOn_matches_and_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hfail : FundedInputFailures.PreStorageRejected ctx)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  have hb := saveEmptyCost_le_saveCost ctx
  have hgas' : saveEmptyCost ctx ≤ ctx.gasLimit := hb.trans hgas
  by_cases hi : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length
  · have hc := inputFailureCost_le_saveEmptyCost ctx
    have hr := execOn_input_failure_bounded gasBound ctx raw st hmethod hp hi (hc.trans hgas')
    exact ⟨hr.1, hr.2.trans (hc.trans hb)⟩
  · by_cases hk : ctx.protocol.wasm.limits.maxLengthStorageKey < 1
    · have hr := execOn_key_failure_bounded gasBound ctx raw st hmethod hp (Nat.le_of_not_gt hi) hk hgas'
      exact ⟨hr.1, hr.2.trans hb⟩
    · have hv : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length := by
        rcases hfail with hi' | hk' | hv
        · exact False.elim (hi hi')
        · exact False.elim (hk hk')
        · exact hv
      have hr := execOn_value_failure_bounded gasBound ctx raw st hmethod hp
        (Nat.le_of_not_gt hi) (Nat.le_of_not_gt hk) hv hgas'
      exact ⟨hr.1, hr.2.trans hb⟩

end WNear.Skeleton.CanonicalInputFailures
