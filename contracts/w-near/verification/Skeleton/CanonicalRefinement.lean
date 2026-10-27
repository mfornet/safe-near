import Skeleton.CanonicalObservation
import Skeleton.CanonicalReceiptSimulation
import Skeleton.ModelSafety
import Skeleton.CanonicalBounded
import Skeleton.InvalidMethod

/-! Model-level arbitrary-gas agreement for general canonical storage.
Node-zero exclusion and actual fetched-state proof acceptance stay explicit. -/
namespace WNear.Skeleton.CanonicalRefinement
open Wasm Wasm.Near NearInterface
open FunctionalInvariant MeteredHosts

private theorem matched_logs (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (observed : Observation) (result : NearInterface.StepResult M.Panic M.State M.Ret M.Promise)
    (h : Matches M ctx raw observed result) : observed.logs = result.logs := by
  cases result with
  | ok out => exact h.2.2.2.2.1
  | error failure => exact h.2.2.2.2.1

/-- General canonical execution at any original gas budget either matches the
independent model or runs out of gas with rollback and a model-log prefix.
Both fresh and replacing cells and both stake outcomes are covered. -/
theorem execOn_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have hhigh := CanonicalObservation.reference_matches gasBound ctx raw st 0
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hwf hrepresented hp.positive hm
    (fuelFor_save _ _) hread hnodes hroom hproof
  change Matches (model gasBound) ctx raw.toFinset
    (ReceiptSimulation.referenceObservation ctx raw (CanonicalObservation.referenceBudget ctx raw 0))
    ((model gasBound).step ctx st ()) at hhigh
  have hl := matched_logs (model gasBound) ctx raw.toFinset _ _ hhigh
  have hr := CanonicalReceiptSimulation.execOn_replay ctx raw (CanonicalObservation.referenceBudget ctx raw 0)
    hmethod hwf hp.positive hp.minmax hp.maximum hp.types hp.functions hnodes hproof
  rcases hr with he | hg
  · left
    rw [he]
    exact hhigh
  · right
    rw [hl] at hg
    exact hg

/-- The same model-level alternative for the exact finite-set runtime. -/
theorem nearRuntime_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw)
    (hrepresented : (model gasBound).Represents raw st)
    (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : CanonicalReady.ProofAccepted ctx raw.toList) :
    Matches (model gasBound) ctx raw (Near.Boundary.nearRuntime.exec code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.nearRuntime.exec code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw (Near.Boundary.nearRuntime.exec code raw ctx) ∧
      (Near.Boundary.nearRuntime.exec code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have h := execOn_matches_or_gas gasBound ctx raw.toList st hmethod
    (by simpa only [Finset.toList_toFinset] using hwf)
    (by simpa only [Finset.toList_toFinset] using hrepresented)
    hp hm hread hnodes hroom hproof
  simpa only [Near.Boundary.nearRuntime, Finset.toList_toFinset] using h

/-- The independent walking model with its original-data canonical gas bound. -/
def boundedModel : ContractModel := model (fun ctx _ _ => CanonicalCost.saveCost ctx)

/-- Every pointwise `Refines` clause for arbitrary canonical storage and
accepted resources. No empty-base or selected-key restriction remains;
nonzero nodes, actual proof acceptance and native arithmetic room are explicit. -/
theorem nearRuntime_refinement_clauses
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hwf : ctx.WF raw) (hrepresented : boundedModel.Represents raw st)
    (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : CanonicalReady.ProofAccepted ctx raw.toList) :
    let M := boundedModel
    let r := Near.Boundary.nearRuntime.exec code raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (∀ call, M.Parses ctx.method ctx.args call →
      (M.gas ctx st call ≤ ctx.gasLimit →
        Matches M ctx raw r (M.step ctx st call) ∧ r.usedGas ≤ M.gas ctx st call) ∧
      (Matches M ctx raw r (M.step ctx st call) ∨
        (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs <+: (M.step ctx st call).logs))) ∧
    ((¬ ∃ call, M.Parses ctx.method ctx.args call) → RolledBack ctx raw r) := by
  dsimp only
  by_cases hmethod : ctx.method = "save"
  · have halt := nearRuntime_matches_or_gas (fun ctx _ _ => CanonicalCost.saveCost ctx)
      ctx raw st hmethod hwf hrepresented hp hm hread hnodes hroom hproof
    refine ⟨?_, ?_, ?_⟩
    · rcases halt with hmatch | hg
      · exact matches_modelStep_no_issue (fun ctx _ _ => CanonicalCost.saveCost ctx) ctx raw st _ hmatch
      · intro msg he
        rw [hg.1] at he
        cases he
    · intro call hparse
      cases call
      refine ⟨?_, halt⟩
      intro hgas
      have hb := CanonicalBounded.execOn_matches_and_gas (fun ctx _ _ => CanonicalCost.saveCost ctx)
        ctx raw.toList st (by simpa only [Finset.toList_toFinset] using hwf)
        (by simpa only [boundedModel, Finset.toList_toFinset] using hrepresented)
        hmethod hp hm hnodes hread hroom hgas hproof
      simpa only [boundedModel, model, Near.Boundary.nearRuntime, Finset.toList_toFinset] using hb
    · intro hn
      exact False.elim (hn ⟨(), hmethod⟩)
  · have hn : ¬ ∃ call, boundedModel.Parses ctx.method ctx.args call := by
      rintro ⟨call, hparse⟩
      exact hmethod hparse
    have hi := nearRuntime_invalid_method (fun ctx _ _ => CanonicalCost.saveCost ctx) ctx raw hn
    refine ⟨hi.2, ?_, fun _ => hi.1⟩
    intro call hparse
    exact False.elim (hn ⟨call, hparse⟩)

end WNear.Skeleton.CanonicalRefinement
