import Skeleton.CanonicalRefinement
import Skeleton.CanonicalInputFailures
import Skeleton.CanonicalOutputFailures
import Skeleton.CanonicalFailureBounded
import Skeleton.CanonicalArithmetic

/-! General canonical pointwise refinement across every resource branch.
Native usage room follows from shared WF and a protocol-level growth bound
only where value validation accepts; rejected inputs need no write-room premise. -/
namespace WNear.Skeleton.CanonicalAllLimits
open Wasm Wasm.Near NearInterface
open FunctionalInvariant CanonicalRefinement

/-- All resource branches agree with the model or return a rollback gas abort,
for any original gas budget, over arbitrary canonical storage. -/
theorem execOn_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hp : PreparationLimits ctx.protocol) (hgrowth : CanonicalArithmetic.GrowthRoom ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  by_cases hpre : FundedInputFailures.PreStorageRejected ctx
  · exact CanonicalInputFailures.execOn_matches_or_gas gasBound ctx raw st hmethod hwf hp hpre hnodes hproof
  have hn := hpre
  unfold FundedInputFailures.PreStorageRejected at hn
  have hi : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize := by omega
  have hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey := by omega
  have hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue := by omega
  by_cases hout : ctx.protocol.wasm.limits.maxNumberLogs = 0 ∨
      ctx.protocol.wasm.limits.maxTotalLogLength < 5 ∨
      ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length
  · exact CanonicalOutputFailures.output_matches_or_gas gasBound ctx raw st hmethod hwf hp hi hk hv
      hout hread hnodes hproof
  have hm : ModelSaveLimits ctx := ⟨hi, hk, hv, by omega, by omega, by omega⟩
  have hroom := CanonicalArithmetic.write_usage_room ctx raw.toFinset hwf hgrowth hv
  exact CanonicalRefinement.execOn_matches_or_gas gasBound ctx raw st hmethod hwf hrepresented hp hm
    hread hnodes hroom hproof

/-- The same original-context gas bound covers actual execution for every
input/key/value/log/return failure and either final stake outcome. -/
theorem execOn_matches_and_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hp : PreparationLimits ctx.protocol) (hgrowth : CanonicalArithmetic.GrowthRoom ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw)
    (hgas : CanonicalCost.saveCost ctx ≤ ctx.gasLimit) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ CanonicalCost.saveCost ctx := by
  by_cases hpre : FundedInputFailures.PreStorageRejected ctx
  · exact CanonicalInputFailures.execOn_matches_and_gas gasBound ctx raw st hmethod hp hpre hgas
  have hn := hpre
  unfold FundedInputFailures.PreStorageRejected at hn
  have hi : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize := by omega
  have hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey := by omega
  have hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue := by omega
  by_cases hout : ctx.protocol.wasm.limits.maxNumberLogs = 0 ∨
      ctx.protocol.wasm.limits.maxTotalLogLength < 5 ∨
      ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length
  · exact CanonicalFailureBounded.execOn_matches_and_gas gasBound ctx raw st hmethod hwf hp hi hk hv
      hout hnodes hread hgas hproof
  have hm : ModelSaveLimits ctx := ⟨hi, hk, hv, by omega, by omega, by omega⟩
  have hroom := CanonicalArithmetic.write_usage_room ctx raw.toFinset hwf hgrowth hv
  exact CanonicalBounded.execOn_matches_and_gas gasBound ctx raw st hwf hrepresented hmethod hp hm
    hnodes hread hroom hgas hproof

/-- Exact finite-set runtime arbitrary-gas agreement without any accepting
resource limit or context-specific prospective-write-room premise. -/
theorem nearRuntime_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw)
    (hrepresented : (model gasBound).Represents raw st)
    (hp : PreparationLimits ctx.protocol) (hgrowth : CanonicalArithmetic.GrowthRoom ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw.toList) :
    Matches (model gasBound) ctx raw (Near.Boundary.nearRuntime.exec code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.nearRuntime.exec code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw (Near.Boundary.nearRuntime.exec code raw ctx) ∧
      (Near.Boundary.nearRuntime.exec code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have h := execOn_matches_or_gas gasBound ctx raw.toList st hmethod
    (by simpa only [Finset.toList_toFinset] using hwf)
    (by simpa only [Finset.toList_toFinset] using hrepresented)
    hp hgrowth hread hnodes hproof
  simpa only [Near.Boundary.nearRuntime, Finset.toList_toFinset] using h

/-- Every pointwise `Refines` clause over arbitrary canonical storage. Resource
acceptance, empty-base, selected-key and per-call usage-room premises are absent.
Node exclusion, actual proof acceptance and protocol certificates stay explicit. -/
theorem nearRuntime_refinement_clauses
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hwf : ctx.WF raw) (hrepresented : boundedModel.Represents raw st)
    (hp : PreparationLimits ctx.protocol) (hgrowth : CanonicalArithmetic.GrowthRoom ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw.toList) :
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
      ctx raw st hmethod hwf hrepresented hp hgrowth hread hnodes hproof
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
      have hb := execOn_matches_and_gas (fun ctx _ _ => CanonicalCost.saveCost ctx) ctx raw.toList st
        hmethod (by simpa only [Finset.toList_toFinset] using hwf)
        (by simpa only [boundedModel, Finset.toList_toFinset] using hrepresented)
        hp hgrowth hread hnodes hproof hgas
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

end WNear.Skeleton.CanonicalAllLimits
