import Skeleton.EmptyFailures
import Skeleton.OutputFailureGas
import Skeleton.StorageFailureGas

/-!
# Sufficient-gas refinement of the empty-base walking-module slice

Every model resource-limit branch, including either final storage-stake
outcome, agrees with actual public execution and uses at most the original
`saveEmptyCost`. The finite-set theorem uses the precise `nearRuntime`
interface. Empty canonical base, no selected key, native usage room and the
recorded-proof check remain explicit. `Skeleton.EmptyRefinement` assembles
the lower-gas alternative and the remaining pointwise refinement clauses.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts
set_option maxHeartbeats 800000

/-- One original-data bound covers matching and gas for every resource-limit
branch of the empty-base slice. No individual resource limit must accept. -/
theorem execOn_empty_allLimits_bounded
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  constructor
  · exact execOn_empty_matches_modelStep_allLimits gasBound ctx raw st hwf hrepresented hmethod hp
      hentries hselected hroom hgas hproof
  · by_cases hi : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length
    · exact (execOn_input_failure_bounded gasBound ctx raw st hmethod hp hi
        ((inputFailureCost_le_saveEmptyCost ctx).trans hgas)).2.trans (inputFailureCost_le_saveEmptyCost ctx)
    have hinput := Nat.le_of_not_gt hi
    by_cases hk : ctx.protocol.wasm.limits.maxLengthStorageKey < 1
    · exact (execOn_key_failure_bounded gasBound ctx raw st hmethod hp hinput hk hgas).2
    have hkey := Nat.le_of_not_gt hk
    by_cases hv : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length
    · exact (execOn_value_failure_bounded gasBound ctx raw st hmethod hp hinput hkey hv hgas).2
    have hvalue := Nat.le_of_not_gt hv
    by_cases hz : ctx.protocol.wasm.limits.maxNumberLogs = 0
    · exact execOn_empty_log_failure_usedGas_le ctx raw hwf hmethod hp hinput hkey hvalue hz
        hentries hselected hgas hproof
    have hcount := Nat.pos_of_ne_zero hz
    by_cases hl : ctx.protocol.wasm.limits.maxTotalLogLength < 5
    · exact execOn_empty_log_length_failure_usedGas_le ctx raw hwf hmethod hp hinput hkey hvalue hcount hl
        hentries hselected hgas hproof
    have hloglen := Nat.le_of_not_gt hl
    by_cases hr : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length
    · exact execOn_empty_return_length_failure_usedGas_le ctx raw hwf hmethod hp hinput hkey hvalue hcount
        hloglen hr hentries hselected hgas hproof
    have hm : ModelSaveLimits ctx := ⟨hinput, hkey, hvalue, hcount, hloglen, Nat.le_of_not_gt hr⟩
    exact (execOn_empty_matches_and_gas gasBound ctx raw st hwf hrepresented hmethod hp hm
      hentries hselected hroom hgas hproof).2

/-- The same bounded result for the exact finite-set runtime interface.
The runtime's selected listing is explicit in the recorded-proof premise. -/
theorem nearRuntime_empty_allLimits_bounded
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hwf : ctx.WF raw)
    (hrepresented : (model gasBound).Represents raw st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw.toList)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw.toList).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw (Near.Boundary.nearRuntime.exec code raw ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.nearRuntime.exec code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have h := execOn_empty_allLimits_bounded gasBound ctx raw.toList st
    (by simpa only [Finset.toList_toFinset] using hwf)
    (by simpa only [Finset.toList_toFinset] using hrepresented)
    hmethod hp hentries hselected hroom hgas hproof
  simpa only [Near.Boundary.nearRuntime, Finset.toList_toFinset] using h

/-- The independent model with the proved original-data bound as its gas field. -/
def sufficientGasModel : ContractModel := model (fun ctx _ _ => saveEmptyCost ctx)

/-- The sufficient-gas implication of the actual `Refines` valid-call clause,
restricted to the explicit empty-base and native-width/proof-check scope.
This theorem makes no claim about the lower-gas alternative. -/
theorem nearRuntime_empty_sufficientGas_clause
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hwf : ctx.WF raw)
    (hrepresented : sufficientGasModel.Represents raw st)
    (hp : PreparationLimits ctx.protocol)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (emptyPaid ctx raw.toList)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw.toList).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    ∀ call, sufficientGasModel.Parses ctx.method ctx.args call →
      sufficientGasModel.gas ctx st call ≤ ctx.gasLimit →
      Matches sufficientGasModel ctx raw (Near.Boundary.nearRuntime.exec code raw ctx)
        (sufficientGasModel.step ctx st call) ∧
      (Near.Boundary.nearRuntime.exec code raw ctx).usedGas ≤ sufficientGasModel.gas ctx st call := by
  intro call hparse hgas
  cases call
  exact nearRuntime_empty_allLimits_bounded (fun ctx _ _ => saveEmptyCost ctx) ctx raw st
    hwf hrepresented hparse hp hentries hselected hroom hgas hproof

end WNear.Skeleton
