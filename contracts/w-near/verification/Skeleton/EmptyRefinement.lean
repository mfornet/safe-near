import Skeleton.FundedObservation
import Skeleton.FundedInputFailures
import Skeleton.FundedOutputFailures
import Skeleton.EmptyBounded
import Skeleton.InvalidMethod
import Skeleton.ModelSafety

/-! Pointwise assembly of the actual refinement clauses. This is explicitly
restricted to the empty-base/native-width/proof scope;
it does not narrow `Refines` or the shared context predicate. -/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface MeteredHosts
open FunctionalInvariant

/-- The recorded-proof premise is unchanged by startup and storage prepayment. -/
theorem emptyPaid_recordedStorageError (ctx : Context) (raw : Storage)
    (trie : Near.TrieOverlay.State) :
    recordedStorageError (emptyPaid ctx raw) trie = recordedStorageError (origin ctx raw) trie := by
  have hf := congrArg NearState.storageProofSize (emptyPaid_frame ctx raw).2
  change (emptyPaid ctx raw).storageProofSize = (emptyBefore ctx raw).host.storageProofSize at hf
  rw [recordedStorageError, recordedStorageError, emptyPaid_config, storageInput_config, hf,
    storageInput_storageProofSize]
  rfl

/-- No resource limit must accept: the ordered input, storage, log and
return branches all have the model-or-gas alternative at arbitrary gas. -/
theorem execOn_empty_allLimits_matches_or_gas
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hp : PreparationLimits ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  by_cases hpre : FundedInputFailures.PreStorageRejected ctx
  · exact FundedInputFailures.execOn_matches_or_gas gasBound ctx raw st hmethod hwf hp hpre
      hentries hselected hproof
  have hn := hpre
  unfold FundedInputFailures.PreStorageRejected at hn
  have hi : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize := by omega
  have hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey := by omega
  have hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue := by omega
  by_cases hout : ctx.protocol.wasm.limits.maxNumberLogs = 0 ∨
      ctx.protocol.wasm.limits.maxTotalLogLength < 5 ∨
      ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length
  · exact FundedOutputFailures.output_matches_or_gas gasBound ctx raw st hmethod hwf hp hi hk hv
      hout hread hentries hselected hproof
  have hm : ModelSaveLimits ctx := ⟨hi, hk, hv, by omega, by omega, by omega⟩
  exact FundedObservation.execOn_matches_or_gas gasBound ctx raw st hmethod hwf hrepresented hp hm
    hread hentries hselected hroom hproof

/-- The exact finite-set runtime has model agreement or the rollback/log-prefix
alternative for any gas amount on the stated empty-base slice, for every resource-limit branch. -/
theorem nearRuntime_empty_matches_or_gas
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw)
    (hrepresented : (model gasBound).Represents raw st)
    (hp : PreparationLimits ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw.toList)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw (Near.Boundary.nearRuntime.exec code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.nearRuntime.exec code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw (Near.Boundary.nearRuntime.exec code raw ctx) ∧
      (Near.Boundary.nearRuntime.exec code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have h := execOn_empty_allLimits_matches_or_gas gasBound ctx raw.toList st hmethod
    (by simpa only [Finset.toList_toFinset] using hwf)
    (by simpa only [Finset.toList_toFinset] using hrepresented)
    hp hread hentries hselected hroom hproof
  simpa only [Near.Boundary.nearRuntime, Finset.toList_toFinset] using h

/-- All clauses appearing in `Refines`, at one context/storage point under
explicit slice assumptions. The unrestricted `Refines` theorem remains open. -/
theorem nearRuntime_empty_refinement_clauses
    (ctx : Context) (raw : RawStorage) (st : Option Storage)
    (hwf : ctx.WF raw) (hrepresented : sufficientGasModel.Represents raw st)
    (hp : PreparationLimits ctx.protocol)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw.toList)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let M := sufficientGasModel
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
  · have halt := nearRuntime_empty_matches_or_gas (fun ctx _ _ => saveEmptyCost ctx)
      ctx raw st hmethod hwf hrepresented hp hread hentries hselected hroom hproof
    have hpaid : recordedStorageError (emptyPaid ctx raw.toList)
        (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw.toList).context.currentAccountId
          "k".toUTF8.toList) ctx.args) = none := by
      rw [(emptyPaid_represents ctx raw.toList).1, emptyPaid_recordedStorageError]
      exact hproof
    refine ⟨?_, ?_, ?_⟩
    · rcases halt with hmatch | hg
      · exact matches_modelStep_no_issue (fun ctx _ _ => saveEmptyCost ctx) ctx raw st _ hmatch
      · intro msg he
        rw [hg.1] at he
        cases he
    · intro call hparse
      cases call
      exact ⟨nearRuntime_empty_sufficientGas_clause ctx raw st hwf hrepresented hp hentries hselected
        hroom hpaid () hparse, halt⟩
    · intro hn
      exact False.elim (hn ⟨(), hmethod⟩)
  · have hn : ¬ ∃ call, sufficientGasModel.Parses ctx.method ctx.args call := by
      rintro ⟨call, hparse⟩
      exact hmethod hparse
    have hi := nearRuntime_invalid_method (fun ctx _ _ => saveEmptyCost ctx) ctx raw hn
    refine ⟨hi.2, ?_, fun _ => hi.1⟩
    intro call hparse
    exact False.elim (hn ⟨call, hparse⟩)

end WNear.Skeleton
