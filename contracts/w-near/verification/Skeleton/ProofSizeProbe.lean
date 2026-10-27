import Skeleton.Model
import Spec.Contract
import Wasm.Binary

/-!
# Recorded-proof-size counterexample to the current refinement premises

Unlike the historical duplicate-overlay example, this input satisfies the
current Context.WF: its base is canonical empty and both overlays are unique.
The trusted proof recorder is unconstrained by that invariant (SAF-67).
-/
namespace WNear.Skeleton.ProofSizeProbe
open Wasm Wasm.Near NearInterface

def trie : Near.TrieOverlay.State :=
  { entries := [], base := { root := List.replicate 32 0, memoryUsage := 0, witness := [] } }

def context (cfg : RuntimeConfig) (account : NearInterface.AccountId) : Context := {
  method := "new", args := [123, 125], current := account, predecessor := account, signer := account,
  signerPk := [], attached := 0, prepaidGas := 300 * 10^12,
  promiseResults := [], outputDataReceivers := [], balance := 100 * 10^24,
  locked := 0, storageUsage := 1000,
  blockHeight := 1, timestamp := 0, epochHeight := 1, randomSeed := List.replicate 32 0,
  trie := trie, protocol := cfg,
  storageProofSize := some (fun _ => cfg.wasm.limits.perReceiptStorageProofSizeLimit + 1) }

theorem canonical : Near.TrieConstruction.build trie.entries = .ok trie.base := by rfl

theorem unique : trie.UniqueChanges := by
  simp [trie, Near.TrieOverlay.State.UniqueChanges]

theorem storage_empty (account : NearInterface.AccountId) : contractData trie account.bytes = ∅ := by
  rfl

/-- Current WF accepts the excessive recorder for every valid account and
protocol satisfying these ordinary numeric conditions. -/
theorem context_wf (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (hroom : 1000 + cfg.wasm.limits.maxGasBurnt < 2 ^ 64)
    (hop : 0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost) :
    (context cfg account).WF ∅ := by
  refine ⟨(by change 100 * 10^24 + 0 < 2 ^ 128; decide),
    (by change 0 < 2 ^ 128; decide), (by change 300 * 10^12 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), (by change 0 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), ?_, hroom, hop, canonical, unique, storage_empty account, ?_⟩
  · simp [storageUsageOf]
  · intro k v v' hv
    simp at hv

/-- The recorder is above the limit at every trie state, including before any
storage access. This is permitted by the current WF theorem above. -/
theorem recorded_size_exceeds (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (state : Near.TrieOverlay.State) :
    ∃ size, (context cfg account).storageProofSize = some size ∧
      cfg.wasm.limits.perReceiptStorageProofSizeLimit < size state := by
  exact ⟨_, rfl, Nat.lt_succ_self _⟩

/-- The call parses independently of the contents of its unused input. -/
theorem parses_new (cfg : RuntimeConfig) (account : NearInterface.AccountId) :
    WNear.Parses (context cfg account).method (context cfg account).args .new := by rfl

def modelOutput (cfg : RuntimeConfig) : NearInterface.Outcome WNear.State Ret Promise :=
  { state := (WNear.new (Config.ofRuntime cfg)).state, ret := .unit, logs := [], promises := [] }

/-- The only resource condition for model initialization here is its final
storage stake. The recorded-proof oracle does not occur in contractStep. -/
theorem model_new_success (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (hstake : stakeDeficit cfg
      (usageAfter (context cfg account) none (WNear.new (Config.ofRuntime cfg)).state)
      (100 * 10^24) 0 = 0) :
    contractStep (context cfg account) none .new = .ok (modelOutput cfg) := by
  simp [contractStep, step, Call.isPrivate, Call.isPayable, Call.isView,
    Env.ofContext, context, require, bind, Except.bind, pure, Except.pure, new, Outcome.nearOut,
    stepLogs, logLimitError, logLimitError.go, encodeReceipts, ReceiptValidation.callReceiptsError,
    modelOutput]
  exact hstake

/-- Any actual non-gas failure disagrees with this successful model step. The
executable below checks the deployed observation rather than asking the
kernel to normalize the whole deployed binary. -/
theorem recorded_failure_not_matches (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (modelCfg : Config) (actual : Observation)
    (hstake : stakeDeficit cfg
      (usageAfter (context cfg account) none (WNear.new (Config.ofRuntime cfg)).state)
      (100 * 10^24) 0 = 0)
    (hactual : actual.outcome = .error (.other
      (FunctionCallError.hostError (.recordedStorageExceeded cfg.wasm.limits.perReceiptStorageProofSizeLimit)).message)) :
    ¬ Matches (wnear modelCfg) (context cfg account) ∅ actual
      ((wnear modelCfg).step (context cfg account) none .new) := by
  change ¬ Matches (wnear modelCfg) (context cfg account) ∅ actual
    (contractStep (context cfg account) none .new)
  rw [model_new_success cfg account hstake]
  intro h
  have he := h.1
  rw [hactual] at he
  cases he

/-- The initial empty raw storage represents the absent model state. -/
theorem represents_empty (modelCfg : Config) : (wnear modelCfg).Represents ∅ none := by rfl

/-- This isolates the precise remaining executable-to-kernel frontier: an
execution with the checked recorded-proof failure refutes current Refines.
The low-gas alternative does not rescue the statement, since this failure
is not outOfGas. -/
theorem not_refines_of_recorded_failure {R : RuntimeInterface} (cfg : RuntimeConfig)
    (account : NearInterface.AccountId) (modelCfg : Config) (code : R.Code)
    (hroom : 1000 + cfg.wasm.limits.maxGasBurnt < 2 ^ 64)
    (hop : 0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost)
    (hstake : stakeDeficit cfg
      (usageAfter (context cfg account) none (WNear.new (Config.ofRuntime cfg)).state)
      (100 * 10^24) 0 = 0)
    (hactual : (R.exec code ∅ (context cfg account)).outcome = .error (.other
      (FunctionCallError.hostError (.recordedStorageExceeded cfg.wasm.limits.perReceiptStorageProofSizeLimit)).message)) :
    ¬ Refines R cfg code (wnear modelCfg) := by
  intro h
  have hvalid := (h ∅ none (context cfg account) (represents_empty modelCfg)
    (context_wf cfg account hroom hop) rfl).2.1 .new (parses_new cfg account)
  rcases hvalid.2 with hm | hg
  · exact recorded_failure_not_matches cfg account modelCfg _ hstake hactual hm
  · rw [hactual] at hg
    cases hg.1

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL: {label}")

private def checkedAccount : IO NearInterface.AccountId :=
  if h : validAccountIdBytes "aa".toUTF8.toList = true then pure ⟨"aa", h⟩
  else throw (IO.userError "invalid probe account")

def run : IO Unit := do
  let cfg ← RuntimeConfig.load "../../../near-lean/vm/configs" 86
  let account ← checkedAccount
  let ctx := context cfg account
  check "WF storage-usage room" (decide (1000 + cfg.wasm.limits.maxGasBurnt < 2 ^ 64))
  check "WF positive operation charges" (decide (0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost))
  check "WF trie storage" (decide (contractData ctx.trie account.bytes = ∅))
  check "WF unique overlays" (decide ((ctx.trie.prospective.map Prod.fst).Nodup ∧ (ctx.trie.committed.map Prod.fst).Nodup))
  let binary ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode binary with
    | .ok module => pure module
    | .error error => throw (IO.userError s!"decode: {repr error}")
  let deployed : Near.Boundary.Code :=
    { code := { module, size := binary.size, hash := "proof-size-probe" }, codeOf := fun _ => default }
  let actual := Near.Boundary.execOn deployed [] ctx
  IO.println s!"deployed wNEAR new, protocol 86: {repr actual.outcome}; burnt={actual.burntGas}; logs={repr actual.logs}"
  let expected := FunctionCallError.hostError (.recordedStorageExceeded cfg.wasm.limits.perReceiptStorageProofSizeLimit)
  check "exact recorded-proof failure" (match actual.outcome with
    | .error (.other message) => message == expected.message
    | _ => false)
  check "failure rolls back storage" (decide (actual.storage = ∅))
  check "failure rolls back balance and usage" (decide (actual.balance = ctx.balance ∧ actual.storageUsage = ctx.storageUsage))
  check "model final storage stake fits" (decide (stakeDeficit cfg
    (usageAfter ctx none (WNear.new (Config.ofRuntime cfg)).state) (100 * 10^24) 0 = 0))
  check "failure has no logs or receipts" (decide (actual.logs = [] ∧ actual.receipts = []))
  let model := WNear.contractStep ctx none .new
  let modelOk := match model with | .ok _ => true | _ => false
  IO.println s!"model new success={modelOk}; gasBound={WNear.gasBound ctx .new}; gasLimit={ctx.gasLimit}"
  check "model new succeeds" modelOk
  check "model gas bound fits" (decide (WNear.gasBound ctx .new ≤ ctx.gasLimit))
  IO.println "confirmed current-WF recorded-proof counterexample; no runtime/model/WF definitions changed"

end WNear.Skeleton.ProofSizeProbe

def main : IO Unit := WNear.Skeleton.ProofSizeProbe.run
