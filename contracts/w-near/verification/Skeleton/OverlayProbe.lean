import Skeleton.Model
import Wasm.Binary

/-!
# Duplicate-overlay refinement-premise probe

A canonical empty base and duplicate prospective entries expose a discrepancy
between `State.view` (last duplicate wins) and `getReference` (first wins).
The executable pins protocol 86 and runs both the walking module and the
deployed wNEAR binary, without modifying the runtime or its well-formedness.
-/
namespace WNear.Skeleton.OverlayProbe
open Wasm Wasm.Near NearInterface

def key : Near.Bytes := [107]
def wrong : Near.Bytes := [119, 114, 111, 110, 103]
def actual : Near.Bytes := [97, 99, 116, 117, 97, 108]
def rawKey (account : NearInterface.AccountId) : Near.Bytes :=
  Near.TrieOverlay.contractKey account.bytes key

def emptyBase : Near.TrieConstruction.Built :=
  { root := List.replicate 32 0, memoryUsage := 0, witness := [] }

def trie (account : NearInterface.AccountId) : Near.TrieOverlay.State :=
  { entries := [], base := emptyBase,
    prospective := [(rawKey account, some wrong), (rawKey account, some actual)] }

def raw : RawStorage := {(key, actual)}
def storage : List (Near.Bytes × Near.Bytes) := [(key, actual)]

theorem canonical (account : NearInterface.AccountId) :
    Near.TrieConstruction.build (trie account).entries = .ok (trie account).base := by rfl

def context (cfg : RuntimeConfig) (account : NearInterface.AccountId) : Context := {
  method := "save", args := [110, 101, 119], current := account, predecessor := account, signer := account,
  signerPk := [], attached := 0, prepaidGas := 300 * 10^12,
  promiseResults := [], outputDataReceivers := [], balance := 100 * 10^24,
  locked := 0, storageUsage := 1000 + storageUsageOf cfg raw,
  blockHeight := 1, timestamp := 0, epochHeight := 1, randomSeed := List.replicate 32 0,
  trie := trie account, protocol := cfg }

def stateKey (account : NearInterface.AccountId) : Near.Bytes :=
  Near.TrieOverlay.contractKey account.bytes [83, 84, 65, 84, 69]

def stateTrie (account : NearInterface.AccountId) : Near.TrieOverlay.State :=
  { entries := [], base := emptyBase,
    prospective := [(stateKey account, some wrong), (stateKey account, none)] }

def newContext (cfg : RuntimeConfig) (account : NearInterface.AccountId) : Context :=
  { context cfg account with
    method := "new", args := [123, 125],
    trie := stateTrie account, storageUsage := 1000 }

-- Unfold the transparent implementation helper without changing its code.
local macro "unfold_overlay_changes" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieOverlay 0) "Near") "TrieOverlay") "applyChanges"
  `(tactic| unfold $(Lean.mkIdent name))

local macro "unfold_overlay_search" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieOverlay 0) "Near") "TrieOverlay") "overlay"
  `(tactic| unfold $(Lean.mkIdent name))

theorem view_actual (account : NearInterface.AccountId) :
    (trie account).view = [(rawKey account, actual)] := by
  unfold trie Near.TrieOverlay.State.view
  unfold_overlay_changes
  simp

theorem lookup_wrong (account : NearInterface.AccountId) :
    Near.TrieOverlay.getReference (trie account) (rawKey account) true =
      .ok (trie account, some (.memory wrong)) := by
  unfold Near.TrieOverlay.getReference
  unfold_overlay_search
  simp [trie]
  rfl

theorem storage_actual (account : NearInterface.AccountId) :
    contractData (trie account) account.bytes = raw := by
  simp only [contractData, view_actual]
  have hk : rawKey account = Near.TrieOverlay.contractKey account.bytes [] ++ key := by
    simp [rawKey, Near.TrieOverlay.contractKey, List.append_assoc]
  rw [hk]
  simp [raw]

theorem state_view_empty (account : NearInterface.AccountId) : (stateTrie account).view = [] := by
  unfold stateTrie Near.TrieOverlay.State.view
  unfold_overlay_changes
  simp

theorem state_lookup_wrong (account : NearInterface.AccountId) (accountNodes : Bool) :
    Near.TrieOverlay.getReference (stateTrie account) (stateKey account) accountNodes =
      .ok (stateTrie account, some (.memory wrong)) := by
  unfold Near.TrieOverlay.getReference
  unfold_overlay_search
  simp [stateTrie]
  rfl

theorem state_storage_empty (account : NearInterface.AccountId) :
    contractData (stateTrie account) account.bytes = ∅ := by
  simp [contractData, state_view_empty]

/-- The current `WF` accepts the inconsistent duplicate overlay for every
valid account, under just the explicitly checked numeric protocol bounds. -/
theorem context_wf (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (hroom : 1000 + storageUsageOf cfg raw + cfg.wasm.limits.maxGasBurnt < 2 ^ 64)
    (hop : 0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost) :
    (context cfg account).WF raw := by
  refine ⟨(by change 100 * 10^24 + 0 < 2 ^ 128; decide),
    (by change 0 < 2 ^ 128; decide), (by change 300 * 10^12 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), (by change 0 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), ?_, hroom, hop, canonical account, storage_actual account, ?_⟩
  · exact Nat.le_add_left _ _
  · intro k v v' hv hv'
    simp only [raw, Finset.mem_singleton] at hv hv'
    exact (Prod.mk.inj (hv.trans hv'.symm)).2

theorem new_context_wf (cfg : RuntimeConfig) (account : NearInterface.AccountId)
    (hroom : 1000 + cfg.wasm.limits.maxGasBurnt < 2 ^ 64)
    (hop : 0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost) :
    (newContext cfg account).WF ∅ := by
  refine ⟨(by change 100 * 10^24 + 0 < 2 ^ 128; decide),
    (by change 0 < 2 ^ 128; decide), (by change 300 * 10^12 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), (by change 0 < 2 ^ 64; decide),
    (by change 1 < 2 ^ 64; decide), ?_, hroom, hop, ?_, state_storage_empty account, ?_⟩
  · simp [storageUsageOf]
  · rfl
  · intro k v v' hv
    simp at hv

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL: {label}")

private def checkedAccount : IO NearInterface.AccountId :=
  if h : validAccountIdBytes "aa".toUTF8.toList = true then pure ⟨"aa", h⟩
  else throw (IO.userError "invalid probe account")

private def mismatch (r : Observation) : Bool :=
  match r.outcome with
  | .error (.executionIssue message) => message.contains "trie/contract storage"
  | _ => false

def run : IO Unit := do
  let cfg ← RuntimeConfig.load "../../../near-lean/vm/configs" 86
  let account ← checkedAccount
  let ctx := context cfg account
  check "WF storage-usage room" (decide (1000 + storageUsageOf cfg raw + cfg.wasm.limits.maxGasBurnt < 2 ^ 64))
  check "WF positive operation charges" (decide (0 < cfg.wasm.regularOpCost ∧ 0 < cfg.wasm.linearOpBaseCost))
  check "WF skeleton trie_storage" (decide (contractData ctx.trie account.bytes = raw))
  let result := Near.Boundary.execOn code storage ctx
  IO.println s!"skeleton, protocol 86: {repr result.outcome}; burnt={result.burntGas}; logs={repr result.logs}"
  check "duplicate overlay causes skeleton executionIssue" (mismatch result)
  check "skeleton failure rolls back storage" (decide (result.storage = raw))
  let newCtx := newContext cfg account
  check "WF wNEAR trie_storage" (decide (contractData newCtx.trie account.bytes = ∅))
  check "WF wNEAR storage-usage room" (decide (1000 + cfg.wasm.limits.maxGasBurnt < 2 ^ 64))
  let binary ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode binary with
    | .ok module => pure module
    | .error error => throw (IO.userError s!"decode: {repr error}")
  let deployed : Near.Boundary.Code :=
    { code := { module, size := binary.size, hash := "overlay-probe" }, codeOf := fun _ => default }
  let actualRun := Near.Boundary.execOn deployed [] newCtx
  IO.println s!"deployed wNEAR new, protocol 86: {repr actualRun.outcome}; burnt={actualRun.burntGas}; logs={repr actualRun.logs}"
  check "duplicate overlay causes deployed wNEAR executionIssue" (mismatch actualRun)
  check "wNEAR failure rolls back storage" (decide (actualRun.storage = ∅))
  IO.println "confirmed runtime counterexamples; no runtime or model definitions changed"

end WNear.Skeleton.OverlayProbe

def main : IO Unit := WNear.Skeleton.OverlayProbe.run
