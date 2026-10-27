import NearInterface.TrieOverlayInvariant
import NearRuntime.Boundary
import NearRuntime.FinalizeStages

/-!
# Runtime preservation of unique trie-overlay keys

These theorems apply the representation invariant to the actual receipt commit,
rollback, finalization and boundary-observation definitions. Execution of an
arbitrary `VmEngine` must separately preserve the VM-returned trie invariant;
finalization cannot repair arbitrary externally supplied malformed overlays.
-/
namespace Near
open Wasm Wasm.Near

/-- Every trie present at the optional runtime accounting seam has unique keys. -/
def AccountingUnique : Option TrieOverlay.State → Prop
  | none => True
  | some trie => trie.UniqueChanges

/-- Optional accounting with a well-formed fallback remains well formed. -/
theorem accounting_getD_unique (accounting : Option TrieOverlay.State) (fallback : TrieOverlay.State)
    (h : AccountingUnique accounting) (hfallback : fallback.UniqueChanges) :
    (accounting.getD fallback).UniqueChanges := by
  cases accounting <;> assumption

/-- The boundary-seam fallback used after failed calls clears prospective writes. -/
theorem accounting_getD_rollback_unique (accounting : Option TrieOverlay.State)
    (fallback : TrieOverlay.State) (h : AccountingUnique accounting)
    (hfallback : fallback.UniqueChanges) :
    (accounting.getD { fallback with prospective := [] }).UniqueChanges :=
  accounting_getD_unique accounting _ h hfallback.rollback

/-- Account deletion stages removals through the real raw-key fold; it does not
manufacture duplicate updates in the optional accounting trie. -/
theorem stageContractStorageRemoval_unique (account : AccountId)
    (storage : List (Bytes × Bytes)) (accounting : Option TrieOverlay.State)
    (h : AccountingUnique accounting) :
    AccountingUnique (stageContractStorageRemoval account storage accounting) := by
  cases accounting with
  | none => exact True.intro
  | some trie =>
    change (storage.foldl (fun current (key, _) =>
      current.remove (TrieOverlay.contractKey account.toUTF8.toList key)) trie).UniqueChanges
    induction storage generalizing trie with
    | nil => exact h
    | cons entry storage ih => exact ih _ (h.remove _)

def Exec.UniqueChanges (exec : Exec) : Prop := AccountingUnique exec.storageAccounting

/-- Receipt commit uses the real inline fold in `Exec.commitStorage`. -/
theorem Exec.UniqueChanges.commitStorage {exec : Exec} (h : exec.UniqueChanges) :
    exec.commitStorage.UniqueChanges := by
  cases ha : exec.storageAccounting with
  | none => simp only [Exec.UniqueChanges, Exec.commitStorage, ha, Option.map_none, AccountingUnique]
  | some trie =>
    have ht : trie.UniqueChanges := by simpa only [Exec.UniqueChanges, ha, AccountingUnique] using h
    simpa only [Exec.UniqueChanges, Exec.commitStorage, ha, Option.map_some, AccountingUnique]
      using ht.commit

/-- The real receipt rollback clears prospective writes without changing the
committed overlay, and successful receipts retain both maps. -/
theorem rollbackReceipt_unique (st0 : ChainState) (exec : Exec) (failed : Option RuntimeError)
    (h : exec.UniqueChanges) : (rollbackReceipt st0 exec failed).UniqueChanges := by
  cases failed with
  | none => exact h
  | some error =>
    cases ha : exec.storageAccounting with
    | none => simp only [Exec.UniqueChanges, rollbackReceipt, ha, Option.map_none, AccountingUnique]
    | some trie =>
      have ht : trie.UniqueChanges := by simpa only [Exec.UniqueChanges, ha, AccountingUnique] using h
      simpa only [Exec.UniqueChanges, rollbackReceipt, ha, Option.map_some, AccountingUnique]
        using ht.rollback

/-- Refunds, rewards and data delivery retain the rollback result's overlays. -/
theorem finalizeReceipt_unique (c : ReceiptCtx) (st0 : ChainState) (exec : Exec)
    (failed : Option RuntimeError) (h : exec.UniqueChanges) :
    (finalizeReceipt c st0 exec failed).UniqueChanges := by
  apply finalizeReceipt_stages Exec.UniqueChanges c st0 exec failed
    (rollbackReceipt_unique st0 exec failed h)
  · intro e tokens other he
    exact he
  · intro e receiver amount he
    exact he
  · intro e receiver pk amount he
    exact he
  · intro e burnPrice purchasePrice he
    unfold Exec.creditReceiptReward
    split <;> exact he
  · intro e he
    unfold Exec.finishReceiptResult Exec.deliverResult
    dsimp only
    repeat' (first | exact he | split)
  · intro e result compute he
    exact he

/-- The actual receipt's finalization/commit pipeline preserves the invariant
supplied by its action execution, for either success or failure. -/
theorem applyActionReceipt_unique [VmEngine] (c : ReceiptCtx) (st0 : ChainState)
    (h : (runReceiptActions c st0).1.UniqueChanges) :
    (applyActionReceipt c st0).UniqueChanges := by
  unfold applyActionReceipt
  exact (finalizeReceipt_unique c st0 _ _ h).commitStorage

namespace Boundary
open NearInterface (Context)

/-- Every boundary failure path rolls back prospective keys; every successful
path retains the unique VM accounting trie or the unique input fallback. -/
theorem observe_unique (ctx : Context) (storage : List (Bytes × Bytes)) (outcome : VMOutcome)
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError)
    (hctx : ctx.trie.UniqueChanges) (hout : AccountingUnique outcome.storageAccounting) :
    (observe ctx storage outcome issue receiptError).trie.UniqueChanges := by
  have ht := accounting_getD_unique outcome.storageAccounting ctx.trie hout hctx
  unfold observe
  dsimp only
  repeat' (first | exact ht | exact ht.rollback | split)

end Boundary
end Near
