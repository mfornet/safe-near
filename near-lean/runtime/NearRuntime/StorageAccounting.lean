import NearRuntime.Apply

/-! Chunk cache and receipt-write lifetimes, independently of contract success.
The accounting context is execution metadata, not a persistent runtime record. -/
namespace Near

/-- Deleting an account stages tombstones without erasing warmed hashes. -/
theorem stageContractStorageRemoval_keeps_accounting (account : AccountId)
    (storage : List (Bytes × Bytes)) (accounting : Option TrieOverlay.State) :
    (stageContractStorageRemoval account storage accounting).map (·.accounting) =
      accounting.map (·.accounting) := by
  have frame (rows : List (Bytes × Bytes)) (trie : TrieOverlay.State) :
      (rows.foldl (fun trie (key, _) =>
        trie.remove (TrieOverlay.contractKey account.toUTF8.toList key)) trie).accounting = trie.accounting := by
    induction rows generalizing trie with
    | nil => rfl
    | cons row rest ih => exact ih (trie.remove (TrieOverlay.contractKey account.toUTF8.toList row.1))
  cases accounting with
  | none => rfl
  | some trie => simpa only [stageContractStorageRemoval, Option.map_some] using congrArg some (frame storage trie)

/-- A failed receipt cannot erase warmed hashes or accesses already observed. -/
theorem rollbackReceipt_keeps_accounting (initial : ChainState) (exec : Exec) (error : RuntimeError) :
    (rollbackReceipt initial exec (some error)).storageAccounting.map (·.accounting) =
      exec.storageAccounting.map (·.accounting) := by
  simp [rollbackReceipt, Option.map_map, Function.comp_def]

/-- Previously committed chunk writes survive a later receipt's failure. -/
theorem rollbackReceipt_keeps_committed (initial : ChainState) (exec : Exec) (error : RuntimeError) :
    (rollbackReceipt initial exec (some error)).storageAccounting.map (·.committed) =
      exec.storageAccounting.map (·.committed) := by
  simp [rollbackReceipt, Option.map_map, Function.comp_def]

/-- Publishing writes does not change the base trie or the accounting history. -/
theorem commitStorage_keeps_base_and_cache (exec : Exec) :
    exec.commitStorage.storageAccounting.map (fun trie => (trie.base, trie.accounting)) =
      exec.storageAccounting.map (fun trie => (trie.base, trie.accounting)) := by
  simp [Exec.commitStorage, Option.map_map, Function.comp_def]

/-- Every completed receipt leaves no tentative writes for the next receipt. -/
theorem applyActionReceipt_no_prospective (context : ReceiptCtx) (state : ChainState)
    (trie : TrieOverlay.State) (h : (applyActionReceipt context state).storageAccounting = some trie) :
    trie.prospective = [] := by
  unfold applyActionReceipt Exec.commitStorage at h
  cases he : (finalizeReceipt context state (runReceiptActions context state).1
      (runReceiptActions context state).2).storageAccounting with
  | none => simp [he] at h
  | some before =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    cases h
    rfl

end Near
