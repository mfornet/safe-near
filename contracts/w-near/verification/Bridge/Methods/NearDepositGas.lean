import Bridge.Methods.FtTotalSupplyGas
import NearLogic.Hosts.StorageWrite

/-!
# `near_deposit` (234): the trie nodes against the model's `trieGas`

`near_deposit` makes, on a fresh account, three storage writes: the account's balance entry
twice (`register_account`, then `internal_deposit`) and `STATE` (`state_write`), and its reads:
`STATE` (`state_read`), the account (`contains_key` through `storage_has_key`, then
`internal_deposit`'s `get`).

* **Reads bill no trie node at the boundary.** `toVMContext` leaves `storageReadsFromTrie` false,
  so `storage_read` and `storage_has_key` bill `readNodes = 0` nodes (`readNodes_of_false`,
  `hostOf_readsFromTrie`).
* **The writes fit `trieGas`** (`trie_writes_le`): each write bills at most `2·|rawKey| + 2` nodes
  at the dearer node cost (`storageWritePhaseUse`). Two writes of a key at most
  `maxStorageKeyBytes` long and one of `STATE` (5 bytes) bill at most `3 · trieNodes ctx` nodes,
  since `STATE` is 64 bytes shorter than the longest key; and
  `3 · trieNodes · max t c ≤ 3 · trieNodes · t + 8 · trieNodes · c = trieGas`.

With the reads' nodes counted as before (`2·|rawKey| + 1` each), three reads and three writes
would exceed `trieGas` whenever the cached node cost is small against the cold one.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near NearLogic NearInterface

/-- At the boundary the host does not read from the trie. -/
theorem hostOf_readsFromTrie (ctx : Context) (raw : RawStorage) :
    (erase (hostOf ctx raw)).storageReadsFromTrie = false := rfl

/-- At the boundary `storage_read` and `storage_has_key` bill no trie node. -/
theorem readNodes_boundary (ctx : Context) (raw : RawStorage) (k : List UInt8) :
    readNodes (erase (hostOf ctx raw)) k = 0 :=
  readNodes_of_false (hostOf_readsFromTrie ctx raw) k

/-- The nodes of two writes of a contract key at most `maxStorageKeyBytes` long and one of a 5-byte
key are at most `3 · trieNodes`. -/
theorem nodes_writes_le (ctx : Context) (ka : List UInt8) (hka : ka.length ≤ WNear.maxStorageKeyBytes)
    (ks : List UInt8) (hks : ks.length = 5) :
    2 * (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ka).length + 2) +
        (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ks).length + 2) ≤
      WNear.storageKeysTouched * WNear.trieNodes ctx := by
  simp only [WNear.storageKeysTouched, WNear.trieNodes, WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes,
    Near.TrieOverlay.contractKey, List.length_append, List.length_cons, List.length_nil] at hka ⊢
  omega

/-- **The trie nodes of `near_deposit`'s three writes fit the model's `trieGas`**, at the dearer
node cost. -/
theorem trie_writes_le (ctx : Context) (raw : RawStorage) (ka : List UInt8)
    (hka : ka.length ≤ WNear.maxStorageKeyBytes) (ks : List UInt8) (hks : ks.length = 5) :
    (2 * (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ka).length + 2) +
        (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ks).length + 2)) *
      trieNodeMax (erase (hostOf ctx raw)) ≤ WNear.trieGas ctx := by
  have hn := nodes_writes_le ctx ka hka ks hks
  have hx : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  unfold trieNodeMax
  rw [hx]
  unfold WNear.trieGas
  simp only [WNear.storageKeysTouched, WNear.storageAccesses] at hn ⊢
  set t := ctx.protocol.wasm.extCosts.cost "touching_trie_node"
  set r := ctx.protocol.wasm.extCosts.cost "read_cached_trie_node"
  set N := WNear.trieNodes ctx
  set w := 2 * (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ka).length + 2) +
    (2 * (Near.TrieOverlay.contractKey ctx.current.bytes ks).length + 2)
  have h1 : w * max t r ≤ 3 * N * max t r := Nat.mul_le_mul_right _ hn
  have h2 : 3 * N * max t r ≤ 3 * N * t + 8 * N * r := by
    rcases le_total t r with h | h
    · rw [max_eq_right h]
      have : 3 * N * r ≤ 8 * N * r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      omega
    · rw [max_eq_left h]
      omega
  exact le_trans h1 h2

end WNear.Binary.NearDepositGas
