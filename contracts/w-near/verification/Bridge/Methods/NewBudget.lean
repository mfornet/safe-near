import Bridge.Methods.NewModel
import Bridge.Methods.FtTotalSupplyPre
import NearLogic.Hosts.StorageRemove

/-!
# `new` (290): the recorded-proof budget

`new` makes four storage calls: `storage_has_key(STATE)`, `storage_write(k, 0u128)` and
`storage_remove(k)` of the dummy account key `k = b"a" ++ borsh("a" * 64)` (69 bytes), and
`storage_write(STATE, state)`. `proof_new_le`: what they record together
(`lookupProofBound`, `writeProofCost`, `removeProofCost`) is within the model's `proofBound`.
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near NearLogic NearInterface Near.TrieOverlay

/-- The dummy account key `measure_account_storage_usage` inserts and removes:
`b"a" ++ borsh("a" * 64)`. -/
def dummyKey : List UInt8 := [97] ++ [64, 0, 0, 0] ++ List.replicate 64 97

theorem dummyKey_length : dummyKey.length = 69 := rfl

theorem contractKey_length (a k : List UInt8) : (contractKey a k).length = a.length + 2 + k.length := by
  simp only [contractKey, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The four storage calls of `new` record at most `proofBound`.** -/
theorem proof_new_le (ctx : Context) (v : List UInt8) (hv : v.length = 16) :
    lookupProofBound (contractKey ctx.current.bytes WNear.stateKey) +
      writeProofCost (contractKey ctx.current.bytes dummyKey) none +
      removeProofCost (contractKey ctx.current.bytes dummyKey) (some v) +
      writeProofCost (contractKey ctx.current.bytes WNear.stateKey) none ≤ WNear.proofBound ctx := by
  have h1 : lookupProofBound (contractKey ctx.current.bytes WNear.stateKey) ≤
      lookupProofBoundLen (2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes) := by
    unfold lookupProofBound
    rw [contractKey_length, stateKey_length]
    exact FtTotalSupplyMethod.lookupProofBoundLen_mono (by simp [WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes]; omega)
  have h2 : lookupProofBound (contractKey ctx.current.bytes dummyKey) ≤
      lookupProofBoundLen (2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes) := by
    unfold lookupProofBound
    rw [contractKey_length, dummyKey_length]
    exact FtTotalSupplyMethod.lookupProofBoundLen_mono (by simp [WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes]; omega)
  simp only [removeProofCost, writeProofCost, Option.map_none, Option.getD_none, Option.map_some,
    Option.getD_some, hv, WNear.proofBound, WNear.storageAccesses, WNear.storageRemovals,
    WNear.maxStorageValueBytes]
  generalize lookupProofBoundLen (2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes) = L at h1 h2 ⊢
  generalize removalProofCharge = R
  omega

/-- **The trie nodes the four storage calls of `new` may bill**, at the dearer node cost (`2·|k| + 1`
for `storage_has_key`, `2·|k| + 2` for each mutation), against the model's `trieGas`: they fit but
for `2·|current|` cold nodes. The bound pays three cold paths of the longest key; `new`'s four
calls are billed here as four paths at the dearer cost, two of them of the longest key. -/
theorem trie_new_le (ctx : Context) :
    ((2 * (contractKey ctx.current.bytes WNear.stateKey).length + 1) +
      (2 * (contractKey ctx.current.bytes dummyKey).length + 2) +
      (2 * (contractKey ctx.current.bytes dummyKey).length + 2) +
      (2 * (contractKey ctx.current.bytes WNear.stateKey).length + 2)) *
        max (ctx.protocol.wasm.extCosts.cost "touching_trie_node")
          (ctx.protocol.wasm.extCosts.cost "read_cached_trie_node") ≤
      WNear.trieGas ctx + 2 * ctx.current.bytes.length * ctx.protocol.wasm.extCosts.cost "touching_trie_node" := by
  rw [contractKey_length, contractKey_length, stateKey_length, dummyKey_length]
  simp only [WNear.trieGas, WNear.trieNodes, WNear.storageKeysTouched, WNear.storageAccesses,
    WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes]
  set t := ctx.protocol.wasm.extCosts.cost "touching_trie_node"
  set r := ctx.protocol.wasm.extCosts.cost "read_cached_trie_node"
  set c := ctx.current.bytes.length
  have hm : max t r ≤ t + r := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have h1 := Nat.mul_le_mul_left (c + 7 + 2 * (c + 2 + 7) + 1 + (2 * (c + 2 + 69) + 2) + (2 * (c + 2 + 69) + 2) -
    (c + 7)) hm
  nlinarith

end WNear.Binary.NewMethod
