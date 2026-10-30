import Bridge.Functions.NewCosts

/-!
# The host through `new`'s storage calls

`new`'s success path makes four storage calls: `storage_has_key(STATE)`, the write and the
removal of the dummy record (`mKey`) and `storage_write(STATE, …)`. `Keep` is what none of them
changes: the config, the fee tables, the account, the balance, the logs, the return data, the
promises, the recorded proof's size function, the execution issue. `keep_storageWriteHost`,
`keep_storageRemoveHost`: the write and the removal keep it; `keep_of_erase`: so does `erase`.

`NewPost e h h4`: the chain of hosts from `h` to `h4`, each up to gas.
-/

namespace WNear.Binary.NewBody

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.MeasureUsage (mKey mVal)
open WNear.Binary.StorageWrite (evictedRegister)
open WNear.Binary.StateWrite (stateBytes)

/-- What `new`'s storage calls keep of the host. -/
structure Keep where
  config : NearConfig
  isView : Bool
  extCosts : Near.ExtCosts
  fees : Near.ActionFees
  id : List UInt8
  balance : Nat
  logs : List (List UInt8)
  returnData : Option (List UInt8)
  promises : List NearPromise
  returnedPromise : Option Nat
  gasWeights : List (Nat × Nat × Nat)
  proofSize : Option (Near.TrieOverlay.State → Nat)
  issue : Option Near.ExecutionIssue
  fromTrie : Bool

def keep (x : NearState) : Keep :=
  ⟨x.config, x.context.isView, x.extCosts, x.fees, x.context.currentAccountId, x.context.accountBalance, x.logs,
    x.returnData, x.promises, x.returnedPromise, x.gasWeights, x.storageProofSize, x.lastExecutionIssue,
    x.storageReadsFromTrie⟩

theorem keep_erase (x : NearState) : keep (erase x) = keep x := rfl

theorem keep_of_erase {x y : NearState} (he : erase x = erase y) : keep x = keep y := by
  rw [← keep_erase x, he, keep_erase]

theorem keep_acc (x : NearState) (s : Option Near.TrieOverlay.State) :
    keep { x with storageAccounting := s } = keep x := rfl

theorem keep_storageReadRegs (x : NearState) (r : UInt64) (v : Option (List UInt8)) :
    keep (storageReadRegs x r v) = keep x := by
  unfold storageReadRegs
  split
  · split <;> rfl
  · rfl

theorem keep_storageWriteHost (e : Nat) (x : NearState) (k v : List UInt8) (r : UInt64) (s : Near.TrieOverlay.State) :
    keep (storageWriteHost e x k v r s) = keep x := by
  unfold storageWriteHost logWrite
  have := keep_storageReadRegs { x with storageAccounting := some s } r (x.storage k)
  exact this

theorem keep_storageRemoveHost (e : Nat) (x : NearState) (k : List UInt8) (r : UInt64) (s : Near.TrieOverlay.State) :
    keep (storageRemoveHost e x k r s) = keep x := by
  unfold storageRemoveHost logRemove removeRegs
  split
  · rename_i v _
    exact keep_storageReadRegs { x with storageAccounting := some s } r (some v)
  · rfl

theorem sameCost_of_keep {x y : NearState} (hk : keep x = keep y) : SameCost x y :=
  ⟨congrArg Keep.extCosts hk, congrArg Keep.fees hk, congrArg Keep.id hk⟩

/-- The bytes `state_write` stores for `new`'s state: the prefix `"a"`, `total_supply = 0`,
`account_storage_usage = 85 + extra`. -/
def newBytes (e : Nat) : List UInt8 :=
  stateBytes 1 [97] (List.replicate 8 0) (List.replicate 8 0) (storeBytes (.i64 (UInt64.ofNat (85 + e))) 8)

/-- The hosts `new`'s success path goes through, from `h` to `h4`, each up to gas: `storage_has_key`
(`h2`), the dummy record written (`h1`) and removed (`h3`), the state written (`h4`). -/
def NewPost (e : Nat) (h h4 : NearState) : Prop :=
  ∃ (h2 h1 h3 : NearState) (s2 s1 s3 s4 : Near.TrieOverlay.State),
    erase h2 = erase { h with storageAccounting := some s2 } ∧
    erase h1 = erase (storageWriteHost e h2 mKey mVal evictedRegister s1) ∧
    erase h3 = erase (storageRemoveHost e h1 mKey evictedRegister s3) ∧
    erase h4 = erase (storageWriteHost e h3 StateRead.stateKey (newBytes e) evictedRegister s4)

theorem NewPost.keep {e : Nat} {h h4 : NearState} (hp : NewPost e h h4) : keep h4 = keep h := by
  obtain ⟨h2, h1, h3, s2, s1, s3, s4, e2, e1, e3, e4⟩ := hp
  rw [keep_of_erase e4, keep_storageWriteHost, keep_of_erase e3, keep_storageRemoveHost, keep_of_erase e1,
    keep_storageWriteHost, keep_of_erase e2, keep_acc]

theorem stateKey_ne_mKey : StateRead.stateKey ≠ mKey := by decide

open Near.TrieOverlay in
/-- `f289_spec`'s bound on the removal side, from any host with `h`'s costs. -/
theorem hK2_of (cfg : WasmConfig) (e : Nat) (h h2 : NearState) (hs : SameCost h2 h) :
    ∀ h1 s2, erase h1 = erase (storageWriteHost e h2 mKey mVal evictedRegister s2) →
      250 * cfg.regularOpCost + storageUsageUse h1 + LookupMapOps.cost402 cfg (1 + 3) 1 64 h1 mKey mVal ≤
        k2New cfg h := by
  intro h1 s2 he
  refine k2New_bound cfg h h1 ((sameCost_of_keep ((keep_of_erase he).trans (keep_storageWriteHost _ _ _ _ _ _))).trans hs) ?_
  rw [erase_field he NearState.storage fun _ => rfl, storageWriteHost_storage]
  simp

open Near.TrieOverlay in
/-- What `measure_account_storage_usage` leaves meets the hypotheses of `state_write`: the dummy
record written (`h1`) then removed (`h3`), the accounting a canonical trie linked to the storage,
the budget spent. -/
theorem after404 {e : Nat} {h2 h3 : NearState} {st2 : Near.TrieOverlay.State} {bud : Nat}
    (hq : MeasureUsage.Post404 e h2 st2 bud h3)
    (hw : writeProofCost (contractKey h2.context.currentAccountId mKey) none +
      removeProofCost (contractKey h2.context.currentAccountId mKey) (some mVal) ≤ bud) :
    ∃ h1 s1 st3, erase h1 = erase (storageWriteHost e h2 mKey mVal evictedRegister s1) ∧
      erase h3 = erase (storageRemoveHost e h1 mKey evictedRegister st3) ∧
      h3.storageAccounting = some st3 ∧ Canon st3 ∧ StorageLink h3 st3 ∧
      ProofBudget h3 st3 (bud - (writeProofCost (contractKey h2.context.currentAccountId mKey) none +
        removeProofCost (contractKey h2.context.currentAccountId mKey) (some mVal))) := by
  obtain ⟨h1, s2, -, -, hc1, hl1, hp1, he1, hr⟩ := hq
  have hk1 : h1.storage mKey = some mVal := by
    rw [erase_field he1 NearState.storage fun _ => rfl, storageWriteHost_storage]; simp
  have hid1 : h1.context.currentAccountId = h2.context.currentAccountId :=
    congrArg Keep.id ((keep_of_erase he1).trans (keep_storageWriteHost _ _ _ _ _ _))
  obtain ⟨st3, hacc3, hc3, hl3, hp3, he3⟩ := StorageRemovePost.next hr hc1 hl1 hp1 (by rw [hk1, hid1]; omega)
  refine ⟨h1, s2, st3, he1, he3, hacc3, hc3, hl3, ?_⟩
  rw [hk1, hid1, Nat.sub_sub] at hp3
  exact hp3

theorem storage_after404 {e : Nat} {h2 h1 h3 : NearState} {s1 st3 : Near.TrieOverlay.State}
    (he1 : erase h1 = erase (storageWriteHost e h2 mKey mVal evictedRegister s1))
    (he3 : erase h3 = erase (storageRemoveHost e h1 mKey evictedRegister st3)) (k : List UInt8) :
    h3.storage k = if k = mKey then none else h2.storage k := by
  rw [erase_field he3 NearState.storage fun _ => rfl, storageRemoveHost_storage,
    erase_field he1 NearState.storage fun _ => rfl, storageWriteHost_storage]
  by_cases hk : k = mKey <;> simp [hk]

theorem keep_after404 {e : Nat} {h2 h1 h3 : NearState} {s1 st3 : Near.TrieOverlay.State}
    (he1 : erase h1 = erase (storageWriteHost e h2 mKey mVal evictedRegister s1))
    (he3 : erase h3 = erase (storageRemoveHost e h1 mKey evictedRegister st3)) : keep h3 = keep h2 := by
  rw [keep_of_erase he3, keep_storageRemoveHost, keep_of_erase he1, keep_storageWriteHost]

end WNear.Binary.NewBody
