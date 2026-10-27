import NearVM.MeteredHosts.StorageReadPrepare
import NearVM.MeteredHosts.StorageCanonical

/-! Canonical read plans at the actual storageReadsFromTrie accounting mode. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered StorageOverlay
open _root_.Near.TrieOverlay
abbrev ReadPlan := StorageCanonical.LookupPlan

def ReadPlan.looked : ReadPlan → State
  | .fresh looked => looked
  | .replace looked _ _ _ => looked

def ReadPlan.Valid (initial : State) (key : List UInt8) (accountNodes : Bool) (original : Option (List UInt8)) : ReadPlan → Prop
  | .fresh looked => getReference initial key accountNodes = .ok (looked, none) ∧ original = none
  | .replace looked pointer fetched value =>
    getReference initial key accountNodes = .ok (looked, some pointer) ∧
    dereference looked pointer = .ok (fetched, value) ∧ original = some value

def lookupPlan (initial : State) (key : List UInt8) (accountNodes : Bool) : Except String ReadPlan := do
  let (looked, pointer) ← getReference initial key accountNodes
  match pointer with
  | none => return .fresh looked
  | some pointer =>
    let (fetched, value) ← dereference looked pointer
    return .replace looked pointer fetched value

def readPlan (initial : State) (key : List UInt8) (accountNodes : Bool) : ReadPlan :=
  match lookupPlan initial key accountNodes with
  | .ok p => p
  | .error _ => .fresh initial

def ReadPlan.charges (initial : State) : ReadPlan → List Charge
  | .fresh looked => trieCharges initial looked
  | .replace looked pointer _ _ => trieCharges initial looked ++ storageReadValueCharges pointer.reference.2.length

def ReadPlan.paid (before : HostStore NearState) (initial : State) : ReadPlan → NearState
  | .fresh looked => nodePaid before initial looked
  | .replace looked pointer _ _ => hitPaid before initial looked pointer

def ReadPlan.result (before : HostStore NearState) (initial : State) (p : ReadPlan) :=
  prepared before (p.paid before initial) p.fetched

/-- Canonicality and WF derive the real reference and dereference successes,
including exact raw bytes, at either accounting mode. -/
theorem readPlan_valid (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (key : List UInt8) (accountNodes : Bool) :
    (readPlan ctx.trie (contractKey before.host.context.currentAccountId key) accountNodes).Valid ctx.trie
      (contractKey before.host.context.currentAccountId key) accountNodes (before.host.storage key) := by
  let fullKey := contractKey before.host.context.currentAccountId key
  have hread := canonical_read ctx.trie fullKey accountNodes hwf.trie_canonical hwf.trie_changes_unique hnodes
  have hsview := StorageCanonical.storage_view before ctx raw hwf storage hs hr key
  change (readPlan ctx.trie fullKey accountNodes).Valid ctx.trie fullKey accountNodes (before.host.storage key)
  cases hv : Lookup.first ctx.trie.view fullKey with
  | none =>
    rw [hv] at hread
    obtain ⟨looked, hg, _⟩ := hread
    simp only [readPlan, lookupPlan, hg, bind, Except.bind, pure, Except.pure, ReadPlan.Valid]
    exact ⟨True.intro, hsview.trans hv⟩
  | some value =>
    rw [hv] at hread
    obtain ⟨looked, pointer, fetched, hg, hd, _⟩ := hread
    simp only [readPlan, lookupPlan, hg, hd, bind, Except.bind, pure, Except.pure, ReadPlan.Valid]
    exact ⟨True.intro, True.intro, hsview.trans hv⟩

/-- Complete canonical preparation with actual ordered phase billing. The
proof check is on the looked trie, before any value dereference. -/
theorem prepare_canonical_credits (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr register : UInt64) (key : List UInt8) (rest : Nat)
    (ha : before.host.storageAccounting = some ctx.trie)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hc : before.host.gas.Credits (burnSum before.host.extCosts
      ((readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).charges ctx.trie) + rest))
    (hp : recordedStorageError before.host
      (readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie).looked = none) :
    let p := readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie
    prepareStorageCall "storage_read" before (args keyLen keyPtr register) = (p.result before ctx.trie, none) ∧
    (p.result before ctx.trie).host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (p.charges ctx.trie) ∧
    (p.result before ctx.trie).host.gas.Credits rest := by
  have valid := readPlan_valid before ctx raw hwf storage hs hr hnodes key before.host.storageReadsFromTrie
  generalize he : readPlan ctx.trie (contractKey before.host.context.currentAccountId key) before.host.storageReadsFromTrie = p at valid hc hp ⊢
  cases p with
  | fresh looked =>
    exact prepare_miss_credits before keyLen keyPtr register key ctx.trie looked rest ha hk hl valid.1 valid.2 hc hp
  | replace looked pointer fetched value =>
    have c : before.host.gas.Credits (burnSum before.host.extCosts (trieCharges ctx.trie looked) +
        (burnSum before.host.extCosts (storageReadValueCharges pointer.reference.2.length) + rest)) := by
      simpa only [ReadPlan.charges, burnSum, List.map_append, List.sum_append, Nat.add_assoc] using hc
    have h := prepare_hit_credits before keyLen keyPtr register key value ctx.trie looked fetched pointer rest ha hk hl valid.1 valid.2.2 valid.2.1 c hp
    simpa only [ReadPlan.result, ReadPlan.paid, ReadPlan.charges, StorageCanonical.LookupPlan.fetched, burnSum,
      List.map_append, List.sum_append, Nat.add_assoc] using h

end Wasm.Near.MeteredHosts.StorageRead
