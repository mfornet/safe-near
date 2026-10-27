import NearVM.Run
import NearVM.StorageListing
import NearVM.MeteredHosts.StorageMetered
import NearInterface.StorageUsage
import NearInterface.TrieOverlayStorage

/-!
# Functional host storage represents finite raw storage

Only key-list coverage is needed for outcome extraction. Repeated keys and
stale keys are harmless: finite-set conversion removes repetitions and
`finalStorage` omits absent cells. No ordering invariant is required.
-/
namespace Wasm.Near.StorageRepresentation
open NearInterface
open _root_.Near.TrieOverlay

/-- Lookup agreement and support coverage, without key order or uniqueness. -/
structure Represents (ns : NearState) (raw : RawStorage) : Prop where
  lookup : ∀ key value, ns.storage key = some value ↔ (key, value) ∈ raw
  coverage : ∀ key value, (key, value) ∈ raw → key ∈ ns.storageKeys

theorem mem_finalStorage (ns : NearState) (key value : Bytes) :
    (key, value) ∈ finalStorage ns ↔ key ∈ ns.storageKeys ∧ ns.storage key = some value := by
  simp only [finalStorage, List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, he⟩
    cases hs : ns.storage k with
    | none => simp [hs] at he
    | some v =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hk, hs⟩
  · rintro ⟨hk, hs⟩
    exact ⟨key, hk, by simp [hs]⟩

/-- VM outcome extraction returns exactly the represented finite records. -/
theorem Represents.finalStorage {ns : NearState} {raw : RawStorage} (h : Represents ns raw) :
    (finalStorage ns).toFinset = raw := by
  ext record
  obtain ⟨key, value⟩ := record
  simp only [List.mem_toFinset, mem_finalStorage]
  constructor
  · intro hm
    exact (h.lookup key value).mp hm.2
  · intro hm
    exact ⟨h.coverage key value hm, (h.lookup key value).mpr hm⟩

/-- Context construction installs a faithful lookup and covers all raw keys. -/
theorem toNearState_represents (cfg : RuntimeConfig) (ctx : VMContext)
    (listing : List (Bytes × Bytes)) (raw : RawStorage) (hlisting : listing.toFinset = raw)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v') :
    Represents (ctx.toNearState cfg listing) raw := by
  have hm (key value : Bytes) : (key, value) ∈ listing ↔ (key, value) ∈ raw := by
    rw [← hlisting, List.mem_toFinset]
  constructor
  · intro key value
    change Lookup.first listing key = some value ↔ (key, value) ∈ raw
    constructor
    · intro h
      exact (hm key value).mp (Lookup.first_some_mem listing key value h)
    · intro h
      apply Lookup.first_eq_some_of_mem listing key value ((hm key value).mpr h)
      intro v hv
      exact hunique key v value ((hm key v).mp hv) h
  · intro key value h
    change key ∈ sortedKeys listing
    have hk : key ∈ listing.map Prod.fst := List.mem_map.mpr ⟨(key, value), (hm key value).mpr h, rfl⟩
    simpa [sortedKeys] using hk

theorem mem_setStorage_keys (ns : NearState) (key value query : Bytes) :
    query ∈ (ns.setStorage key value).storageKeys ↔ query = key ∨ query ∈ ns.storageKeys := by
  by_cases hk : key ∈ ns.storageKeys
  · simp [NearState.setStorage, hk]
    intro he
    subst query
    exact hk
  · simp [NearState.setStorage, hk, List.mem_append, or_comm]

/-- Installing a cell preserves representation and adds just that raw key. -/
theorem Represents.setStorage {ns : NearState} {raw : RawStorage} (h : Represents ns raw)
    (key value : Bytes) : Represents (ns.setStorage key value) (rawWrite raw key value) := by
  constructor
  · intro query found
    rw [mem_rawWrite]
    by_cases he : query = key
    · subst query
      simp [NearState.setStorage, eq_comm]
    · simp [NearState.setStorage, he, h.lookup]
  · intro query found hm
    rw [mem_setStorage_keys]
    rw [mem_rawWrite] at hm
    rcases hm with ⟨he, _⟩ | ⟨hm, _⟩
    · exact Or.inl he
    · exact Or.inr (h.coverage query found hm)

/-- Iterator invalidation does not change the storage projection or coverage. -/
theorem Represents.invalidateIterators {ns : NearState} {raw : RawStorage}
    (h : Represents ns raw) : Represents ns.invalidateIterators raw := ⟨h.lookup, h.coverage⟩

/-- Actual raw discard-output writes have the finite-map update in outcomes. -/
theorem finalStorage_written (before : HostStore NearState) (raw : RawStorage)
    (h : Represents before.host raw) (key value : Bytes) :
    (finalStorage (MeteredHosts.written before key value).host).toFinset = rawWrite raw key value := by
  exact ((h.setStorage key value).invalidateIterators).finalStorage

/-- Billing preserves storage and support even on a failing burn prefix. -/
theorem Represents.applyCharges {ns : NearState} {raw : RawStorage} (h : Represents ns raw)
    (charges : List Charge) (hburn : ∀ charge ∈ charges, MeteredHosts.BurnsOnly charge) :
    Represents (Wasm.Near.applyCharges ns charges).1 raw := by
  have hf := MeteredHosts.applyCharges_frame ns charges hburn
  have hs := congrArg NearState.storage hf
  have hk := congrArg NearState.storageKeys hf
  constructor
  · intro key value
    rw [show (Wasm.Near.applyCharges ns charges).1.storage = ns.storage from hs]
    exact h.lookup key value
  · intro key value hm
    rw [show (Wasm.Near.applyCharges ns charges).1.storageKeys = ns.storageKeys from hk]
    exact h.coverage key value hm

/-- The pre-call used-gas context refresh retains lookup and support. -/
theorem Represents.paidStore (before : HostStore NearState) {paid : NearState}
    {raw : RawStorage} (h : Represents paid raw) :
    Represents (MeteredHosts.Output.paidStore before paid).host raw := ⟨h.lookup, h.coverage⟩

/-- The trie-phase accounting/gas splice retains lookup and key support. -/
theorem Represents.prepared (before : HostStore NearState) (paid : NearState)
    (trie : _root_.Near.TrieOverlay.State) {raw : RawStorage} (h : Represents before.host raw) :
    Represents (MeteredHosts.StorageMetered.prepared before paid trie).host raw := ⟨h.lookup, h.coverage⟩

/-- Storage-usage/log accounting retains the represented records. -/
theorem Represents.updateStorageUsage {ns : NearState} {raw : RawStorage}
    (h : Represents ns raw) (extra : Nat) (name : String)
    (before : HostStore NearState) (mem : Memory) (args : List Value) :
    Represents (updateStorageUsage extra name before { mem, host := ns } args).host raw := by
  simp only [Wasm.Near.updateStorageUsage]
  repeat' split
  all_goals exact ⟨h.lookup, h.coverage⟩

/-- Outcome storage of the actual computed post-call store is the finite-map
write; billing and usage changes cannot alter this equality. -/
theorem finalStorage_finished (extra : Nat) (before : HostStore NearState)
    (raw : RawStorage) (h : Represents before.host raw)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : Bytes) :
    let paid := (applyCharges (MeteredHosts.written before key value).host
      (MeteredHosts.StorageMetered.postCharges before key)).1
    (finalStorage (MeteredHosts.StorageMetered.finished extra before
      keyLen keyPtr valueLen valuePtr key value paid).host).toFinset = rawWrite raw key value := by
  have hw := (h.setStorage key value).invalidateIterators
  have hc := hw.applyCharges (MeteredHosts.StorageMetered.postCharges before key)
    (MeteredHosts.StorageMetered.postCharges_burnsOnly before key)
  exact (hc.updateStorageUsage extra "storage_write" before before.mem
    (MeteredHosts.StorageMetered.args keyLen keyPtr valueLen valuePtr)).finalStorage

end Wasm.Near.StorageRepresentation
