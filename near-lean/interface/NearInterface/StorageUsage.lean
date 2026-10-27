import NearInterface.Boundary

/-!
# Finite raw-storage write usage

A write removes all records with the key before installing the new value.
For functional raw storage, replacement removes exactly one old record.
The natural-number formulas retain the boundary's non-storage usage overhead.
-/
namespace NearInterface
open Wasm Wasm.Near

/-- Finite-map write, independent of a choice of list representation. -/
def rawWrite (raw : RawStorage) (key value : Bytes) : RawStorage :=
  insert (key, value) (raw.filter fun record => record.1 ≠ key)

theorem mem_rawWrite (raw : RawStorage) (key value query found : Bytes) :
    (query, found) ∈ rawWrite raw key value ↔
      (query = key ∧ found = value) ∨ ((query, found) ∈ raw ∧ query ≠ key) := by
  simp [rawWrite, Prod.mk.injEq]

theorem rawWrite_keys_unique (raw : RawStorage) (key value : Bytes)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v') :
    ∀ k v v', (k, v) ∈ rawWrite raw key value →
      (k, v') ∈ rawWrite raw key value → v = v' := by
  intro k v v' hv hv'
  rw [mem_rawWrite] at hv hv'
  rcases hv with ⟨rfl, rfl⟩ | ⟨hv, hk⟩
  · rcases hv' with ⟨_, rfl⟩ | ⟨_, hk⟩
    · rfl
    · exact False.elim (hk rfl)
  · rcases hv' with ⟨rfl, _⟩ | ⟨hv', _⟩
    · exact False.elim (hk rfl)
    · exact hunique k v v' hv hv'

theorem filter_key_fresh (raw : RawStorage) (key : Bytes)
    (habsent : ∀ value, (key, value) ∉ raw) :
    raw.filter (fun record => record.1 ≠ key) = raw := by
  ext record
  obtain ⟨k, v⟩ := record
  simp only [Finset.mem_filter]
  constructor
  · exact And.left
  · intro hm
    refine ⟨hm, ?_⟩
    intro he
    subst k
    exact habsent v hm

theorem filter_key_replace (raw : RawStorage) (key old : Bytes)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v')
    (hold : (key, old) ∈ raw) :
    raw.filter (fun record => record.1 ≠ key) = raw.erase (key, old) := by
  ext record
  obtain ⟨k, v⟩ := record
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨fun he => hk (congrArg Prod.fst he), hm⟩
  · rintro ⟨hne, hm⟩
    refine ⟨hm, ?_⟩
    intro he
    subst k
    have hv := hunique key v old hm hold
    subst v
    exact hne rfl

/-- Fresh-cell storage usage includes key, value, and record overhead. -/
theorem storageUsageOf_write_fresh (cfg : RuntimeConfig) (raw : RawStorage)
    (key value : Bytes) (habsent : ∀ old, (key, old) ∉ raw) :
    storageUsageOf cfg (rawWrite raw key value) =
      storageUsageOf cfg raw + key.length + value.length + cfg.fees.numExtraBytesRecord := by
  rw [rawWrite, filter_key_fresh raw key habsent]
  simp only [storageUsageOf, Finset.sum_insert (habsent value), recordBytes]
  omega

/-- Replacement changes just the value byte count. The additive form avoids
any hidden truncated subtraction in the finite-sum statement. -/
theorem storageUsageOf_write_replace (cfg : RuntimeConfig) (raw : RawStorage)
    (key value old : Bytes)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v')
    (hold : (key, old) ∈ raw) :
    storageUsageOf cfg (rawWrite raw key value) + old.length =
      storageUsageOf cfg raw + value.length := by
  have hnot : (key, value) ∉ raw.filter (fun record => record.1 ≠ key) := by simp
  have hsum := Finset.sum_erase_add (s := raw) (f := recordBytes cfg) hold
  rw [rawWrite]
  simp only [storageUsageOf, Finset.sum_insert hnot]
  rw [filter_key_replace raw key old hunique hold]
  simp only [recordBytes] at hsum ⊢
  omega

/-- The old record fits inside the total contract usage. -/
theorem recordBytes_le_storageUsageOf (cfg : RuntimeConfig) (raw : RawStorage)
    (key old : Bytes) (hold : (key, old) ∈ raw) :
    recordBytes cfg (key, old) ≤ storageUsageOf cfg raw := by
  have hs := Finset.sum_erase_add (s := raw) (f := recordBytes cfg) hold
  change recordBytes cfg (key, old) ≤ ∑ record ∈ raw, recordBytes cfg record
  omega

/-- The model's overhead-preserving formula equals fresh-write accounting. -/
theorem write_usage_fresh (cfg : RuntimeConfig) (raw : RawStorage) (usage : Nat)
    (key value : Bytes) (husage : storageUsageOf cfg raw ≤ usage)
    (habsent : ∀ old, (key, old) ∉ raw) :
    usage - storageUsageOf cfg raw + storageUsageOf cfg (rawWrite raw key value) =
      usage + key.length + value.length + cfg.fees.numExtraBytesRecord := by
  rw [storageUsageOf_write_fresh cfg raw key value habsent]
  omega

/-- The model's formula equals actual natural replacement accounting. The
usage invariant pays for the old value before subtraction. -/
theorem write_usage_replace (cfg : RuntimeConfig) (raw : RawStorage) (usage : Nat)
    (key value old : Bytes) (husage : storageUsageOf cfg raw ≤ usage)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v')
    (hold : (key, old) ∈ raw) :
    usage - storageUsageOf cfg raw + storageUsageOf cfg (rawWrite raw key value) =
      usage + value.length - old.length := by
  have hs := storageUsageOf_write_replace cfg raw key value old hunique hold
  have hl := recordBytes_le_storageUsageOf cfg raw key old hold
  simp only [recordBytes] at hl
  omega

/-- The finite-map update matches the list update used by storage adapters. -/
theorem rawWrite_toFinset (storage : List (Bytes × Bytes)) (key value : Bytes) :
    ((key, value) :: storage.filter (fun record => record.1 != key)).toFinset =
      rawWrite storage.toFinset key value := by
  ext record
  obtain ⟨k, v⟩ := record
  simp [rawWrite, Prod.mk.injEq]

/-- Under the explicit room bound, the ABI word retains the fresh-write
natural usage and therefore the model's overhead-preserving usage. -/
theorem write_usage_fresh_toNat (cfg : RuntimeConfig) (raw : RawStorage) (usage : Nat)
    (key value : Bytes) (husage : storageUsageOf cfg raw ≤ usage)
    (habsent : ∀ old, (key, old) ∉ raw)
    (hroom : usage + key.length + value.length + cfg.fees.numExtraBytesRecord < 2 ^ 64) :
    (UInt64.ofNat (usage + key.length + value.length + cfg.fees.numExtraBytesRecord)).toNat =
      usage - storageUsageOf cfg raw + storageUsageOf cfg (rawWrite raw key value) := by
  rw [UInt64.toNat_ofNat_of_lt' hroom]
  exact (write_usage_fresh cfg raw usage key value husage habsent).symm

/-- Replacement uses the same explicit ABI room bound after value subtraction. -/
theorem write_usage_replace_toNat (cfg : RuntimeConfig) (raw : RawStorage) (usage : Nat)
    (key value old : Bytes) (husage : storageUsageOf cfg raw ≤ usage)
    (hunique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v')
    (hold : (key, old) ∈ raw) (hroom : usage + value.length - old.length < 2 ^ 64) :
    (UInt64.ofNat (usage + value.length - old.length)).toNat =
      usage - storageUsageOf cfg raw + storageUsageOf cfg (rawWrite raw key value) := by
  rw [UInt64.toNat_ofNat_of_lt' hroom]
  exact (write_usage_replace cfg raw usage key value old husage hunique hold).symm

end NearInterface
