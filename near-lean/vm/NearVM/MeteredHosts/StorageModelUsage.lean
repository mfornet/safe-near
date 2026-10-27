import NearVM.StorageRepresentation

/-! Model storage and usage for arbitrary successful writes. Fresh and
replacing cells share one contract; no empty-trie assumption is needed. -/
namespace Wasm.Near.MeteredHosts.StorageModelUsage
open NearInterface StorageRepresentation StorageMetered

/-- Functional host lookup forces the represented raw records to be a map. -/
theorem raw_keys_unique (before : HostStore NearState) (raw : RawStorage)
    (hrep : Represents before.host raw) :
    ∀ key first second, (key, first) ∈ raw → (key, second) ∈ raw → first = second := by
  intro key first second hf hs
  have hfirst := (hrep.lookup key first).mpr hf
  have hsecond := (hrep.lookup key second).mpr hs
  exact Option.some.inj (hfirst.symm.trans hsecond)

/-- The actual natural usage calculation equals the independent model's
non-storage-overhead-preserving formula, for either cell presence. -/
theorem writeUsage_model (cfg : RuntimeConfig) (before : HostStore NearState)
    (raw : RawStorage) (hrep : Represents before.host raw)
    (husage : storageUsageOf cfg raw ≤ before.host.context.storageUsage.toNat)
    (key value : Bytes) :
    writeUsage cfg.fees.numExtraBytesRecord before key value =
      before.host.context.storageUsage.toNat - storageUsageOf cfg raw +
        storageUsageOf cfg (rawWrite raw key value) := by
  cases hs : before.host.storage key with
  | none =>
    have habsent : ∀ old, (key, old) ∉ raw := by
      intro old hm
      have h := (hrep.lookup key old).mpr hm
      rw [hs] at h
      cases h
    simpa only [writeUsage, hs] using
      (write_usage_fresh cfg raw before.host.context.storageUsage.toNat key value husage habsent).symm
  | some old =>
    have hm := (hrep.lookup key old).mp hs
    simpa only [writeUsage, hs] using
      (write_usage_replace cfg raw before.host.context.storageUsage.toNat key value old husage
        (raw_keys_unique before raw hrep) hm).symm

/-- One original growth bound also covers replacement subtraction. -/
theorem writeUsage_lt (extra : Nat) (before : HostStore NearState) (key value : Bytes)
    (hroom : before.host.context.storageUsage.toNat + key.length + value.length + extra < 2 ^ 64) :
    writeUsage extra before key value < 2 ^ 64 := by
  unfold writeUsage
  split <;> omega

/-- Successful actual post-call charging preserves exact model usage without
ABI wrapping, for arbitrary represented storage and either old-cell branch. -/
theorem finished_usage_model (cfg : RuntimeConfig) (before : HostStore NearState)
    (raw : RawStorage) (hrep : Represents before.host raw)
    (husage : storageUsageOf cfg raw ≤ before.host.context.storageUsage.toNat)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : Bytes) (paid : NearState)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hcharge : applyCharges (written before key value).host (postCharges before key) = (paid, none))
    (hroom : before.host.context.storageUsage.toNat + key.length + value.length +
      cfg.fees.numExtraBytesRecord < 2 ^ 64) :
    (finished cfg.fees.numExtraBytesRecord before keyLen keyPtr valueLen valuePtr key value paid).host.context.storageUsage.toNat =
      before.host.context.storageUsage.toNat - storageUsageOf cfg raw +
        storageUsageOf cfg (rawWrite raw key value) := by
  rw [finished_usage_toNat cfg.fees.numExtraBytesRecord before keyLen keyPtr valueLen valuePtr
    key value paid hkey hcharge (writeUsage_lt _ _ _ _ hroom)]
  exact writeUsage_model cfg before raw hrep husage key value

end Wasm.Near.MeteredHosts.StorageModelUsage
