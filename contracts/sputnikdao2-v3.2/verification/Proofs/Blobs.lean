import Model.Blobs

namespace SputnikDAO2

theorem has_blob_reads_raw_key_only (owner : Option String) :
    hasBlob ⟨none, owner⟩ = false := by
  rfl

theorem raw_blob_without_owner_is_visible (bytes : CodeBytes) :
    hasBlob ⟨some bytes, none⟩ = true := by
  rfl

theorem store_rejects_existing_raw_key (slot : BlobSlot)
    (caller : String) (input : Option CodeBytes) (attached byteCost : Nat)
    (h : slot.rawBytes.isSome = true) :
    storeBlob slot true caller input attached byteCost = none := by
  cases input with
  | none => simp [storeBlob]
  | some bytes => simp [storeBlob, h]

theorem store_writes_raw_bytes_and_owner (slot : BlobSlot)
    (caller : String) (bytes : CodeBytes) (attached byteCost : Nat)
    (hempty : slot.rawBytes = none)
    (hdeposit : blobStorageCost byteCost bytes.length ≤ attached) :
    storeBlob slot true caller (some bytes) attached byteCost =
      some ⟨some bytes, some caller⟩ := by
  simp [storeBlob, hempty, Nat.not_lt.mpr hdeposit]

theorem remove_rejects_other_caller (slot : BlobSlot)
    (caller owner : String) (byteCost ownerValueLen : Nat)
    (howner : slot.owner = some owner) (hdifferent : caller ≠ owner) :
    removeBlob slot true caller byteCost ownerValueLen = none := by
  simp [removeBlob, howner, hdifferent]

theorem missing_raw_blob_uses_stale_owner_length (owner : String)
    (byteCost ownerValueLen : Nat) :
    removeBlob ⟨none, some owner⟩ true owner byteCost ownerValueLen =
      some (⟨none, none⟩, blobStorageCost byteCost ownerValueLen) := by
  simp [removeBlob]

theorem remove_refunds_current_storage_cost (bytes : CodeBytes)
    (owner : String) (byteCost ownerValueLen : Nat) :
    removeBlob ⟨some bytes, some owner⟩ true owner byteCost ownerValueLen =
      some (⟨none, none⟩, blobStorageCost byteCost bytes.length) := by
  simp [removeBlob]

theorem absent_raw_key_allows_owner_replacement :
    storeBlob ⟨none, some "old.near"⟩ true "new.near"
      (some []) 32 1 = some ⟨some [], some "new.near"⟩ := by
  decide

theorem changed_storage_price_changes_refund :
    blobStorageCost 1 2 = 34 ∧
    removeBlob ⟨some [0, 1], some "alice.near"⟩ true
      "alice.near" 2 14 = some (⟨none, none⟩, 68) := by
  decide

theorem missing_raw_blob_can_refund_stale_length :
    removeBlob ⟨none, some "alice.near"⟩ true
      "alice.near" 1 14 = some (⟨none, none⟩, 46) := by
  decide

end SputnikDAO2
