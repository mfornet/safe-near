import Model.BlobExport
import Proofs.BlobKeySeparation

namespace SputnikDAO2

private theorem store_blob_success_slot
    (before after : BlobSlot) (caller : String)
    (bytes : BountyBytes) (attached byteCost : Nat)
    (h : storeBlob before true caller (some bytes) attached byteCost =
      some after) :
    after = ⟨some bytes, some caller⟩ := by
  by_cases hoccupied : before.rawBytes.isSome = true
  · simp [storeBlob, hoccupied] at h
  · by_cases hshort : attached < blobStorageCost byteCost bytes.length
    · simp [storeBlob, hoccupied, hshort] at h
    · simp [storeBlob, hoccupied, hshort] at h
      exact h.symm

private theorem remove_blob_success_slot
    (before after : BlobSlot) (caller : String)
    (byteCost ownerValueLen refund : Nat)
    (h : removeBlob before true caller byteCost ownerValueLen =
      some (after, refund)) :
    after = ⟨none, none⟩ := by
  cases howner : before.owner with
  | none => simp [removeBlob, howner] at h
  | some owner =>
      by_cases hcaller : caller = owner
      · simp [removeBlob, howner, hcaller] at h
        exact h.1.symm
      · simp [removeBlob, howner, hcaller] at h

theorem store_blob_export_rejects_occupied_hash
    (raw : BountyRawTrie) (ctx : RawBlobContext)
    (state : Option BlobSlot) (bytes digest : BountyBytes)
    (sha256 : BountyBytes → BountyBytes) (byteCost : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hhash : sha256 bytes = digest)
    (hoccupied : (raw digest).isSome = true) :
    runStoreBlobExport raw ctx state (some bytes) sha256 byteCost
      encodeRoot = none := by
  cases state with
  | none => simp [runStoreBlobExport]
  | some before =>
      simp [runStoreBlobExport, hhash, hoccupied]

theorem store_blob_export_rejects_short_deposit
    (raw : BountyRawTrie) (ctx : RawBlobContext)
    (state : Option BlobSlot) (bytes : BountyBytes)
    (sha256 : BountyBytes → BountyBytes) (byteCost : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hdeposit : ctx.attachedDeposit < blobStorageCost byteCost bytes.length) :
    runStoreBlobExport raw ctx state (some bytes) sha256 byteCost
      encodeRoot = none := by
  cases state with
  | none => simp [runStoreBlobExport]
  | some before =>
      simp [runStoreBlobExport, storeBlob, hdeposit]

theorem store_blob_export_success_keys
    (raw final : BountyRawTrie) (ctx : RawBlobContext)
    (state : BlobSlot) (bytes digest : BountyBytes)
    (sha256 : BountyBytes → BountyBytes) (byteCost : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (h : runStoreBlobExport raw ctx (some state) (some bytes)
      sha256 byteCost encodeRoot = some (final, digest)) :
    ∃ after,
      digest = sha256 bytes ∧ digest.length = 32 ∧
      raw digest = none ∧
      storeBlob state true ctx.predecessor (some bytes)
        ctx.attachedDeposit byteCost = some after ∧
      final digest = some bytes ∧
      final (daoBlobOwnerKey digest) =
        some (bountyBorshString ctx.predecessor) ∧
      final daoRootKey = some (encodeRoot after) := by
  let hash := sha256 bytes
  by_cases hlen : hash.length = 32
  · cases hraw : raw hash with
    | some existing =>
        simp [runStoreBlobExport, hash, hlen, hraw] at h
    | none =>
        cases hb : storeBlob state true ctx.predecessor
            (some bytes) ctx.attachedDeposit byteCost with
        | none =>
            simp [runStoreBlobExport, hash, hlen, hraw, hb] at h
        | some after =>
            have hownerHash : daoBlobOwnerKey hash ≠ hash :=
              dao_blob_owner_key_ne_raw hash
            have hhashRoot : hash ≠ daoRootKey := by
              intro heq
              have hlength := congrArg List.length heq
              simp [hlen, daoRootKey] at hlength
            have hownerRoot : daoBlobOwnerKey hash ≠ daoRootKey := by
              simp [daoBlobOwnerKey, daoRootKey]
            have hwrite : daoRawBlobInsert raw hash bytes
                (bountyBorshString ctx.predecessor) =
                some (bountyRawWrite
                  (bountyRawWrite raw hash bytes)
                  (daoBlobOwnerKey hash)
                  (bountyBorshString ctx.predecessor)) := by
              simp [daoRawBlobInsert, hraw]
            simp [runStoreBlobExport, hash, hlen, hraw,
              hb, hwrite] at h
            rcases h with ⟨hfinal, hdigest⟩
            subst final
            subst digest
            dsimp only [hash] at hlen hraw hownerHash hhashRoot hownerRoot
            refine ⟨after, rfl, hlen, hraw, rfl, ?_, ?_, ?_⟩
            · simp [bountyRawWrite, hhashRoot, Ne.symm hownerHash]
            · simp [bountyRawWrite, hownerRoot]
            · simp [bountyRawWrite]
  · simp [runStoreBlobExport, hash, hlen] at h

theorem store_blob_export_succeeds_under_fresh_hash_and_deposit
    (raw : BountyRawTrie) (ctx : RawBlobContext)
    (owner : Option String) (bytes : BountyBytes)
    (sha256 : BountyBytes → BountyBytes) (byteCost : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hlen : (sha256 bytes).length = 32)
    (hraw : raw (sha256 bytes) = none)
    (hdeposit : blobStorageCost byteCost bytes.length ≤ ctx.attachedDeposit) :
    ∃ final,
      runStoreBlobExport raw ctx (some ⟨none, owner⟩)
        (some bytes) sha256 byteCost encodeRoot =
        some (final, sha256 bytes) := by
  let after : BlobSlot := ⟨some bytes, some ctx.predecessor⟩
  let inserted := bountyRawWrite
    (bountyRawWrite raw (sha256 bytes) bytes)
    (daoBlobOwnerKey (sha256 bytes))
    (bountyBorshString ctx.predecessor)
  refine ⟨bountyRawWrite inserted daoRootKey (encodeRoot after), ?_⟩
  simp [runStoreBlobExport, storeBlob, daoRawBlobInsert,
    hlen, hraw, Nat.not_lt.mpr hdeposit, after, inserted]

theorem store_blob_export_establishes_raw_image
    (raw final : BountyRawTrie) (ctx : RawBlobContext)
    (state : BlobSlot) (bytes digest : BountyBytes)
    (sha256 : BountyBytes → BountyBytes) (byteCost : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (h : runStoreBlobExport raw ctx (some state) (some bytes)
      sha256 byteCost encodeRoot = some (final, digest)) :
    ∃ after,
      storeBlob state true ctx.predecessor (some bytes)
        ctx.attachedDeposit byteCost = some after ∧
      blobSlotRawImage final digest after := by
  obtain ⟨after, _, _, _, hbody, hraw, howner, _⟩ :=
    store_blob_export_success_keys raw final ctx state bytes digest
      sha256 byteCost encodeRoot h
  have hafter := store_blob_success_slot state after ctx.predecessor
    bytes ctx.attachedDeposit byteCost hbody
  refine ⟨after, hbody, ?_⟩
  simpa [blobSlotRawImage, hafter] using And.intro hraw howner

theorem remove_blob_export_rejects_non_digest
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BlobSlot) (digest : BountyBytes)
    (byteCost ownerValueLen : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hlen : digest.length ≠ 32) :
    runRemoveBlobExport raw ctx state digest byteCost ownerValueLen
      encodeRoot = none := by
  simp [runRemoveBlobExport, hlen]

theorem remove_blob_export_rejects_deposit
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BlobSlot) (digest : BountyBytes)
    (byteCost ownerValueLen : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hdeposit : ctx.attachedDeposit ≠ 0) :
    runRemoveBlobExport raw ctx state digest byteCost ownerValueLen
      encodeRoot = none := by
  have hi : findDAOExport "remove_blob" =
      some ⟨"remove_blob", .call, false, false⟩ := by decide
  simp [runRemoveBlobExport, runGeneratedCallWrapper, hi, hdeposit]

theorem remove_blob_export_success_keys_and_refund
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BlobSlot) (digest : BountyBytes)
    (byteCost ownerValueLen refund : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (h : runRemoveBlobExport raw ctx (some state) digest
      byteCost ownerValueLen encodeRoot = some (final, refund)) :
    ∃ after,
      digest.length = 32 ∧
      removeBlob state true ctx.predecessor byteCost ownerValueLen =
        some (after, refund) ∧
      final digest = none ∧
      final (daoBlobOwnerKey digest) = none ∧
      final daoRootKey = some (encodeRoot after) := by
  have hi : findDAOExport "remove_blob" =
      some ⟨"remove_blob", .call, false, false⟩ := by decide
  by_cases hlen : digest.length = 32
  · cases hr : removeBlob state true ctx.predecessor
        byteCost ownerValueLen with
    | none => simp [runRemoveBlobExport, hlen, hr] at h
    | some pair =>
        obtain ⟨after, actualRefund⟩ := pair
        have hroot : digest ≠ daoRootKey := by
          intro heq
          have hlength := congrArg List.length heq
          simp [hlen, daoRootKey] at hlength
        have hownerRoot : daoBlobOwnerKey digest ≠ daoRootKey := by
          simp [daoBlobOwnerKey, daoRootKey]
        by_cases hdeposit : ctx.attachedDeposit = 0
        · by_cases hargs : ctx.argumentsDecoded = true
          · simp [runRemoveBlobExport, hlen, hr,
              runGeneratedCallWrapper, hi, hdeposit, hargs] at h
            rcases h with ⟨hfinal, hrefund⟩
            subst final
            subst actualRefund
            refine ⟨after, hlen, rfl, ?_, ?_, ?_⟩
            · simp [bountyRawWrite, daoRawBlobRemove,
                bountyRawRemove, hroot]
            · simp [bountyRawWrite, daoRawBlobRemove,
                bountyRawRemove, hownerRoot]
            · simp [bountyRawWrite]
          · simp [runRemoveBlobExport, hlen,
              runGeneratedCallWrapper, hi, hargs] at h
        · simp [runRemoveBlobExport, hlen,
            runGeneratedCallWrapper, hi, hdeposit] at h
  · simp [runRemoveBlobExport, hlen] at h

theorem remove_blob_export_missing_raw_uses_owner_register_length
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (owner : String) (digest : BountyBytes)
    (byteCost ownerValueLen refund : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (hcaller : ctx.predecessor = owner)
    (h : runRemoveBlobExport raw ctx
      (some ⟨none, some owner⟩) digest byteCost ownerValueLen
      encodeRoot = some (final, refund)) :
    refund = blobStorageCost byteCost ownerValueLen := by
  obtain ⟨after, _, hbody, _, _, _⟩ :=
    remove_blob_export_success_keys_and_refund raw final ctx
      ⟨none, some owner⟩ digest byteCost ownerValueLen refund
      encodeRoot h
  simp [removeBlob, hcaller] at hbody
  exact hbody.2.symm

theorem remove_blob_export_establishes_empty_raw_image
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BlobSlot) (digest : BountyBytes)
    (byteCost ownerValueLen refund : Nat)
    (encodeRoot : BlobSlot → BountyBytes)
    (h : runRemoveBlobExport raw ctx (some state) digest
      byteCost ownerValueLen encodeRoot = some (final, refund)) :
    ∃ after,
      removeBlob state true ctx.predecessor byteCost ownerValueLen =
        some (after, refund) ∧
      blobSlotRawImage final digest after := by
  obtain ⟨after, _, hbody, hraw, howner, _⟩ :=
    remove_blob_export_success_keys_and_refund raw final ctx state
      digest byteCost ownerValueLen refund encodeRoot h
  have hafter := remove_blob_success_slot state after ctx.predecessor
    byteCost ownerValueLen refund hbody
  refine ⟨after, hbody, ?_⟩
  simpa [blobSlotRawImage, hafter] using And.intro hraw howner

end SputnikDAO2
