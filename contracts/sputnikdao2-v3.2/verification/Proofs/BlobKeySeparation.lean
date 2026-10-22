import Model.BlobKeySeparation
import Proofs.BountyEncoding

namespace SputnikDAO2

theorem dao_proposal_key_length (id : Nat) :
    (daoProposalEntryKey id).length = 9 := by
  simp [daoProposalEntryKey, bountyLE_length]

theorem dao_bounty_key_length (id : Nat) :
    (daoBountyEntryKey id).length = 9 := by
  simp [daoBountyEntryKey, bountyLE_length]

theorem dao_bounty_count_key_length (id : Nat) :
    (bountyCountKey id).length = 9 := by
  simp [bountyCountKey, bountyLE_length]

theorem dao_blob_owner_key_length (digest : BountyBytes) :
    (daoBlobOwnerKey digest).length = digest.length + 1 := by
  simp [daoBlobOwnerKey]

theorem dao_blob_owner_key_ne_raw (digest : BountyBytes) :
    daoBlobOwnerKey digest ≠ digest := by
  intro h
  have hlen := congrArg List.length h
  simp [dao_blob_owner_key_length] at hlen

theorem dao_account_key_length (account : String) :
    (delegationKey account).length =
      account.toUTF8.data.toList.length + 5 ∧
    (bountyClaimersKey account).length =
      account.toUTF8.data.toList.length + 5 := by
  simp [delegationKey, bountyClaimersKey,
    bountyBorshString, bountyLE_length]
  omega

theorem raw_blob_key_avoids_fixed_collection_keys
    (digest ownerDigest : BountyBytes) (id : Nat)
    (hlen : digest.length = 32)
    (howner : ownerDigest.length = 32) :
    digest ≠ daoProposalEntryKey id ∧
    digest ≠ daoBountyEntryKey id ∧
    digest ≠ bountyCountKey id ∧
    digest ≠ daoBlobOwnerKey ownerDigest := by
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, dao_proposal_key_length] at this
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, dao_bounty_key_length] at this
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, dao_bounty_count_key_length] at this
  · intro h
    have := congrArg List.length h
    simp [hlen, howner, dao_blob_owner_key_length] at this

theorem raw_blob_key_avoids_constructor_keys
    (digest : BountyBytes) (hlen : digest.length = 32) :
    ¬ constructorKey digest := by
  simp only [constructorKey, not_or]
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, daoConfigKey] at this
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, daoPolicyKey] at this
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, daoFactoryKey] at this
  constructor
  · intro h
    have := congrArg List.length h
    simp [hlen, daoVersionKey] at this
  · intro h
    have := congrArg List.length h
    simp [hlen, daoRootKey] at this

theorem raw_blob_delegation_collision_requires_27_bytes
    (digest : BountyBytes) (account : String)
    (hlen : digest.length = 32)
    (hkey : digest = delegationKey account) :
    account.toUTF8.data.toList.length = 27 := by
  have hlenKey := (dao_account_key_length account).1
  have h := congrArg List.length hkey
  omega

theorem raw_blob_claimers_collision_requires_27_bytes
    (digest : BountyBytes) (account : String)
    (hlen : digest.length = 32)
    (hkey : digest = bountyClaimersKey account) :
    account.toUTF8.data.toList.length = 27 := by
  have hlenKey := (dao_account_key_length account).2
  have h := congrArg List.length hkey
  omega

theorem raw_blob_insert_rejects_occupied_account_key
    (raw : BountyRawTrie) (digest bytes ownerBytes value : BountyBytes)
    (account : String)
    (hkey : digest = delegationKey account)
    (hoccupied : raw (delegationKey account) = some value) :
    daoRawBlobInsert raw digest bytes ownerBytes = none := by
  simp [daoRawBlobInsert, hkey, hoccupied]

theorem checked_delegation_insert_rejects_malformed_old_bytes
    (raw : BountyRawTrie) (account : String) (old : BountyBytes)
    (hstored : raw (delegationKey account) = some old)
    (hmalformed : parseDelegationBalance old = none) :
    daoDelegationRegisterChecked raw account = none := by
  simp [daoDelegationRegisterChecked, hstored, hmalformed]

theorem colliding_blob_payload_must_decode_for_delegation
    (raw : BountyRawTrie) (digest bytes ownerBytes : BountyBytes)
    (account : String)
    (hkey : digest = delegationKey account)
    (hempty : raw digest = none)
    (hmalformed : parseDelegationBalance bytes = none) :
    (daoRawBlobInsert raw digest bytes ownerBytes).bind
      (fun after => daoDelegationRegisterChecked after account) = none := by
  subst digest
  have hneq := dao_blob_owner_key_ne_raw (delegationKey account)
  have hneq' := Ne.symm hneq
  simp [daoRawBlobInsert, hempty, daoDelegationRegisterChecked,
    bountyRawWrite, hneq', hmalformed]

theorem decodable_colliding_blob_allows_delegation_overwrite
    (raw : BountyRawTrie) (digest bytes ownerBytes : BountyBytes)
    (account : String) (oldBalance : Nat)
    (hkey : digest = delegationKey account)
    (hempty : raw digest = none)
    (hdecodes : parseDelegationBalance bytes = some oldBalance) :
    ((daoRawBlobInsert raw digest bytes ownerBytes).bind
      (fun after => daoDelegationRegisterChecked after account)).bind
      (fun after => after digest) = some (encodeDelegationBalance 0) := by
  subst digest
  have hneq := dao_blob_owner_key_ne_raw (delegationKey account)
  have hneq' := Ne.symm hneq
  simp [daoRawBlobInsert, hempty, daoDelegationRegisterChecked,
    bountyRawWrite, hneq', hdecodes, delegationRawRegister]

theorem malformed_colliding_blob_blocks_claimers_write
    (raw : BountyRawTrie) (digest bytes ownerBytes newBytes : BountyBytes)
    (account : String)
    (hkey : digest = bountyClaimersKey account)
    (hempty : raw digest = none)
    (hmalformed : bountyParseClaims bytes = none) :
    (daoRawBlobInsert raw digest bytes ownerBytes).bind
      (fun after => daoClaimersWriteChecked after account newBytes) = none := by
  subst digest
  have hneq' := Ne.symm (dao_blob_owner_key_ne_raw (bountyClaimersKey account))
  simp [daoRawBlobInsert, hempty, daoClaimersWriteChecked,
    bountyRawWrite, hneq', hmalformed]

theorem decodable_colliding_blob_allows_claimers_overwrite
    (raw : BountyRawTrie) (digest bytes ownerBytes newBytes : BountyBytes)
    (account : String) (oldClaims : List PhysicalBountyClaim)
    (hkey : digest = bountyClaimersKey account)
    (hempty : raw digest = none)
    (hdecodes : bountyParseClaims bytes = some oldClaims) :
    ((daoRawBlobInsert raw digest bytes ownerBytes).bind
      (fun after => daoClaimersWriteChecked after account newBytes)).bind
      (fun after => after digest) = some newBytes := by
  subst digest
  have hneq' := Ne.symm (dao_blob_owner_key_ne_raw (bountyClaimersKey account))
  simp [daoRawBlobInsert, hempty, daoClaimersWriteChecked,
    bountyRawWrite, hneq', hdecodes]

example : bountyParseClaims [0, 0, 0, 0] = some [] := by decide
example : bountyParseClaims [98, 97, 100] = none := by decide

-- These two raw-write lemmas describe key effects after the source's old
-- value deserialization succeeds. The checked transition above records that
-- additional precondition.
theorem raw_delegation_write_replaces_colliding_blob
    (raw : BountyRawTrie) (digest bytes ownerBytes : BountyBytes)
    (account : String)
    (hkey : digest = delegationKey account)
    (hempty : raw digest = none) :
    ((daoRawBlobInsert raw digest bytes ownerBytes).map
      (fun after => delegationRawRegister after account)).bind
      (fun after => after digest) = some (encodeDelegationBalance 0) := by
  subst digest
  simp [daoRawBlobInsert, hempty, delegationRawRegister,
    bountyRawWrite]

theorem raw_delegation_write_keeps_blob_owner_index
    (raw : BountyRawTrie) (digest bytes ownerBytes : BountyBytes)
    (account : String)
    (hkey : digest = delegationKey account)
    (hempty : raw digest = none) :
    ((daoRawBlobInsert raw digest bytes ownerBytes).map
      (fun after => delegationRawRegister after account)).bind
      (fun after => after (daoBlobOwnerKey digest)) = some ownerBytes := by
  subst digest
  have hneq : daoBlobOwnerKey (delegationKey account) ≠
      delegationKey account := by
    intro heq
    have hlen := congrArg List.length heq
    simp [dao_blob_owner_key_length] at hlen
  simp [daoRawBlobInsert, hempty, delegationRawRegister,
    bountyRawWrite, hneq]

theorem raw_blob_removal_deletes_colliding_delegation_key
    (raw : BountyRawTrie) (digest : BountyBytes) (account : String)
    (hkey : digest = delegationKey account) :
    daoRawBlobRemove raw digest (delegationKey account) = none := by
  simp [daoRawBlobRemove, bountyRawRemove, hkey]

theorem raw_blob_removal_preserves_bounty_count_key
    (raw : BountyRawTrie) (digest : BountyBytes) (id : Nat)
    (hlen : digest.length = 32) :
    daoRawBlobRemove raw digest (bountyCountKey id) =
      raw (bountyCountKey id) := by
  have hraw : digest ≠ bountyCountKey id :=
    (raw_blob_key_avoids_fixed_collection_keys digest digest id hlen hlen).2.2.1
  have howner : daoBlobOwnerKey digest ≠ bountyCountKey id := by
    simp [daoBlobOwnerKey, bountyCountKey]
  simp [daoRawBlobRemove, bountyRawRemove,
    Ne.symm hraw, Ne.symm howner]

-- A valid 27-byte ASCII account makes each account-index key exactly 32
-- bytes. Whether a SHA-256 digest equals such a key is a separate hash-image
-- question, not ruled out by the storage layout.
example : (delegationKey "aaaaaaaaaaaaaaaaaaaaaaaaaaa").length = 32 := by
  decide

example : (bountyClaimersKey "aaaaaaaaaaaaaaaaaaaaaaaaaaa").length = 32 := by
  decide

end SputnikDAO2
