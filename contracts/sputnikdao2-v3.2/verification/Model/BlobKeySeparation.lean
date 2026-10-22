import Model.ConstructorTrie
import Model.DelegationEncoding

namespace SputnikDAO2

/-! The raw `store_blob` key is a 32-byte SHA-256 digest. Legacy LookupMap
keys append Borsh-serialized keys to their one-byte StorageKeys prefix.
This model is byte-level; it does not assume SHA-256 has or lacks preimages
for any particular storage key. -/

def daoProposalEntryKey (id : Nat) : BountyBytes :=
  3 :: bountyLE 8 id

def daoBountyEntryKey (id : Nat) : BountyBytes :=
  4 :: bountyLE 8 id

def daoBlobOwnerKey (digest : BountyBytes) : BountyBytes :=
  7 :: digest

-- Raw-key part of a successful `store_blob` after state, hash, deposit and
-- byte-width checks. The owner value is supplied as already serialized bytes.
-- The raw hash check is performed before either write.
def daoRawBlobInsert (raw : BountyRawTrie) (digest bytes ownerBytes : BountyBytes) :
    Option BountyRawTrie :=
  if (raw digest).isSome then none
  else some <| bountyRawWrite (bountyRawWrite raw digest bytes)
    (daoBlobOwnerKey digest) ownerBytes

-- Key-level effect after `remove_blob` finds an authorized owner. The
-- source removes the index first and the raw key second; refund computation
-- and rollback are outside this projection.
def daoRawBlobRemove (raw : BountyRawTrie) (digest : BountyBytes) :
    BountyRawTrie :=
  bountyRawRemove (bountyRawRemove raw (daoBlobOwnerKey digest)) digest

-- Legacy LookupMap.insert returns the old value. If a colliding raw blob
-- occupies a delegation key, deserializing that old value must succeed for
-- the source call to complete. `none` denotes an abort with assumed rollback.
def daoDelegationRegisterChecked (raw : BountyRawTrie)
    (account : String) : Option BountyRawTrie :=
  match raw (delegationKey account) with
  | none => some (delegationRawRegister raw account)
  | some old =>
      if (parseDelegationBalance old).isSome then
        some (delegationRawRegister raw account)
      else none

-- `bounty_claim` reads the old Vec<BountyClaim> before rewriting it. The
-- caller supplies the newly serialized vector after its logical checks.
-- Earlier claim-count writes require host rollback if decoding aborts.
def daoClaimersWriteChecked (raw : BountyRawTrie)
    (account : String) (newBytes : BountyBytes) : Option BountyRawTrie :=
  match raw (bountyClaimersKey account) with
  | none => some (bountyRawWrite raw (bountyClaimersKey account) newBytes)
  | some old =>
      if (bountyParseClaims old).isSome then
        some (bountyRawWrite raw (bountyClaimersKey account) newBytes)
      else none

end SputnikDAO2
