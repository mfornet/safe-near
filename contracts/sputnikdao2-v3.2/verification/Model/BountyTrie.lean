import Model.BountyEncoding

namespace SputnikDAO2

-- Functional raw trie projection. SDK `storage_write` and `storage_remove`
-- update one byte key; runtime rollback and gas effects are separate.
abbrev BountyRawTrie := BountyBytes → Option BountyBytes

def bountyRawWrite (raw : BountyRawTrie) (key value : BountyBytes) :
    BountyRawTrie :=
  fun query => if query == key then some value else raw query

def bountyRawRemove (raw : BountyRawTrie) (key : BountyBytes) :
    BountyRawTrie :=
  fun query => if query == key then none else raw query

-- An image relation at all bounty account keys and all bounded u64 IDs.
-- It does not yet assert that arbitrary raw bytes decode successfully or
-- that every occupied raw key is listed in a finite account enumeration.
def bountyRawImage (raw : BountyRawTrie)
    (state : BountyStorageState) : Prop :=
  (∀ account,
    raw (bountyClaimersKey account) =
      (state.claimers account).map encodeStoredBountyClaims) ∧
  (∀ bountyId, bountyId < 256 ^ 8 →
    raw (bountyCountKey bountyId) =
      (state.counts bountyId).map encodeBountyCount)

-- Bounds needed for Borsh round trips. The ghost bond is intentionally
-- unconstrained because it is not part of the serialized claim record.
def bountyStorageSerializable (state : BountyStorageState) : Prop :=
  (∀ account claims, state.claimers account = some claims →
    claims.length < 256 ^ 4 ∧
    ∀ claim ∈ claims, validStoredBountyClaim claim) ∧
  (∀ bountyId count, state.counts bountyId = some count →
    count < 256 ^ 4)

-- Projection of fresh DAO initialization onto the two bounty maps and
-- their raw namespaces. Other constructor writes are outside this projection.
def bountyEmptyState : BountyStorageState :=
  { claimers := fun _ => none, counts := fun _ => none, locked := 0 }

def bountyEmptyRaw : BountyRawTrie := fun _ => none

-- Raw key writes in `bounty_claim`: count first, then account claim vector.
-- This is invoked only when the logical step and Borsh serialization succeed.
def bountyRawAddClaim (raw : BountyRawTrie)
    (state : BountyStorageState) (account : String)
    (bountyId now deadline attached : Nat) : BountyRawTrie :=
  let count := (state.counts bountyId).getD 0
  let claims := (state.claimers account).getD []
  let newClaim : StoredBountyClaim :=
    ⟨bountyId, now, deadline, false, attached⟩
  bountyRawWrite
    (bountyRawWrite raw (bountyCountKey bountyId)
      (encodeBountyCount (count + 1)))
    (bountyClaimersKey account)
    (encodeStoredBountyClaims (claims ++ [newClaim]))

-- `internal_remove_claim` updates the account vector first (deleting the
-- key when empty), then writes a present count key with the new u32 value.
def bountyRawRemoveClaim (raw : BountyRawTrie)
    (state : BountyStorageState) (account : String)
    (bountyId : Nat) : Option BountyRawTrie := Id.run do
  let some claims := state.claimers account | return none
  let some (_, remaining) := removeFirstBountyClaim claims bountyId |
    return none
  let some count := state.counts bountyId | return none
  if count == 0 then return none
  let afterClaims :=
    if remaining.isEmpty then
      bountyRawRemove raw (bountyClaimersKey account)
    else bountyRawWrite raw (bountyClaimersKey account)
      (encodeStoredBountyClaims remaining)
  return some <| bountyRawWrite afterClaims
    (bountyCountKey bountyId) (encodeBountyCount (count - 1))

-- Timely `bounty_done` rewrites only the account's vector after its proposal
-- step succeeds. The latter's own storage writes are outside this projection.
def bountyRawCompleteClaim (raw : BountyRawTrie)
    (state : BountyStorageState) (account : String)
    (bountyId : Nat) : Option BountyRawTrie := do
  let claims ← state.claimers account
  let completed ← completeFirstBountyClaim claims bountyId
  some <| bountyRawWrite raw (bountyClaimersKey account)
    (encodeStoredBountyClaims completed)

end SputnikDAO2
