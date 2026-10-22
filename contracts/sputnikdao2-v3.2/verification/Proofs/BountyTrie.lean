import Model.BountyTrie
import Proofs.BountyEncoding
import Proofs.BountyStorage

namespace SputnikDAO2

theorem bounty_raw_write_at (raw : BountyRawTrie)
    (key value : BountyBytes) :
    bountyRawWrite raw key value key = some value := by
  simp [bountyRawWrite]

theorem bounty_raw_write_other (raw : BountyRawTrie)
    (key query value : BountyBytes) (hne : query ≠ key) :
    bountyRawWrite raw key value query = raw query := by
  simp [bountyRawWrite, hne]

theorem bounty_raw_add_claim_preserves_image
    (raw : BountyRawTrie) (state next : BountyStorageState)
    (account : String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    bountyRawImage
      (bountyRawAddClaim raw state account bountyId now deadline bond)
      next := by
  simp [addStoredClaim] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · simp at hstep
      subst next
      constructor
      · intro query
        by_cases hsame : query = account
        · subst query
          simp [bountyRawAddClaim, bountyRawWrite]
        · have hkey : bountyClaimersKey query ≠
              bountyClaimersKey account := by
            intro heq
            exact hsame (bounty_claimers_key_injective query account heq)
          have hcross : bountyClaimersKey query ≠
              bountyCountKey bountyId :=
            bounty_claimers_and_count_keys_disjoint query bountyId
          simp [bountyRawAddClaim, bountyRawWrite,
            hkey, hcross, hsame, himage.1 query]
      · intro query hquery
        have hcross : bountyCountKey query ≠
            bountyClaimersKey account := by
          exact Ne.symm (bounty_claimers_and_count_keys_disjoint
            account query)
        by_cases hsame : query = bountyId
        · subst query
          simp [bountyRawAddClaim, bountyRawWrite, hcross]
        · have hkey : bountyCountKey query ≠
              bountyCountKey bountyId := by
            intro heq
            exact hsame (bounty_count_key_injective_bounded query
              bountyId hquery hid heq)
          simp [bountyRawAddClaim, bountyRawWrite, hcross,
            hkey, hsame, himage.2 query hquery]

theorem bounty_raw_claimers_read_decodes
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String)
    (himage : bountyRawImage raw state)
    (hvalid : ∀ claims, state.claimers account = some claims →
      claims.length < 256 ^ 4 ∧
      ∀ claim ∈ claims, validStoredBountyClaim claim) :
    (raw (bountyClaimersKey account)).bind bountyParseClaims =
      (state.claimers account).map
        (fun claims => claims.map physicalBountyClaim) := by
  cases hclaims : state.claimers account with
  | none => simp [himage.1 account, hclaims]
  | some claims =>
      obtain ⟨hlen, hrecords⟩ := hvalid claims hclaims
      simp [himage.1 account, hclaims,
        bounty_parse_claims_encoded claims hlen hrecords]

theorem bounty_raw_count_read_decodes
    (raw : BountyRawTrie) (state : BountyStorageState)
    (bountyId : Nat) (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hvalid : ∀ count, state.counts bountyId = some count →
      count < 256 ^ 4) :
    (raw (bountyCountKey bountyId)).bind bountyParseCount =
      state.counts bountyId := by
  cases hcount : state.counts bountyId with
  | none => simp [himage.2 bountyId hid, hcount]
  | some count =>
      have hbound := hvalid count hcount
      simp [himage.2 bountyId hid, hcount,
        bounty_parse_count_encoded count hbound]

theorem bounty_raw_remove_claim_exact
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count) :
    bountyRawRemoveClaim raw state account bountyId = some
      (bountyRawWrite
        (if remaining.isEmpty then
          bountyRawRemove raw (bountyClaimersKey account)
        else bountyRawWrite raw (bountyClaimersKey account)
          (encodeStoredBountyClaims remaining))
        (bountyCountKey bountyId)
        (encodeBountyCount (count - 1))) := by
  simp [bountyRawRemoveClaim, hclaims, hfind, hcount,
    Nat.ne_of_gt hpositive]

theorem bounty_raw_remove_claim_preserves_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count) :
    ∃ next nextRaw,
      removeStoredClaim state account bountyId = some (next, found) ∧
      bountyRawRemoveClaim raw state account bountyId = some nextRaw ∧
      bountyRawImage nextRaw next := by
  let next : BountyStorageState := {
    claimers := fun key => if key == account then
      if remaining.isEmpty then none else some remaining
      else state.claimers key
    counts := fun key => if key == bountyId then some (count - 1)
      else state.counts key
    locked := state.locked }
  let nextRaw : BountyRawTrie := bountyRawWrite
    (if remaining.isEmpty then
      bountyRawRemove raw (bountyClaimersKey account)
    else bountyRawWrite raw (bountyClaimersKey account)
      (encodeStoredBountyClaims remaining))
    (bountyCountKey bountyId) (encodeBountyCount (count - 1))
  refine ⟨next, nextRaw,
    remove_stored_claim_exact state account bountyId count claims
      remaining found hclaims hfind hcount hpositive,
    bounty_raw_remove_claim_exact raw state account bountyId count
      claims remaining found hclaims hfind hcount hpositive, ?_⟩
  constructor
  · intro query
    by_cases hsame : query = account
    · subst query
      have hcross : bountyClaimersKey account ≠
          bountyCountKey bountyId :=
        bounty_claimers_and_count_keys_disjoint account bountyId
      cases hempty : remaining.isEmpty <;>
        simp [next, nextRaw, bountyRawWrite, bountyRawRemove,
          hcross, hempty]
    · have hkey : bountyClaimersKey query ≠
          bountyClaimersKey account := by
        intro heq
        exact hsame (bounty_claimers_key_injective query account heq)
      have hcross : bountyClaimersKey query ≠
          bountyCountKey bountyId :=
        bounty_claimers_and_count_keys_disjoint query bountyId
      cases hempty : remaining.isEmpty <;>
        simp [next, nextRaw, bountyRawWrite, bountyRawRemove,
          hempty, hsame, hkey, hcross, himage.1 query]
  · intro query hquery
    have hcross : bountyCountKey query ≠
        bountyClaimersKey account := by
      exact Ne.symm (bounty_claimers_and_count_keys_disjoint
        account query)
    by_cases hsame : query = bountyId
    · subst query
      simp [next, nextRaw, bountyRawWrite]
    · have hkey : bountyCountKey query ≠
          bountyCountKey bountyId := by
        intro heq
        exact hsame (bounty_count_key_injective_bounded query
          bountyId hquery hid heq)
      cases hempty : remaining.isEmpty <;>
        simp [next, nextRaw, bountyRawWrite, bountyRawRemove,
          hempty, hsame, hkey, hcross, himage.2 query hquery]

end SputnikDAO2
