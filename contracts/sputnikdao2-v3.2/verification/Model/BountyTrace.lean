import Model.BountyTrie

namespace SputnikDAO2

-- Only the three bounty-claimer storage mutations modeled here. Other DAO
-- entry points and proposal side effects require separate refinement.
inductive BountyTrieStep :
    String → BountyRawTrie → BountyStorageState →
    BountyRawTrie → BountyStorageState → Prop where
  | add (raw : BountyRawTrie) (state next : BountyStorageState)
      (account : String)
      (bountyId now deadline maxDeadline times bond : Nat)
      (hid : bountyId < 256 ^ 8)
      (hlogical : addStoredClaim state account bountyId now deadline
        maxDeadline times bond bond = some next) :
      BountyTrieStep account raw state
        (bountyRawAddClaim raw state account bountyId now deadline bond)
        next
  | remove (raw nextRaw : BountyRawTrie)
      (state next : BountyStorageState)
      (account : String) (bountyId count : Nat)
      (claims remaining : List StoredBountyClaim)
      (found : StoredBountyClaim)
      (hid : bountyId < 256 ^ 8)
      (hclaims : state.claimers account = some claims)
      (hfind : removeFirstBountyClaim claims bountyId =
        some (found, remaining))
      (hcount : state.counts bountyId = some count)
      (hpositive : 0 < count)
      (hlogical : removeStoredClaim state account bountyId =
        some (next, found))
      (hraw : bountyRawRemoveClaim raw state account bountyId =
        some nextRaw) :
      BountyTrieStep account raw state nextRaw next

  | complete (raw nextRaw : BountyRawTrie)
      (state next : BountyStorageState)
      (account : String) (bountyId : Nat)
      (claims completed : List StoredBountyClaim)
      (hclaims : state.claimers account = some claims)
      (hcomplete : completeFirstBountyClaim claims bountyId =
        some completed)
      (hlogical : completeStoredClaim state account bountyId = some next)
      (hraw : bountyRawCompleteClaim raw state account bountyId =
        some nextRaw) :
      BountyTrieStep account raw state nextRaw next

inductive BountyTrieReachable :
    BountyRawTrie → BountyStorageState → Prop where
  | empty : BountyTrieReachable bountyEmptyRaw bountyEmptyState
  | advance {account : String} {raw nextRaw : BountyRawTrie}
      {state next : BountyStorageState}
      (prior : BountyTrieReachable raw state)
      (step : BountyTrieStep account raw state nextRaw next) :
      BountyTrieReachable nextRaw next

-- The enumeration contains every account modified by a trace step.
-- Its resulting key support is proved for projected traces, not assumed
-- for an arbitrary deployed storage snapshot.
inductive BountyTrieCoveredReachable (accounts : List String) :
    BountyRawTrie → BountyStorageState → Prop where
  | empty : BountyTrieCoveredReachable accounts bountyEmptyRaw bountyEmptyState
  | advance {account : String} {raw nextRaw : BountyRawTrie}
      {state next : BountyStorageState}
      (prior : BountyTrieCoveredReachable accounts raw state)
      (step : BountyTrieStep account raw state nextRaw next)
      (hmem : account ∈ accounts) :
      BountyTrieCoveredReachable accounts nextRaw next

def bountyAccountSupport (state : BountyStorageState)
    (accounts : List String) : Prop :=
  ∀ account, account ∉ accounts → state.claimers account = none

end SputnikDAO2
