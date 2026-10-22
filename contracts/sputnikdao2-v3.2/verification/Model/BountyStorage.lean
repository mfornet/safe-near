import Model.Policy

namespace SputnikDAO2

-- Account-keyed claim vectors and bounty-keyed counters. These are finite-map
-- abstractions of the two LookupMaps, not a Borsh/storage-key encoding.
structure StoredBountyClaim where
  bountyId : Nat
  start : Nat
  deadline : Nat
  completed : Bool
  paidBond : Nat -- ghost history, absent from the on-chain record
  deriving Repr, DecidableEq

structure BountyStorageState where
  claimers : String → Option (List StoredBountyClaim)
  counts : Nat → Option Nat
  locked : Nat

def removeFirstBountyClaim : List StoredBountyClaim → Nat →
    Option (StoredBountyClaim × List StoredBountyClaim)
  | [], _ => none
  | claim :: rest, bountyId =>
      if claim.bountyId == bountyId then some (claim, rest)
      else match removeFirstBountyClaim rest bountyId with
        | none => none
        | some (found, remaining) => some (found, claim :: remaining)

-- The timely `bounty_done` branch updates the first matching, unfinished
-- claim after proposal creation succeeds. No count or lock field changes.
def completeFirstBountyClaim : List StoredBountyClaim → Nat →
    Option (List StoredBountyClaim)
  | [], _ => none
  | claim :: rest, bountyId =>
      if claim.bountyId == bountyId then
        if claim.completed then none
        else some ({ claim with completed := true } :: rest)
      else (completeFirstBountyClaim rest bountyId).map
        (fun remaining => claim :: remaining)

def completeStoredClaim (state : BountyStorageState) (account : String)
    (bountyId : Nat) : Option BountyStorageState := do
  let claims ← state.claimers account
  let completed ← completeFirstBountyClaim claims bountyId
  some { state with claimers := fun key =>
    if key == account then some completed else state.claimers key }

-- `internal_remove_claim`: absent account, absent bounty claim/count, or a
-- zero count aborts. The last account claim removes that LookupMap key;
-- the bounty count key remains present with value zero.
def removeStoredClaim (state : BountyStorageState) (account : String)
    (bountyId : Nat) : Option (BountyStorageState × StoredBountyClaim) := Id.run do
  let some claims := state.claimers account | return none
  let some (found, remaining) := removeFirstBountyClaim claims bountyId |
    return none
  let some count := state.counts bountyId | return none
  if count == 0 then return none
  let next : BountyStorageState := {
    claimers := fun key => if key == account then
      if remaining.isEmpty then none else some remaining
      else state.claimers key
    counts := fun key => if key == bountyId then some (count - 1)
      else state.counts key
    locked := state.locked }
  return some (next, found)

-- `bounty_claim` appends to the caller's vector, which may already contain
-- entries for other bounty IDs. Missing counters default to zero on creation.
def addStoredClaim (state : BountyStorageState) (account : String)
    (bountyId now deadline maxDeadline times policyBond attached : Nat) :
    Option BountyStorageState := Id.run do
  let count := (state.counts bountyId).getD 0
  if bountyId > maxU64 || now > maxU64 || deadline > maxU64 ||
      maxDeadline > maxU64 || times > maxU32 || count > maxU32 ||
      attached > maxU128 || policyBond > maxU128 ||
      attached != policyBond || count ≥ times || deadline > maxDeadline then
    return none
  let oldClaims := (state.claimers account).getD []
  if oldClaims.length ≥ maxU32 then return none
  let newClaim : StoredBountyClaim :=
    ⟨bountyId, now, deadline, false, attached⟩
  return some {
    claimers := fun key => if key == account then
      some (oldClaims ++ [newClaim]) else state.claimers key
    counts := fun key => if key == bountyId then some (count + 1)
      else state.counts key
    locked := min (state.locked + attached) maxU128 }

-- A finite account enumeration is needed to state count coherence over the
-- functional-map abstraction. Coverage of all occupied account keys is an
-- external invariant until the concrete LookupMap encoding is refined.
def accountClaimCount (claims : List StoredBountyClaim) (bountyId : Nat) : Nat :=
  (claims.filter (fun claim => claim.bountyId == bountyId)).length

def observedBountyCount (state : BountyStorageState)
    (accounts : List String) (bountyId : Nat) : Nat :=
  (accounts.map fun account =>
    accountClaimCount ((state.claimers account).getD []) bountyId).sum

def coherentBountyCount (state : BountyStorageState)
    (accounts : List String) (bountyId : Nat) : Prop :=
  (state.counts bountyId).getD 0 =
    observedBountyCount state accounts bountyId

def coherentAllBountyCounts (state : BountyStorageState)
    (accounts : List String) : Prop :=
  ∀ bountyId, coherentBountyCount state accounts bountyId

end SputnikDAO2
