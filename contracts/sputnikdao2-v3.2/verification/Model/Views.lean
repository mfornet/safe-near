import Model.Policy

namespace SputnikDAO2

/-! The common index loop in `get_proposals` and `get_bounties`.
`lookup` represents the respective persistent map followed by conversion of its
versioned value. `none` denotes a checked-u64 addition abort, not an empty page.
The JSON conversion and storage read are outside this index-level model. -/

def pageScan {α : Type} (lookup : Nat → Option α) : Nat → Nat → List (Nat × α)
  | _, 0 => []
  | start, fuel + 1 =>
      let tail := pageScan lookup (start + 1) fuel
      match lookup start with
      | none => tail
      | some value => (start, value) :: tail

def viewPage {α : Type} (lastId fromIndex limit : Nat)
    (lookup : Nat → Option α) : Option (List (Nat × α)) :=
  if lastId > maxU64 || fromIndex > maxU64 || limit > maxU64 ||
      fromIndex + limit > maxU64 then none
  else
    let stop := min lastId (fromIndex + limit)
    some (pageScan lookup fromIndex (stop - fromIndex))

/-! `NearToken` stores u128 yoctoNEAR. The storage-usage argument is u64 in
the host API; callers of this mathematical projection must supply that width.
Both source arithmetic operations are saturating. -/

def viewLockedStorage (byteCost usage : Nat) : Nat :=
  min maxU128 (byteCost * usage)

def viewAvailable (balance byteCost usage lockedBonds : Nat) : Nat :=
  (balance - viewLockedStorage byteCost usage) - lockedBonds

-- `get_proposal` and `get_bounty` abort when the map entry is absent.
def viewOne {α : Type} (id : Nat) (entry : Option α) : Option (Nat × α) :=
  entry.map (fun value => (id, value))

-- Both claim views return the type's default for an absent map entry.
def viewDefault {α : Type} (default : α) (entry : Option α) : α :=
  entry.getD default

def viewDelegationRatio (balanceEntry : Option Nat) (total : Nat) : Nat × Nat :=
  (balanceEntry.getD 0, total)

/-! `get_policy` calls `unwrap` and then `VersionedPolicy::to_policy`.
Initialization upgrades both input variants to Current. Migration copies the
old `LazyOption` without upgrading it, so Current is a required invariant for
the view and for callers of `to_policy`. -/

inductive StoredPolicy (α : Type) where
  | default (council : List String)
  | current (policy : α)
  deriving Repr, DecidableEq

inductive PolicyViewError where
  | missing | legacy
  deriving Repr, DecidableEq

def upgradeStoredPolicy {α : Type} (makeDefault : List String → α) :
    StoredPolicy α → StoredPolicy α
  | .default council => .current (makeDefault council)
  | .current policy => .current policy

def readPolicy {α : Type} : Option (StoredPolicy α) → Except PolicyViewError α
  | none => .error .missing
  | some (.default _) => .error .legacy
  | some (.current policy) => .ok policy

-- `get_config` similarly unwraps, but has no version branch.
def readConfig {α : Type} (stored : Option α) : Option α := stored

def viewStakingContract (stakingId : Option String) : String :=
  stakingId.getD ""

def viewDelegationBalance (balanceEntry : Option Nat) : Nat :=
  balanceEntry.getD 0

def viewBountyClaims {α : Type} (claims : Option (List α)) : List α :=
  claims.getD []

def viewBountyClaimCount (count : Option Nat) : Nat :=
  count.getD 0

-- The remaining direct-field views are projections. The blob view is
-- `hasBlob` in Model.Blobs; it observes the raw key, not the owner map.
def viewVersion : String := "2.3.1"

end SputnikDAO2
