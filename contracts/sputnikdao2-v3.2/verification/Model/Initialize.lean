import Model.Views
import Model.Upgrade
import Model.Migration
import Model.BountyEncoding

namespace SputnikDAO2

/-! Source-level projection of `new`. Complex Config/Policy values and
collection entries are opaque; the constructor creates empty handles. The
SDK's `#[init]` no-prior-state check, Borsh writes, state serialization,
host rollback and gas are separate refinement obligations. -/

structure InitializedDAO where
  config : String
  policy : StoredPolicy String
  lockedAmount : Nat
  stakingId : Option String
  totalDelegationAmount : Nat
  delegations : List (String × Nat)
  lastProposalId : Nat
  proposals : List (Nat × String)
  lastBountyId : Nat
  bounties : List (Nat × String)
  bountyClaimers : List (String × List String)
  bountyClaimsCount : List (Nat × Nat)
  blobs : List (String × CodeBytes)
  actionsLog : List String
  factoryInfo : FactoryInfo
  stateVersion : VersionRead
  deriving Repr, DecidableEq

def initializeDAO (config : String) (policy : StoredPolicy String)
    (makeDefault : List String → String) (predecessor : String) :
    InitializedDAO :=
  { config := config
    policy := upgradeStoredPolicy makeDefault policy
    lockedAmount := 0
    stakingId := none
    totalDelegationAmount := 0
    delegations := []
    lastProposalId := 0
    proposals := []
    lastBountyId := 0
    bounties := []
    bountyClaimers := []
    bountyClaimsCount := []
    blobs := []
    actionsLog := []
    factoryInfo := ⟨predecessor, true⟩
    stateVersion := .v2 }

-- Borsh `FactoryInfo` is AccountId (length-prefixed UTF-8) then bool.
def encodeFactoryInfo (info : FactoryInfo) : BountyBytes :=
  bountyBorshString info.factoryId ++ [if info.autoUpdate then 1 else 0]

def initializedFactoryBytes (predecessor : String) : BountyBytes :=
  encodeFactoryInfo ⟨predecessor, true⟩

-- `StateVersion` has V1 discriminant 0 and V2 discriminant 1.
def initializedVersionBytes : BountyBytes := [1]

end SputnikDAO2
