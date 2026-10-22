import Model.Views

namespace SputnikDAO2

-- Opaque values stand for the corresponding deserialized state fields and
-- legacy collection handles. Their bytes and wire order are not modeled here.
structure StateCore where
  config : String
  policy : String
  lockedAmount : Nat
  stakingId : Option String
  totalDelegationAmount : Nat
  delegations : String
  lastProposalId : Nat
  proposals : String
  lastBountyId : Nat
  bounties : String
  bountyClaimers : String
  bountyClaimsCount : String
  blobs : String
  deriving Repr, DecidableEq

structure CurrentState where
  core : StateCore
  actionsLog : List String
  deriving Repr, DecidableEq

inductive VersionRead where
  | missing | v1 | v2 | malformed
  deriving Repr, DecidableEq

structure MigrationContext where
  current : String
  predecessor : String
  versionRead : VersionRead
  oldState : Option StateCore
  currentState : Option CurrentState
  deriving Repr, DecidableEq

structure MigrationResult where
  state : CurrentState
  wroteV2Version : Bool
  deriving Repr, DecidableEq

-- `migrate` is #[private] and #[init(ignore_state)]. The old branch reads
-- ContractV1, writes STATEVERSION=V2 and adds an empty action log. The V2
-- branch reads and returns current state, without a version-key write.
def runMigrate (ctx : MigrationContext) : Option MigrationResult := Id.run do
  if ctx.predecessor != ctx.current then return none
  match ctx.versionRead with
  | .malformed => return none
  | .missing | .v1 =>
      let some old := ctx.oldState | return none
      return some ⟨⟨old, []⟩, true⟩
  | .v2 =>
      let some current := ctx.currentState | return none
      return some ⟨current, false⟩

-- `migrate` never writes the separate LazyOption Policy key. Its root state
-- contains only that key's handle, so the stored VersionedPolicy survives
-- unchanged even when V1 migration succeeds.
def runMigrateWithPolicy (ctx : MigrationContext)
    (stored : Option (StoredPolicy String)) :
    Option (MigrationResult × Option (StoredPolicy String)) :=
  (runMigrate ctx).map (fun result => (result, stored))

end SputnikDAO2
