import Model.Proposal

namespace SputnikDAO2

inductive ProposalKindCheck where
  | changePolicy (currentVersion : Bool)
  | transfer (baseToken hasMessage : Bool)
  | setStakingContract
  | bountyDone (bountyId : Nat) (receiver : String)
  | other
  deriving Repr, DecidableEq

def validAddKind (stakingSet : Bool) : ProposalKindCheck → Bool
  | .changePolicy currentVersion => currentVersion
  | .transfer baseToken hasMessage => !(baseToken && hasMessage)
  | .setStakingContract => !stakingSet
  | .bountyDone .. => true
  | .other => true

-- Once a ChangePolicy input passes `add_proposal`, its stored variant is
-- Current. This property is independent of later staking-state changes.
def policyKindSafe : ProposalKindCheck → Prop
  | .changePolicy currentVersion => currentVersion = true
  | _ => True

structure CreatedProposal where
  proposer : String
  description : String
  kind : ProposalKindCheck
  status : ProposalStatus
  submissionTime : Nat
  voteCounts : List Nat
  voters : List String
  actionHeights : List Nat
  deriving Repr, DecidableEq

def policyEntriesSafe (entries : List (Nat × CreatedProposal)) : Prop :=
  ∀ entry, entry ∈ entries → policyKindSafe entry.2.kind

structure GlobalAddLog where
  account : String
  proposalId : Nat
  blockHeight : Nat
  deriving Repr, DecidableEq

def appendLog20 {α : Type} (entries : List α) (entry : α) : List α :=
  (if entries.length ≥ 20 then entries.drop 1 else entries) ++ [entry]

def proposalAt : List (Nat × CreatedProposal) → Nat → Option CreatedProposal
  | [], _ => none
  | (id, proposal) :: rest, target =>
      if id == target then some proposal else proposalAt rest target

def setProposal : List (Nat × CreatedProposal) → Nat → CreatedProposal →
    List (Nat × CreatedProposal)
  | [], id, proposal => [(id, proposal)]
  | (oldId, oldProposal) :: rest, id, proposal =>
      if oldId == id then (id, proposal) :: rest
      else (oldId, oldProposal) :: setProposal rest id proposal

structure ProposalCreateState where
  lastId : Nat
  locked : Nat
  stakingSet : Bool
  proposals : List (Nat × CreatedProposal)
  actionsLog : List GlobalAddLog
  deriving Repr, DecidableEq

structure ProposalCreateContext where
  predecessor : String
  blockTimestamp : Nat
  blockHeight : Nat
  attached : Nat
  policyBond : Nat
  addPermission : Bool
  deriving Repr, DecidableEq

-- Projection of `add_proposal` after policy deserialization and
-- `can_execute_action`. Failed branches represent atomic rollback, including
-- the checked u64 increment that occurs after provisional log/map writes.
def addProposal (state : ProposalCreateState) (ctx : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String) :
    Option (ProposalCreateState × Nat) := Id.run do
  if ctx.attached != ctx.policyBond then return none
  if !validAddKind state.stakingSet kind then return none
  if !ctx.addPermission then return none
  if state.lastId ≥ maxU64 then return none
  let proposal : CreatedProposal :=
    ⟨ctx.predecessor, description, kind, .inProgress,
      ctx.blockTimestamp, [], [], [ctx.blockHeight]⟩
  let next : ProposalCreateState :=
    ⟨state.lastId + 1,
      min (state.locked + ctx.attached) maxU128,
      state.stakingSet,
      setProposal state.proposals state.lastId proposal,
      appendLog20 state.actionsLog
        ⟨ctx.predecessor, state.lastId, ctx.blockHeight⟩⟩
  return some (next, state.lastId)

end SputnikDAO2
