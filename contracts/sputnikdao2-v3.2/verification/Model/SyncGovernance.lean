import Model.ProposalBonds
import Model.Views

namespace SputnikDAO2

/-! Synchronous governance execution after an approved vote or successful
finalization, restricted to policy replacement/parameter patching and the
one-time staking setter. `internal_execute_proposal` receives the policy
decoded before mutation and uses that snapshot for immediate bond return.
The caller's proposal status/log writes and host rollback are external. -/

structure GovernanceParameters where
  proposalBond : Nat
  proposalPeriod : Nat
  bountyBond : Nat
  bountyForgivenessPeriod : Nat
  deriving Repr, DecidableEq

structure GovernanceParameterPatch where
  proposalBond : Option Nat
  proposalPeriod : Option Nat
  bountyBond : Option Nat
  bountyForgivenessPeriod : Option Nat
  deriving Repr, DecidableEq

def applyParameterPatch (old : GovernanceParameters)
    (patch : GovernanceParameterPatch) : GovernanceParameters :=
  ⟨patch.proposalBond.getD old.proposalBond,
    patch.proposalPeriod.getD old.proposalPeriod,
    patch.bountyBond.getD old.bountyBond,
    patch.bountyForgivenessPeriod.getD old.bountyForgivenessPeriod⟩

inductive SyncGovernanceAction where
  | replacePolicy (policy : GovernanceParameters)
  | updateParameters (patch : GovernanceParameterPatch)
  | setStaking (account : String)
  deriving Repr, DecidableEq

structure SyncGovernanceState where
  policy : GovernanceParameters
  staking : Option String
  locked : Nat
  deriving Repr, DecidableEq

structure SyncGovernanceOutcome where
  state : SyncGovernanceState
  refund : BondTransfer
  callbackScheduled : Bool
  deriving Repr, DecidableEq

def executeSyncGovernance (state : SyncGovernanceState)
    (action : SyncGovernanceAction) (proposer : String) :
    Option SyncGovernanceOutcome := do
  let next ← match action with
    | .replacePolicy policy => some { state with policy := policy }
    | .updateParameters patch =>
        some { state with policy := applyParameterPatch state.policy patch }
    | .setStaking account =>
        if state.staking.isSome then none
        else some { state with staking := some account }
  let oldBond := state.policy.proposalBond
  some ⟨{ next with locked := state.locked - oldBond },
    ⟨proposer, oldBond⟩, false⟩

/-! Policy-version effect of the synchronous governance branches. The caller
has already decoded the old stored policy before executing the proposal.
`ChangePolicy` writes its supplied VersionedPolicy without `upgrade`; the
shortcut mutations write Current. This projection omits vote authorization,
proposal status, bond accounting and host rollback. -/

inductive PolicyStorageAction (α : Type) where
  | replace (replacement : StoredPolicy α)
  | mutate (change : α → α)

def executePolicyStorageAction {α : Type}
    (stored : Option (StoredPolicy α))
    (action : PolicyStorageAction α) :
    Except PolicyViewError (StoredPolicy α) := do
  let old ← readPolicy stored
  match action with
  | .replace replacement => pure replacement
  | .mutate change => pure (.current (change old))

-- `add_proposal` admits only Current-valued ChangePolicy inputs. An older or
-- directly injected proposal can still reach the unchecked execution branch.
def validPolicyReplacement {α : Type} : StoredPolicy α → Bool
  | .default _ => false
  | .current _ => true

def executeValidatedPolicyReplacement {α : Type}
    (stored : Option (StoredPolicy α)) (replacement : StoredPolicy α) :
    Option (StoredPolicy α) :=
  if validPolicyReplacement replacement then
    (executePolicyStorageAction stored (.replace replacement)).toOption
  else none

def executeValidatedPolicyAction {α : Type}
    (stored : StoredPolicy α) (action : PolicyStorageAction α) :
    Option (StoredPolicy α) :=
  match action with
  | .replace replacement =>
      executeValidatedPolicyReplacement (some stored) replacement
  | .mutate change =>
      (executePolicyStorageAction (some stored) (.mutate change)).toOption

def executeValidatedPolicyTrace {α : Type}
    (stored : StoredPolicy α) :
    List (PolicyStorageAction α) → Option (StoredPolicy α)
  | [] => some stored
  | action :: rest => do
      let next ← executeValidatedPolicyAction stored action
      executeValidatedPolicyTrace next rest

end SputnikDAO2
