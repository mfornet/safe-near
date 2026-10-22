import Model.Policy

namespace SputnikDAO2

inductive ProposalStatus where
  | inProgress | approved | rejected | removed | expired | moved | failed
  deriving Repr, DecidableEq

inductive VoteChoice where
  | approve | reject | remove
  deriving Repr, DecidableEq

structure VoteState where
  status : ProposalStatus
  voters : List String
  approvals : Nat
  rejections : Nat
  removals : Nat
  deriving Repr, DecidableEq

def countVote (state : VoteState) (choice : VoteChoice) (amount : Nat) : VoteState :=
  match choice with
  | .approve => { state with approvals := state.approvals + amount }
  | .reject => { state with rejections := state.rejections + amount }
  | .remove => { state with removals := state.removals + amount }

def decisionStatus : Decision → ProposalStatus
  | .inProgress => .inProgress
  | .approved => .approved
  | .rejected => .rejected
  | .removed => .removed

-- The single-role, pre-execution voting branch of `act_proposal`. The caller
-- supplies the source's per-role amount: 1 or the current delegation weight.
-- A successful step still needs receipt and bond effects to become the full
-- exported-method transition. `none` denotes an abort with atomic rollback.
def voteStep (state : VoteState) (account : String) (choice : VoteChoice)
    (amount threshold : Nat) : Option VoteState := Id.run do
  if state.status != .inProgress then return none
  if state.voters.contains account then return none
  let counted := countVote state choice amount
  let next := decisionStatus <|
    decideRole threshold counted.approvals counted.rejections counted.removals
  return some { counted with status := next, voters := account :: state.voters }

inductive CallbackResult where
  | success | failure
  deriving Repr, DecidableEq

-- Status projection of `on_proposal_callback`. `proposalExists` and `callerSelf`
-- represent the proposal lookup and SDK #[private] wrapper. The source
-- insists on exactly one result but does not require the stored status to be
-- Approved. The successful branch assumes internal bounty processing does not
-- abort; receipt/bond effects are outside this projection.
def callbackStatus (_status : ProposalStatus) (proposalExists callerSelf : Bool)
    (resultCount : Nat) (result : CallbackResult) : Option ProposalStatus :=
  if !proposalExists || !callerSelf || resultCount != 1 then none
  else some <| match result with
    | .success => .approved
    | .failure => .failed

end SputnikDAO2
