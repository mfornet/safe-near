import Model.ProposalCreate

namespace SputnikDAO2

inductive NonVoteAction where
  | addProposal | removeProposal | moveToHub
  deriving Repr, DecidableEq

structure GlobalActLog where
  account : String
  proposalId : Nat
  action : NonVoteAction
  blockHeight : Nat
  deriving Repr, DecidableEq

structure NonVoteState where
  proposals : List (Nat × CreatedProposal)
  globalLog : List GlobalActLog
  locked : Nat
  deriving Repr, DecidableEq

structure NonVoteContext where
  predecessor : String
  blockHeight : Nat
  permissionAllowed : Bool
  exactKindMatches : Bool
  deriving Repr, DecidableEq

-- A finite-list projection of `LookupMap.remove`. Canonical LookupMap states
-- have one value per key; filtering all copies gives the same logical map
-- even if a noncanonical list projection were supplied.
def eraseProposal (entries : List (Nat × CreatedProposal)) (id : Nat) :
    List (Nat × CreatedProposal) :=
  entries.filter (fun entry => entry.1 != id)

-- `internal_log_action` mutates both a local proposal copy and the global
-- log before permission/kind checks. The local copy is not inserted for
-- RemoveProposal or MoveToHub; on abort, transaction rollback discards the
-- global log mutation as well. Exact permission and kind equality are inputs
-- from the wider policy/serialization model.
def actNonVote (state : NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (action : NonVoteAction) : Option NonVoteState := Id.run do
  let some _stored := proposalAt state.proposals id | return none
  let logged := appendLog20 state.globalLog
    ⟨ctx.predecessor, id, action, ctx.blockHeight⟩
  if !ctx.permissionAllowed then return none
  if !ctx.exactKindMatches then return none
  match action with
  | .addProposal => return none
  | .removeProposal =>
      return some ⟨eraseProposal state.proposals id, logged, state.locked⟩
  | .moveToHub =>
      return some ⟨state.proposals, logged, state.locked⟩

end SputnikDAO2
