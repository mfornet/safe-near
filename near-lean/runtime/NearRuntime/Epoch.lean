import NearRuntime.State
import NearRuntime.ChangeLog

/-! The epoch-boundary step of `Runtime::apply`: `Runtime::update_validator_accounts`
(`runtime/runtime/src/lib.rs`). In the first chunk of an epoch, before any transaction or
receipt, the runtime pays the validators of the shard their rewards, returns the stake they no
longer need to keep locked, and pays the protocol treasury. The chain supplies the
`ValidatorAccountsUpdate`; this module only applies it to the shard's accounts. -/

namespace Near

-- nearcore divergence: the update is an input computed by the epoch manager (rewards, stake info,
-- last proposals); an inconsistency is an `Except` error, and the trie nodes the update reads are
-- not replayed into the chunk's node cache (the chunk trie is built from the updated accounts).
/-- `ValidatorAccountsUpdate`, restricted to what this shard holds. -/
structure ValidatorAccountsUpdate where
  /-- Per validator account: the maximum of its stakes in the past three epochs
  (`stake_info`). -/
  stakeInfo : List (AccountId × Nat) := []
  /-- Reward of each validator account of the epoch that ended, the treasury included
  (`validator_rewards`). -/
  validatorRewards : List (AccountId × Nat) := []
  /-- The stake each account proposed during the previous epoch (`last_proposals`). -/
  lastProposals : List (AccountId × Nat) := []
  /-- `protocol_treasury_account_id`, when the shard holds it. -/
  protocolTreasury : Option AccountId := none
  deriving Inhabited, Repr

namespace ValidatorAccountsUpdate

private def lookup (table : List (AccountId × Nat)) (id : AccountId) : Option Nat :=
  (table.find? (·.1 == id)).map (·.2)

/-- One validator account: add its reward to the locked balance, check the staking invariant,
and return everything above `max(max_of_stakes, last_proposal)` to the liquid balance. -/
def updateValidator (u : ValidatorAccountsUpdate) (st : ChainState) (entry : AccountId × Nat) :
    Except String ChainState :=
  let (id, maxOfStakes) := entry
  match st.account? id with
  | none =>
    if maxOfStakes > 0 then
      .error s!"Account {id} with max of stakes {maxOfStakes} is not found"
    else .ok st
  | some account =>
    let locked := account.locked + (lookup u.validatorRewards id).getD 0
    if locked < maxOfStakes then
      .error s!"staking invariant does not hold: stake {locked} is less than maximum of stakes {maxOfStakes}"
    else
      let kept := max maxOfStakes ((lookup u.lastProposals id).getD 0)
      if locked < kept then
        .error s!"return stake of {id} overflows: locked {locked}, kept {kept}"
      else
        let returned := locked - kept
        .ok (st.setAccount id { account with locked := kept, amount := account.amount + returned })

/-- `update_validator_accounts`: the validators, then the treasury unless it is a validator
(its reward is then paid above). An error is `StorageInconsistentState` in nearcore: the chunk
is invalid. -/
def apply (u : ValidatorAccountsUpdate) (st : ChainState) : Except String ChainState := do
  let st ← u.stakeInfo.foldlM (updateValidator u) st
  match u.protocolTreasury with
  | none => return st
  | some id =>
    if u.stakeInfo.any (·.1 == id) then return st
    let some account := st.account? id
      | throw s!"Protocol treasury account {id} is not found"
    let some reward := lookup u.validatorRewards id
      | throw s!"Validator reward for the protocol treasury account {id} is not found"
    return st.setAccount id { account with amount := account.amount + reward }

/-- Observational: the `ValidatorAccountsUpdate` commit of `apply` (`ChangeLog.lean`). `update_validator_accounts`
writes (`set_account`) every account of `stake_info` that exists in the shard, and the protocol treasury unless
it is one of them; the writes are there whether or not the values changed. `before` and `after` are the shard's
state around `apply`. -/
def changes (u : ValidatorAccountsUpdate) (before after : ChainState) : List StateChange :=
  commitKeys .validatorAccountsUpdate after
    ((u.stakeInfo.filter fun entry => (before.account? entry.1).isSome).map
        (fun entry => ChangeKey.account entry.1) ++
      (match u.protocolTreasury with
      | some id => if u.stakeInfo.any (·.1 == id) then [] else [ChangeKey.account id]
      | none => []))

end ValidatorAccountsUpdate
end Near
