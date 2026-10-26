import NearRuntime.Fees
import NearRuntime.Refund

/-!
# The state change log of a chunk

nearcore keeps, for every trie key that a chunk passed to `TrieUpdate::set` or `remove`, the list of
`(cause, value)` pairs the key went through (`RawStateChangesWithTrieKey`), and serves them from
`EXPERIMENTAL_changes` and `EXPERIMENTAL_changes_in_block`. `TrieUpdate::commit(cause)` appends, for each key
written since the previous commit, the last value written (a key written twice before a commit is one entry),
and `rollback` drops what was not committed. The exposed kinds are accounts, access keys (and the nonces of
gas keys), contract code and contract data.

This module is **observational**. The log is a result of `Near.apply` (`ExecutionOutcome.changes`, gathered by `ApplyResult.changes`): it is computed
from what the receipt did and from the state it left, and nothing in `apply` reads it back. It describes, in
the runtime's own vocabulary, the commits of `Runtime::apply` that touch an exposed key:

* `TransactionProcessing { tx_hash }`: the signer's access key and account (`verify_and_charge_transaction`);
* `ReceiptProcessing { receipt_hash }`: what the actions of a receipt that succeeded wrote (a receipt that
  fails rolls back and has no entry);
* `ActionReceiptGasReward { receipt_hash }`: the receiver's account with the reward for its function calls;
* `ValidatorAccountsUpdate`: the accounts `update_validator_accounts` writes (`Epoch.lean`).

`ActionReceiptProcessingStarted`, `PostponedReceipt`, `UpdatedDelayedReceipts`, `Migration` and
`BandwidthSchedulerStateUpdate` only commit keys of other kinds (received data, postponed receipts, queues),
which `StateChangesExt::from_changes` drops.
-/

namespace Near

open Wasm.Near

namespace ChainState

/-- The value a key holds in a state (`none` when it is absent). -/
def valueOf? (st : ChainState) : ChangeKey → Option ChangeValue
  | .account id => (st.account? id).map .account
  | .accessKey id pk => (st.accessKey? id pk).map .accessKey
  | .gasKeyNonce id pk lane => (st.gasKeyNonce? id pk lane).map .nonce
  | .contractCode id => ((st.account? id).bind (·.code)).map .code
  | .data id key => (Assoc.lookup (st.contractStorage id) key).map .data

end ChainState

/-- The commit of the keys `keys` (each once) as `cause`, with the values `st` holds. -/
def commitKeys (cause : ChangeCause) (st : ChainState) (keys : List ChangeKey) : List StateChange :=
  let (_, kept) :=
    keys.foldl
      (fun (acc : Std.HashSet ChangeKey × Array ChangeKey) k =>
        if acc.1.contains k then acc else (acc.1.insert k, acc.2.push k))
      ({}, #[])
  -- the storage of each account whose data keys are listed, as a map (the first entry of a key wins, as in `Assoc.lookup`)
  let storages : Std.HashMap AccountId (Std.HashMap Bytes Bytes) :=
    kept.foldl
      (fun m k =>
        match k with
        | .data id _ =>
          if m.contains id then m
          else m.insert id ((st.contractStorage id).foldr (fun e h => h.insert e.1 e.2) {})
        | _ => m)
      {}
  kept.toList.map fun k =>
    { cause, key := k
      value :=
        match k with
        | .data id key => ((storages[id]?).bind (·[key]?)).map .data
        | _ => st.valueOf? k }

/-- The nonce lanes of a gas key, as keys. -/
def laneKeys (id : AccountId) (pk : PublicKey) (nonces : Nat) : List ChangeKey :=
  (List.range nonces).map (.gasKeyNonce id pk ·)

/-- What one action of a receipt writes to the trie beyond the receiver's account (which every receipt
that succeeds writes at its end, `set_account`) and the contract's own storage calls (the VM's log).

`exists_` says whether the receiver's account exists when the action runs and `local_` whether it then
holds code of its own (`AccountContract::Local`); `pre` is the state before the receipt and `earlier`
the actions that ran before this one. Reference: `runtime/runtime/src/{actions,access_keys,
global_contracts}.rs` and `core/store/src/utils/mod.rs` (`remove_account`). -/
def actionKeys (receiver : AccountId) (isGasRefund : Bool) (signerKey : PublicKey)
    (pre : ChainState) (exists_ local_ : Bool) (earlier : List Action) : Action → List ChangeKey
  | .createAccount => []
  | .deployContract _ => [.contractCode receiver]
  | .functionCall .. => []
  | .transfer deposit =>
    if exists_ then
      -- a gas refund restores the allowance of the signer's key when that changes it
      if isGasRefund then
        match pre.accessKey? receiver signerKey with
        | some key =>
          match refundAllowanceUpdate key deposit with
          | some _ => [.accessKey receiver signerKey]
          | none => []
        | none => []
      else []
    else
      -- implicit account creation: a NEAR-implicit account gets its full access key
      match implicitPublicKey? receiver with
      | some pk => [.accessKey receiver pk]
      | none => []
  | .stake .. => []
  | .addKey pk key =>
    match key.permission.gasKeyInfo? with
    | some (_, nonces) => .accessKey receiver pk :: laneKeys receiver pk nonces
    | none => [.accessKey receiver pk]
  | .deleteKey pk =>
    -- the key as it was when the action ran: added by an earlier action, or in the state before
    let added :=
      earlier.reverse.findSome? fun
        | .addKey pk' key => if pk' == pk then some (some key) else none
        | .deleteKey pk' => if pk' == pk then some none else none
        | _ => none
    let key? : Option AccessKey :=
      match added with
      | some k => k
      | none => pre.accessKey? receiver pk
    match key?.bind (·.permission.gasKeyInfo?) with
    | some (_, nonces) => .accessKey receiver pk :: laneKeys receiver pk nonces
    | none => [.accessKey receiver pk]
  | .deleteAccount _ =>
    -- `remove_account`: the account and its code, then every access key, gas key nonce and data key
    -- the account has; whatever earlier actions of the receipt wrote is listed by them
    [.account receiver, .contractCode receiver] ++
      (pre.accessKeys.filter (·.1.1 == receiver)).map (fun e => .accessKey receiver e.1.2) ++
      (pre.gasKeyNonces.filter (·.1.1 == receiver)).map
        (fun e => .gasKeyNonce receiver e.1.2.1 e.1.2.2) ++
      (pre.contractStorage receiver).map (fun e => .data receiver e.1)
  | .useGlobalContract _ => if local_ then [.contractCode receiver] else []
  | .deployGlobalContract .. => []
  | .transferToGasKey pk _ => [.accessKey receiver pk]
  | .withdrawFromGasKey pk _ => [.accessKey receiver pk]
  | .delegate sender _ _ _ nonceIndex _ pk .. =>
    match nonceIndex with
    | none => [.accessKey sender pk]
    | some lane => [.gasKeyNonce sender pk lane]

/-- The keys the actions of a receipt write, in order, folding the facts `actionKeys` needs. -/
def actionsKeys (receiver : AccountId) (isGasRefund : Bool) (signerKey : PublicKey)
    (pre : ChainState) : List Action → List ChangeKey :=
  let rec go (exists_ local_ : Bool) (earlier : List Action) : List Action → List ChangeKey
    | [] => []
    | a :: rest =>
      let keys := actionKeys receiver isGasRefund signerKey pre exists_ local_ earlier a
      let exists_' :=
        match a with
        | .createAccount => true
        | .deleteAccount _ => false
        | .transfer _ => true
        | _ => exists_
      let local_' :=
        match a with
        | .deployContract _ => true
        | .useGlobalContract _ => false
        | .deleteAccount _ => false
        | _ => local_
      keys ++ go exists_' local_' (earlier ++ [a]) rest
  go (pre.account? receiver).isSome ((pre.account? receiver).any (·.code.isSome)) []

/-- The `ReceiptProcessing` commit of a receipt that succeeded: the receiver's account, what the actions
wrote and the contract's storage calls. `st` is the state after the actions, before the gas reward. -/
def receiptCommit (receipt : ReceiptId) (receiver : AccountId) (isGasRefund : Bool)
    (signerKey : PublicKey) (pre st : ChainState) (actions : List Action)
    (dataWrites : List Wasm.StorageWrite) : List StateChange :=
  commitKeys (.receiptProcessing receipt) st
    (.account receiver :: actionsKeys receiver isGasRefund signerKey pre actions ++
      dataWrites.map fun w => .data receiver w.key)

/-- The commit of a transaction: the signer's access key and account. -/
def transactionCommit (index : Nat) (signer : AccountId) (pk : PublicKey) (st : ChainState) :
    List StateChange :=
  commitKeys (.transaction index) st [.accessKey signer pk, .account signer]

/-- The `ActionReceiptGasReward` commit: the receiver's account, when the reward is positive and the
account is there. -/
def rewardCommit (receipt : ReceiptId) (receiver : AccountId) (reward : Nat) (st : ChainState) :
    List StateChange :=
  if decide (reward > 0) && (st.account? receiver).isSome then
    commitKeys (.gasReward receipt) st [.account receiver]
  else []

end Near
