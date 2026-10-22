# Storage Borsh byte oracle

Run from the repository root:

```sh
python3 contracts/sputnikdao2-v3.2/verification/oracle/run_storage_borsh.py
```

The runner requires the pinned Sputnik DAO source checkout to be clean at
`2b0f34a3860460f285307ec2ccf36345acbe05a2`. It copies that source to a
temporary directory, enables near-sdk's native `unit-testing` feature only
there, and appends `bounty_borsh_test.rs` beside the private `BountyClaim`
definition, `delegation_borsh_test.rs` beside the delegation methods,
`views_test.rs` beside the view methods, `init_test.rs` beside `new`, and
`add_proposal_test.rs` and `multi_vote_test.rs` beside the proposal methods.
It appends `signal_vote_test.rs` for the exported Vote-kind path and
`execute_upgrade_test.rs` for the approved upgrade proposal paths, and
`transfer_test.rs` for approved transfer receipts and callback branches, and
`function_call_test.rs` for arbitrary-call promise batches, and
`sync_governance_test.rs` for policy parameters and staking execution, and
`add_bounty_execution_test.rs` for bounty creation through proposal approval,
and `bounty_payout_test.rs` for approved payout receipts and callbacks.
`cargo test --locked --offline` uses the pinned Cargo.lock and
checks actual `LookupMap` writes for an open claim, completed claim, removal,
and a zero count. A second test calls the pinned contract's `bounty_claim`,
timely `bounty_done`, and `internal_remove_claim` methods. It checks both the
nonempty-vector rewrite after removing one of two bounty IDs and deletion
after the final removal. The source checkout is never edited.
An initialization fixture checks that direct `new` writes Config, Policy,
`FACTORY` and `STATEVERSION` before an explicit root `STATE` write. It also
starts with malformed old Config/Policy bytes and an unrelated raw key:
`new` overwrites those auxiliary values and leaves the unrelated key intact.
The generated `#[init]` guard is projected separately from pinned near-sdk
macro source; native direct-method tests do not execute that wrapper.
The migration fixture confirms the V1 root gains only an empty action-log
length and leaves a legacy Default policy key unchanged. A V2 fixture checks
that direct `migrate` returns the existing root bytes and leaves the version
key at V2; it writes the returned state explicitly to emulate the generated
wrapper's final root write.

The delegation test calls registration, delegation, and undelegation. It
checks prefix-2 Borsh AccountId keys and 16-byte u128 values, then confirms
that zero undelegation creates a stored zero and re-registration overwrites a
positive balance while leaving the total unchanged.

The view tests put proposal and bounty entries at IDs 1 and 3 in a window of
five, then check that pagination skips gaps without refilling them. They also
check the source's missing-single-entry panics and checked-u64 overflow,
storage reserve and available-balance arithmetic, and default claim and
delegation reads. These are finite source tests under the near-sdk native
mock; the Lean proofs state the corresponding general index and arithmetic
properties under explicit u64/u128 input bounds.
An owned-staking-view fixture reads the stored Contract, calls
`get_staking_contract(self)` and checks that root bytes remain intact, even
with attached deposit in the native context. The SDK macro source classifies
this owned receiver as a view; the fixture does not execute generated Wasm.
The policy view test confirms that `new` upgrades a Default input to a
readable Current policy, while writing Default back into the policy slot
makes `get_policy` panic at `to_policy`. It also checks the pinned package
version and config/staking projections.
The factory-info view test checks that stored information overrides the
fallback, a missing key derives the immediate parent from the first dot of
a nested DAO account, malformed bytes abort, and a missing key on a no-dot
account aborts.

The constructor test checks zero IDs, supply and locked balance, empty
collections, policy upgrade, and the raw `FACTORY` and `STATEVERSION` bytes.
`Proofs/Initialize.lean` evaluates the Lean encoders to the exact same byte
arrays. The native test calls the Rust method directly, so it does not check
the SDK-generated `#[init]` wrapper's already-initialized guard.

The multi-role test obtains both allowed role names from the pinned policy,
then checks that a RoleWeight vote adds 1 while a TokenWeight vote adds the
caller's weight 7. It confirms status approval and that an expired vote is
counted before `proposal_status` returns Expired. Direct native method calls
do not test NearVM rollback after a panic or receipt scheduling.
An additional duplicate-name fixture shows that the later role's permissions
authorize the vote, while the first role's RoleWeight rule makes a caller
with delegation 7 add only 1 to that name's count.

The add-proposal fixture checks that a fresh payable call writes the prefix-3
proposal entry, returns the old ID, advances the counter and locks the bond.
With a deliberately reused ID, malformed old bytes make LookupMap insertion
panic; a decodable old value is replaced. The native mock does not establish
on-chain rollback after the panic.

The signal-vote test calls the pinned `act_proposal` method and checks
Approved, Rejected, Removed, Expired and InProgress outcomes. It inspects
proposal storage, the locked balance, global log and created transfer
receipts, including the no-refund branches. These observations are native
source fixtures; they do not establish NearVM rollback, receipt delivery or
behavior of the other proposal kinds.

The upgrade tests inspect `act_proposal` receipts for `UpgradeSelf` and
`UpgradeRemote`. They confirm that self-upgrade uses the account's parent
instead of the stored factory override, remote upgrade reads raw blob bytes,
both issue the bond refund before any external result, neither schedules
`on_proposal_callback`, and a missing remote blob aborts. They do not execute
the external factory/receiver receipts or prove migration succeeds.

The transfer tests check NEAR, `ft_transfer`, and `ft_transfer_call` receipt
scheduling, FT gas/deposit and memo, callback scheduling, and the lack of an
immediate bond refund. A successful callback refunds the bond, while a failed
one keeps it locked. A second successful direct callback call confirms the
source has no stored-status guard. Direct Rust calls do not exercise the
generated private-method wrapper, and the tests do not execute external
receipts or establish reachability of a repeated authenticated callback.

The function-call tests confirm that two actions retain their order, raw
arguments, individual deposits and gas in one receiver receipt, with one
follow-up callback. An empty action list still schedules that callback.
Success refunds the bond, while failure stores Failed and keeps the lock.
The native receipt mock does not execute those actions or establish NearVM
resource accounting and batch atomicity.

The synchronous-governance tests confirm that policy replacement and a
parameter patch return the old policy's bond immediately, while the new
bond is stored. They also create two pending staking proposals before the
first approval and observe the second execution's `ERR_INVALID_STAKING_CHANGE`
abort. The native panic test checks the source guard, not host rollback.
The same source oracle checks first-match role replacement and removal when
names are duplicated, group member insertion/deletion, the logged no-op for
a missing role or wrong first role kind, and default vote-policy replacement.
These cases still schedule the old-bond refund and no proposal callback.
The settings tests check complete config replacement and a factory-info
proposal that rewrites malformed `FACTORY` bytes to valid Borsh, returns the
bond, and stores `auto_update = false`. A separate native test process checks
that an enabled factory can call raw `update` and schedule the global-code
use plus `migrate` receipt. `update` installs a process-wide panic hook, so
the permitted-path test is isolated from fixtures that catch expected panics;
the denied raw-update path is covered by the Lean source-level guard proof.
The `AddBounty` tests confirm that a zero-times bounty with an invalid token
string is accepted, stores no claim count, refunds the proposal bond, and
cannot be claimed. An inconsistent reused-ID fixture shows overwrite of the
bounty record without reset of its old claim count. A max-u64 fixture checks
the increment panic; native tests do not prove host rollback of its prior
write.

The payout tests create a bounty, claim it, submit `bounty_done`, and approve
the proposal. They check claim removal before the payout result, native and
FT receipt forms, one callback, and no immediate refund. Failure keeps the
bonds locked and leaves no claim for a direct retry; success stores zero
times and schedules two refunds at the current policy amounts. A second
direct successful callback removes that zero-times bounty and schedules
another pair. Raw key checks confirm a failure leaves the prefix-4 bounty
entry unchanged while rewriting the prefix-3 proposal, a first success
rewrites a present bounty entry, and a repeat success removes that key.
These direct calls bypass `#[private]`; the tests do not prove
repeat callback reachability or refund delivery.
Additional source tests confirm that after give-up and a fresh claim by the
same account, an old `BountyDone` proposal can be approved and consumes that
fresh, uncompleted claim. When a bounty allows two claims by one account,
the completed first matching claim instead makes a later `bounty_done` call
abort even though the second claim is uncompleted.
The same payout oracle checks `VoteReject`, `VoteRemove`, and expired
`Finalize`: all remove the claim, but only rejection and expiration schedule
both refunds and retain the proposal. It also confirms that giving up after
`bounty_done` makes a later rejection abort at claim lookup. With an explicit
policy permission, `RemoveProposal` instead deletes the proposal and leaves
the completed claim and locked funds untouched. Expected native panics do
not establish NearVM transaction rollback.

`Proofs/BountyEncoding.lean` and `Proofs/DelegationEncoding.lean` prove the
exact fixture arrays produced by the Lean encoders. The native tests check
those arrays against the pinned Rust types and near-sdk 5.24.1. This is a
finite cross-language regression, not a
proof that every Lean-encoded value equals Rust Borsh or that a deployed DAO
has the projected storage image.
The delegation fixture also confirms that a valid 27-byte account ID yields
32-byte delegation and bounty-claimer storage keys, while a 32-byte hash has
a 33-byte blob owner-index key. It does not exhibit a SHA-256 preimage for an
account-index key.
With a synthetic digest equal to a delegation key, a 16-byte raw payload can
be decoded as the old u128 balance, then overwritten by delegation and removed
by an authorized `remove_blob` call while the owner index persists until
removal. A malformed old payload makes the delegation insert panic; native
mock storage after panic is not evidence of on-chain rollback.
The bounty fixture checks the parallel claimers-key alias. An empty-vector
Borsh payload lets `bounty_claim` replace the synthetic raw blob with a claim
record; `remove_blob` then deletes that record while the separate count stays
at one. Malformed bytes make
`bounty_claim` panic, without establishing rollback of its preceding count
write in the native mock.
