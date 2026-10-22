# Sputnik DAO v3.2 verification — in progress

Pinned source: `2b0f34a3860460f285307ec2ccf36345acbe05a2`,
`sputnikdao2` v2.3.1. The factory-stored, exactly reproduced code hash is
`DtHZA1mUmGYeScEaUoUZYQGGFHSMpnjMCvkr5U9hJXuF`. The manifest requests
near-sdk 5.24; the lockfile resolves 5.24.1. The dataset has not identified
a deployed DAO instance with this code hash. A proof of this source does not
by itself establish that any particular DAO account executes it.

This Lean package has checked projections for policy arithmetic and
authorization, proposal and bounty transitions, delegation, storage bytes,
views, upgrades, initialization and migration. They are not yet joined into
a whole-contract dispatcher or a proof for the deployed Wasm.
`Model/ExportWrapper.lean` inventories all 34 contract exports and their
wrapper classes: two initializers, ten generated mutating calls, twenty
views and two manual raw exports. Its Lean proofs check unique names, class
counts, the sole private generated callback, the four payable generated
calls, and common call-wrapper guards. A successful modeled mutating call
always writes the returned root; an absent decoded state or failed body
cannot produce that success. The [export audit](audit_exports.py) checks the
inventory names against the canonical Wasm exports. Method bodies, JSON and
callback decoding, return serialization, gas and host rollback remain
separate refinement obligations.
`Model/UpdateExport.lean` connects the manual raw `update` export to the
`FACTORY` key: missing bytes use a validated account-parent fallback,
decodable stored bytes supply the authorization setting, and malformed bytes
abort. Lean proves that the result is independent of every other storage key
and of attached deposit, that a disabled factory cannot call externally, and
that authorized self and factory calls schedule the modeled global-code and
`migrate` receipt. The native source fixture confirms a factory call still
schedules that receipt with no `STATE` root and nonzero deposit. The Borsh
parser in `Model/FactoryEncoding.lean` reads the length-prefixed UTF-8
AccountId and strict boolean, requiring complete byte consumption. Lean
proves round-trip for valid bounded IDs and rejects invalid boolean bytes,
missing booleans, trailing bytes and invalid IDs; source fixtures confirm the
invalid boolean and trailing-byte cases. The exact near-sdk AccountId
validator, arbitrary Rust-Borsh equivalence, SHA-256, promise execution and
concrete Wasm semantics remain refinement obligations.
`Model/FactoryViewRefinement.lean` applies that same parsed `FACTORY` value to
`get_factory_info`. The generated view still requires a decoded Contract root,
then reads the raw factory key. Lean proves that valid stored bytes determine
its result, malformed boolean bytes abort, and the manual `update` call uses
the identical resolved factory setting for authorization. This closes the
previous mismatch where the view and raw update could be supplied unrelated
factory values; root decoding, AccountId validity and return serialization
remain explicit boundaries.
`Model/FactoryGovernanceExport.lean` projects the approved
`FactoryInfoUpdate` branch of `act_proposal` through its three storage writes:
the direct `FACTORY` replacement, updated proposal entry, and generated
`STATE` write. Lean proves that the resulting factory bytes drive the next
parsed `get_factory_info` view and that disabling auto-update blocks a later
external factory call. Approval, policy/permission checks, proposal decoding,
and the proposal/root serializers are explicit branch inputs; this is a
conditional composition rather than a proof of the entire voting path.
`Model/FactoryVoteTrace.lean` now derives the approved branch from the
selected-role vote transition for a `FactoryInfoUpdate` proposal. It carries
the new ballot, one action-log append, and the current proposal-bond refund
into the proposal/root serializer inputs, then composes the three-key write
above. Lean proves an output from this branch has Approved status and the
stated refund/log effects. A source fixture checks the approved proposal,
vote, local/global logs, zero remaining lock, raw factory value and detached
refund. Role selection and policy rules, proposal-kind decoding, receipt
execution and serialization still require refinement.
`Model/FactoryFinalizeTrace.lean` covers the other approved route, where
`Finalize` recomputes status and selects execution. Lean proves the approved
status, current proposal-bond refund, action-log append and the same
three-key storage image. Finalize does not check whether a prior execution
already refunded the bond; a pinned-source fixture injects a synthetic
`Failed` status after an approved synchronous factory update and confirms
that Finalize executes again and schedules a second refund. Ordinary
`FactoryInfoUpdate` execution does not itself enter Failed, so the fixture
establishes conditional behavior rather than reachability from normal DAO
history. The status computation's role inputs and full serialization remain
refinement obligations.
`Model/ConfigGovernanceExport.lean` projects an approved `ChangeConfig`
branch through the Config LazyOption key 0, updated proposal entry, and
generated root write. The modeled `get_config` view reads and parses key 0
only after root decoding; Lean proves that bounded new Config bytes are
returned by the next view, while missing or trailing-byte values abort.
The old key is deliberately unrestricted: near-sdk 5.24.1 `LazyOption::set`
overwrites it without deserialization. A pinned-source fixture confirms an
approved change repairs malformed old Config bytes, stores exact Borsh bytes
and returns the new value. Approval, proposal/root serialization and host
rollback remain refinement obligations.
`Model/ConfigVoteTrace.lean` removes the independent approval Boolean for
the voting route: the shared selected-role transition must produce Approved
before the Config, proposal and root writes occur. The result includes the
current proposal-bond refund and action log. A source fixture checks the
approved stored proposal, one vote, local/global logs, exact Config bytes,
cleared lock and immediate refund. Role selection, policy arithmetic and
complete serializers remain external refinement inputs.
`Model/PolicyGovernanceExport.lean` projects approved `ChangePolicy` storage
through policy key 1, the proposal entry and the root write. It reads key 1
first: the existing policy must decode as Current before `act_proposal` can
execute, so malformed or legacy bytes cannot be repaired through this path.
Lean proves that a bounded Current replacement is read by the next parsed
`get_policy` view, while an executed Default replacement makes that view
abort. Public `add_proposal` rejects Default; this latter trace is conditional
on a synthetically inserted old proposal. Source fixtures check exact Current
and Default policy bytes, the failing legacy view, and the inability to
execute a replacement after corrupting old policy bytes. Policy-map
canonicalization, full serializers and rollback remain external obligations.
`Model/PolicyVoteTrace.lean` derives approved `ChangePolicy` execution from
the selected-role vote transition, with the old policy still required to
decode as Current. Lean composes the approved ballot, action log and old
proposal-bond refund with the policy/proposal/root writes; a conditional
Default replacement then makes the next parsed policy view abort. A pinned
source fixture checks the synthetic Default proposal's approved status, vote
and logs before the failing view. Public proposal creation remains the guard
that excludes this legacy replacement from the ordinary path.
`Model/PolicyReadBarrier.lean` binds the policy-read guards of exported
proposal creation, non-vote actions, Vote-kind voting and Vote-kind Finalize
to raw key 1. Lean proves each modeled path aborts when those bytes are
unreadable, and that executing a legacy Default replacement closes this
shared barrier. A pinned-source fixture confirms `get_policy`, `act_proposal`
and `add_proposal` all panic after that synthetic replacement. The positive
parser-to-near-sdk refinement still depends on AccountId and collection
decoding, and host rollback is external.
`Model/PolicyBountyBarrier.lean` applies the same raw policy guard to
`bounty_claim` and `bounty_giveup`. Timely `bounty_done` is also blocked
because it calls `add_proposal`; its expired cleanup branch does not read
policy and remains available. Lean proves this branch distinction, and a
pinned-source fixture checks all four calls after a synthetic legacy policy
write: claim, giveup and timely done panic, while expired done removes the
claim and decrements its count. The expired path leaves the locked bond in
place, so clearing a claim is not a proof of refund or full recovery.
`Model/PolicyCallbackBarrier.lean` binds the shared private
`on_proposal_callback` branches to raw policy key 1. Success needs a readable
Current policy before bond refund or BountyDone times changes; failure marks
the proposal Failed without reading policy. Lean proves that distinction for
ordinary and BountyDone callbacks and carries the ordinary failure's locked
balance forward. A pinned-source transfer fixture confirms that a legacy
policy blocks a successful callback, while a failed callback still stores
Failed without refunding. Callback receipt execution and host rollback remain
external.
`Proofs/PolicyMigrationBoundary.lean` proves that the manual raw `update`
receipt is independent of policy key 1 and that every successful named
`migrate` under this pinned code preserves that key and its modeled
readability. Source fixtures confirm raw update still schedules its receipt
with a legacy policy and direct V2 migration leaves that policy unreadable.
This is a property of the pinned update/migrate implementation; a different
deployed code hash could intentionally repair the key. Promise execution,
deployed code selection and host rollback remain outside the proof.
`Model/DelegationExport.lean` composes `register_delegation`, `delegate`, and
`undelegate` with their generated wrappers and raw LookupMap writes.
`Proofs/DelegationExport.lean` proves that a successful call writes the
account balance key and root `STATE` key, as well as caller and deposit guards.
It also exhibits a valid payable re-registration that zeros an existing
balance without reducing the total, breaking delegation accounting coherence.
The complete Contract-root serializer is an explicit input to this projection.
`Model/BlobExport.lean` composes generated `remove_blob` with its owner check,
raw hash/index deletion and refund calculation. The proofs require a 32-byte
digest, establish both deletions and the root write on success, and preserve
the source's stale owner-register length when the raw blob key is absent.
The one-digest `blobSlotRawImage` relation now connects the logical slot to
the raw hash and owner-index keys after a successful store or removal. A
whole-map storage image and complete root encoding still need refinement.
The same module separately composes manual
`store_blob`: the proofs reject an occupied hash or insufficient deposit and
show its raw bytes, owner index, root write and returned digest on success.
The SHA-256 function and JSON/base58 return encoding remain external inputs.
`Model/CallbackExport.lean` composes the ordinary (non-`BountyDone`)
`on_proposal_callback` body with its private generated wrapper. Lean proves
the self-caller and exactly-one-result guards, the proposal/root writes, and
the branch effects: failure retains the lock, while success uses the current
proposal bond for its returned transfer. The `BountyDone` callback's bounty
storage effects are composed separately in `Model/BountyCallbackExport.lean`:
success writes or removes the bounty entry before rewriting the proposal,
while failure leaves the bounty key unchanged. Lean proves the source's
`times = 1` to zero write and `times = 0` deletion branches. Exact bounty,
proposal and root serialization remain explicit inputs.
`Model/ProposalCreateExport.lean` composes payable `add_proposal` with the
source bond/kind/permission/ID checks and the generated wrapper. It binds
the body caller and attached deposit to the wrapper context, checks that an
occupied old proposal value can be decoded before LookupMap insertion, and
proves that success returns the previous last ID while writing its proposal
entry and the root. Exact policy evaluation, old-value decoding and complete
serialization remain external refinement inputs. The pinned-source oracle
checks fresh writes and both malformed and decodable occupied-key cases.
`Model/BountyClaimExport.lean` composes payable `bounty_claim` with the
generated wrapper and its count/claimer raw writes. The export proofs require
loaded bounty and policy records, reject a wrong bond, establish both raw
keys and the root on success, and carry the existing Borsh image and
serializability preservation theorem through the wrapper under u64 bounds.
`Model/BountyGiveupExport.lean` composes nonpayable `bounty_giveup` with the
generated wrapper and claim-removal raw writes. It rejects a nonzero deposit,
missing policy, or checked timestamp underflow. The model separates the late
no-refund branch from the timely branch, where the transfer amount and locked
counter use the current policy bond rather than the claim's historical bond.
Its success proofs identify the updated root and the underlying raw claim
removal, then preserve the bounded bounty-key raw image and serializability
through the wrapper. Promise execution, full root serialization and host
rollback remain external obligations.
`Model/BountyDoneExport.lean` composes payable `bounty_done` with its generated
wrapper, account-keyed claim vector and proposal store. It requires the
bounty and proposal projections of the shared locked counter to agree.
Expired cleanup removes the first matching claim and count without checking
the caller or proposal bond; timely completion requires the claimer as caller,
creates a BountyDone proposal and marks that claim complete. The raw model
writes the proposal key before the claim vector and rejects an occupied,
undecodable old proposal value. Lean proves the expired and active guards,
the malformed-old-value abort and the outer root write. Under the bounded
raw-image and serializability assumptions, separate branch proofs preserve
the bounty claim/count image through expired removal and timely completion;
the latter also proves that the proposal-key write cannot alter those bounty
keys. Branch-specific export theorems carry the image through the generated
root write. The final branch theorems derive the removal or completion facts
from successful exported calls, so both outcomes preserve the bounty raw
image and serializability from the corresponding input invariants. Root and
proposal serialization, gas, and runtime rollback remain separate
obligations.
`Model/ActProposalExport.lean` composes the non-vote `act_proposal` actions
with its generated wrapper. A failed policy-read input, out-of-range ID,
nonzero deposit, or `AddProposal` action aborts. On success, `RemoveProposal`
deletes the proposal raw key while `MoveToHub` retains it; both write the
global log through the root. Permission and exact-kind decisions are explicit
inputs. Voting on other proposal kinds still needs export-level composition
with their proposal, bond, and asynchronous effects.
`Model/SignalVoteExport.lean` composes the `ProposalKind::Vote` branch with
the same generated wrapper. It requires a present, decodable proposal raw
key, a readable policy, and a stored Vote kind, then binds the caller and
proposal ID to the wrapper arguments. It uses the existing multi-role vote
and bond model: Removed deletes the proposal key, while Approved, Rejected,
InProgress and Expired rewrite it before the root write. The proofs establish
those raw-key effects and the wrapper composition. Role selection, policy
threshold refinement, proposal/root encoding, detached transfer execution,
and the other proposal kinds remain separate obligations.
`Model/VoteFinalizeExport.lean` composes `Action::Finalize` for a stored Vote
proposal. It binds the current caller and ID at the wrapper, requires a
present decodable proposal key and readable policy, and rejects u64 timestamp
addition overflow. Finalize uses policy roles in vector order; Approved
executes the synchronous Vote action and Expired rejects it. Both store the
updated proposal and schedule a transfer of the current policy proposal bond.
Lean proves the bond amount, proposal/root writes, missing-key abort and
nonpayable guard. Finalize now uses checked ratio evaluation, so overflow
aborts its branch selection, while expiration returns before an unsafe role.
Policy role lookup, exact Borsh refinement and Finalize for other proposal
kinds, including their callbacks and bounty effects, remain open.
`Model/ViewExport.lean` connects all 20 named view exports to a generated view
wrapper that checks export classification and preserves the raw trie. The
composed proofs cover saturating storage reserve/available balance, delegation
defaults and total, `has_blob` reading the raw digest key, policy version
failure, malformed factory information, pagination overflow, missing proposal
and bounty entries, and absent claim defaults. The export audit checks that
the named compositions exactly cover the view inventory. Host inputs,
LookupMap decoding and JSON serialization remain explicit inputs.
`Model/PolicyArithmetic.lean` models the checked u128 ratio calculation
before the final cap. Its proofs distinguish multiplication overflow from
overflow of the subsequent `+ 1`: at total weight `u128::MAX`, ratios 2/1
and 1/1 respectively fail even though the mathematical capped result fits.
The proof now characterizes success exactly: both intermediate operations
must fit. The earlier `validRatio` condition suffices but excludes the safe
1/2 ratio at `u128::MAX`. A Current-valued policy replacement checks only
the version, so it can install an unsafe voting threshold. A pinned-source
fixture submits and approves such a replacement through the public proposal
path, then confirms the stored threshold panics at that total weight. The
ordered-role projection proves that an earlier decisive role skips an
unsafe later ratio, while a source fixture confirms that reversing the role
order panics at the same total weight. The checked status model preserves
the source's status guard and checked u64 expiry sum before role evaluation;
it agrees with the mathematical status model when evaluated ratios are safe
and those width bounds hold. The source fixture confirms expiration returns
before the unsafe ratio and an overflowing expiry sum panics first. A checked
delegation trace reaches `u128::MAX` from zero through
`register_delegation` and `delegate`, given a
configured staking ID and calls from that account; the source fixture
executes those methods before testing role order. It also submits a Vote
proposal under a policy where the unsafe role is the sole authorized voter;
the native `act_proposal` VoteApprove and Finalize calls both panic on that
ratio. The staking contract's economic backing, receipt rollback and
deployed policy remain separate conditions for production impact.
`Model/PolicyTimeTrace.lean` composes an approved policy-parameter patch,
public proposal creation and the checked VoteApprove/Finalize status paths.
Lean proves that setting `proposal_period` to `u64::MAX` makes both paths
abort for every positive submission timestamp; a concrete trace uses a
proposal created at timestamp 1. The pinned-source fixture approves that
patch through `add_proposal`/`act_proposal`, creates Vote proposals at
timestamp 1, and confirms both later actions panic on the checked u64 sum.
This is conditional on governance approving the patch; the native fixture
does not execute the generated Wasm wrappers or prove host rollback.
`Model/Policy.lean` uses
mathematical naturals; `validRatio` states the nonzero denominator and u64/u128
bounds needed to interpret the Rust calculation without overflow. In
particular, the source computes `numerator * total / denominator + 1` before
capping it, so merely proving that the capped mathematical value fits u128 is
insufficient. No theorem here establishes that `validRatio` is an invariant of
every reachable policy. Both default examples (2 of 2 and 3 of 5), the
quorum floor, ratio cap, approval priority, and the zero-threshold approval
case are checked. A two-role witness proves that reversing conflicting
decisive roles changes the result, and the strict expiration boundary is
checked in the mathematical-time model; u64 time addition remains a separate
runtime obligation. `Model/Status.lean` projects `Policy::proposal_status`
for a caller-supplied role order, including the initial status guard,
strict expiration, Everyone-role skip, group/member weighting and first
decisive role. Its proofs show expiration precedence, preservation of Failed
when no role decides, a zero-quorum empty-group approval, and a conflicting
role-order witness. A general theorem shows that if every decisive role has
the same outcome, the first decisive outcome is that one regardless of its
position. Role-name lookup, policy-map integrity and arithmetic width still
need refinement.

`Model/Authorization.lean` models all four permission-string patterns and the
two role-name lookups: later matching entries overwrite permissions in
`get_user_roles`, while `internal_get_role` uses the first entry for voting
rules. A checked duplicate-name witness shows these can select different
roles. A general theorem proves that **unique role names** align the
permission lookup with the first matching role entry (provided that entry
matches the user). The source does not enforce unique names for a supplied
current policy, so this remains an explicit policy invariant or trust
assumption, not an unconditional contract guarantee.
The authorization model now also defines the canonical set of names returned
by `can_execute_action`, with later matching permissions per name and a
permutation relation for the source HashMap's unspecified output order. Within
that source-level relation, it proves that every selected name is allowed and
the returned Boolean is true exactly when the selected list is nonempty.
Under an explicit condition
that every decisive authorized role agrees, the composed status theorem shows
the order cannot change the result. A pinned-source duplicate-name test
confirms the sharper trap: a later role grants permission while the first
same-named role supplies the voting weight. The proof still takes resolved
role rules as an input; a whole-policy storage refinement is open.

`Model/Proposal.lean` models the one-role pre-execution vote branch with an
atomic abort, and the callback status branch under explicit proposal-existence,
self-caller and result-count guards. Its proofs establish that a completed vote
records the voter, rejects a second vote from that account, and increments an
approval count by the selected role amount. Callback proofs cover both guard
failures and the Approved-to-Failed and Failed-to-Approved transitions. This
projection omits multi-role count updates, the connection from voteStep to
expiration and the ordered-role status model, receipt
creation, proposal deletion, bond transfers, storage serialization and failure
of internal bounty processing; these must be modeled before claiming the
exported methods are verified.

`Model/MultiVote.lean` extends the selected-role count and status projection
to every role name returned by authorization, in the actual returned order.
Each role uses one vote for RoleWeight or the caller's current delegation for
TokenWeight; checked u128 additions and the checked u64 expiry sum abort the
modeled transaction. Its status call now also uses the checked ratio model,
so overflow after counting aborts instead of producing a mathematical
threshold. The proofs cover exact selected-role count increments,
overflow, preservation of the selected-role count, duplicate-voter exclusion,
and the source's count-before-expiry behavior: a late vote is counted before
the proposal becomes Expired. A pinned-source test obtains two authorized
roles from `can_execute_action`, confirms weights 1 and 7, and checks the
expiry branch. The model takes the selected role order and first-name voting
rules as inputs; connecting them to the policy HashMap and concrete storage,
preserving unselected persistent counts and receipts, and host rollback
remain separate obligations.
`Model/PolicyRoleResolution.lean` connects an authorized ordering of role
names to the first policy-vector entry for each name, supplying the exact
ordered `StatusRole` list consumed by the vote model. Lean proves that every
authorized name resolves, that no selected entry silently disappears, and
that coherent first-entry weight kinds agree with the authorization model.
A duplicate-name witness combines later-entry permission approval with
first-entry status rules, matching the pinned-source duplicate-role fixture.
The caller's stored delegation, concrete vote-policy decoding, HashMap
iteration order and LookupMap vote counts remain refinement inputs.
`Model/RoleMatching.lean` computes Everyone, Member and Group matching from
the caller's account and delegated weight, then materializes authorization
entries and status-role kinds together. Lean proves the materialized weight
kinds stay aligned and every authorized ordering still resolves. Group
membership uses a list with a separate `Nodup` condition for source HashSet
size; a pinned-source fixture checks the Member threshold, Group membership
and duplicate-eliminating group size. AccountId and HashSet/Borsh refinement
remain open.
`Proofs/GroupSetInvariant.lean` proves the group-list `Nodup` condition is
preserved by every role mutation when any newly supplied role is canonical.
The canonical mutable role list also materializes into a canonical group
matching image. Repeated native AddMember and RemoveMember proposals confirm
the source HashSet's idempotent behavior. Arbitrary supplied role JSON/Borsh
still needs the HashSet-decoding refinement.

`Model/VoteSignal.lean` composes that count/status step with the exported
`act_proposal` effects for a signaling `ProposalKind::Vote`. Approved and
Rejected store the proposal, saturating-subtract the **current** proposal
bond from the lock and detach one refund; Removed deletes the proposal but
leaves the lock and sends no refund; Expired and InProgress store the counted
vote without changing the lock. Successful paths append one bounded global
action-log entry. Lean proves each branch and the log bound, and a pinned-
source test checks all five outcomes plus created transfer receipts. This
scope excludes other proposal kinds, bounty-claim removal, asynchronous
execution callbacks, and a host proof that panics roll back provisional
log/count writes.

`Model/ProposalCreate.lean` projects the successful and aborting branches of
`add_proposal` after policy decoding and authorization lookup. It includes the
exact bond equality, current-policy version, base-token message and one-time
staking guards, the checked u64 proposal-ID increment, saturating bond lock,
new proposal fields and the bounded 20-entry action log. Its successful-branch
proof identifies the returned old ID and the stored in-progress proposal;
separate proofs cover the guards and first-match map update. A map invariant
states that every stored `ChangePolicy` kind uses Current. Lean proves it is
preserved by a successful validated creation, including when insertion
replaces an existing ID, and by an update that keeps a looked-up proposal's
kind. The permission
Boolean is supplied by the authorization layer rather than yet connected to
it. SDK JSON/Borsh parsing, storage writes and rollback remain open.

`Model/ProposalAct.lean` covers the non-vote `act_proposal` branches after
proposal lookup, authorization and exact-kind comparison. It models the
global 20-entry action log and atomic aborts for missing proposals, denied
permission, wrong kind and passing `AddProposal` as an action. A successful
`RemoveProposal` deletes the stored proposal **without reducing**
`locked_amount`. `MoveToHub` commits the global log entry but leaves the
stored proposal, its status and lock unchanged; the transient per-proposal
log is not saved because both branches set `update = false`. These are
source-model effects; the exact kind-equality result and permission result
are external Boolean inputs, and concrete rollback remains open. Lean also
proves removal and every successful non-vote branch preserve the stored-policy
kind invariant.

`Model/Finalize.lean` composes the ordered-role status model with the
`Finalize` action's branch selection. It proves lookup, permission, exact-kind
and terminal-status guards; expiration selects the reject/refund branch, while
approval selects execution. The current source also permits an authorized
**InProgress** proposal to finalize early when a role reaches approval (a
zero-threshold witness is checked), although its comment describes expired
or failed proposals. Recomputed Rejected, Removed, InProgress or Failed
statuses abort this action. The selection model does not claim that the
chosen execution or refund receipt succeeds. The ordinary Expired branch is
joined to bond and state effects below; Approved and BountyDone effects remain
separate obligations.

`Model/ProposalBonds.lean` models `internal_return_bonds` using the **current**
proposal and bounty bond values. An ordinary proposal subtracts the current
proposal bond and returns one transfer promise; `BountyDone` first subtracts
and detaches the bounty-bond transfer, then subtracts and returns a separate
proposal-bond promise. General proofs give the exact scheduled total and
conditional lock equations when the counter covers the bonds. A checked
witness shows saturating subtraction can leave the lock at zero while the
scheduled refund total is larger than the former lock. This does not prove
the account balance can pay those receipts. The ordinary Expired finalization
projection now composes status selection with that helper: it stores Expired,
decrements the lock by the current proposal bond and detaches the refund
receipt. Full proposal execution, receipt success and historic-bond
conservation remain open.

`Model/BountyResolution.lean` joins the one-bounty claim projection to the
asynchronous `BountyDone` payout. Scheduling removes the first matching claim
and decrements its count **before** the payout result is known, without
changing `times` or the lock. The failed callback only stores Failed, so a
checked trace leaves no matching claim for a direct `Finalize` retry; that
retry aborts unless another claim for the same receiver and bounty has since
been added. The successful callback updates `times` and returns bonds using
the current policy. In particular, `times = 1` becomes a stored zero, and
only a success starting at zero removes the bounty. These proofs assume one
bounty, an authenticated callback with one result, coherent storage and
atomic aborts. The rejected-vote and expired-`Finalize` branches remove the
claim and detach **both** current-policy bond refunds; a Removed vote removes
the claim and deletes the proposal without refund. The Expired branch is
composed with the ordered-role `Finalize` selector under its authorization,
kind, status and time guards. If no matching claim exists, rejection or
expiration aborts atomically despite the provisional refund scheduling. These
proofs do not establish payout receipt delivery, every `Finalize` execution
branch, or account-balance solvency.
The pinned-source oracle now reaches `BountyDone` rejection and removal from
a real claim and completion: `VoteReject` removes the claim, stores Rejected
and schedules both current-policy refunds; `VoteRemove` removes the claim and
proposal but leaves both bonds locked; expired `Finalize` removes the claim
and refunds both bonds. A claimer can give up after creating the proposal,
leaving no claim; a subsequent rejection then aborts at claim lookup. The
checked rejection theorem covers this missing-claim abort for every rejection
kind, conditional on host rollback of any provisional refund receipts.

`Model/BountyPayoutExecution.lean` composes that claim-removal step with the
actual approved payout receipt plan and guarded callback. NEAR creates a
transfer; an FT bounty always uses `ft_transfer` with one yoctoNEAR and 10
Tgas, never `ft_transfer_call`, because the source passes no message. Both
schedule `on_proposal_callback` and defer refunds. The checked callback
composition requires a present proposal, self-caller and exactly one promise
result. A failed result leaves the claim removed, times unchanged and both
bonds locked. A successful result uses **current** bond amounts, updates
times and schedules two refunds. The source oracle reaches this path through
`bounty_claim`, `bounty_done`, and approval, checking NEAR/FT receipts,
success/failure and failed direct retry. It also confirms that changing policy
bonds can schedule refunds exceeding the former lock, and that a second
authenticated successful callback under the same preconditions removes a
zero-times bounty and schedules both refunds again. Direct native callback
calls bypass the generated `#[private]` wrapper, so repeat reachability is
not established. Token parsing, external receipt outcome, host rollback and
account solvency remain open.

`Model/BountyDone.lean` projects the exported `bounty_done` method for one
bounty and composes active completion with `addProposal`. The claim now
includes its on-chain `completed` bit as well as ghost bond history. A
completed **first matching claim** aborts before checking expiry, even when
a later claim from the same account is uncompleted. Expiry is strict
(`now > start + deadline`): anyone may clear an expired uncompleted claim,
without proposal authorization or an exact attached proposal bond, and the
claim slot is freed without refunding its bond or reducing the lock. At the
deadline equality, only the claimer can submit; proposal creation then checks
the current proposal bond, authorization and ID increment before marking the
first claim completed. Checked proofs cover these branches, first-match
preservation, a general completed-first guard, and a duplicate-claim witness.
The model requires bounded u64
time addition; reachability of this bound, SDK argument parsing, multi-bounty
account vectors and host rollback still require refinement.

The `bounty_done` and `bounty_giveup` projections are also composed in a
checked trace. `bounty_giveup` has no completed-claim guard: a claimer can
remove a completed claim and schedule its current-policy bond refund while
the `BountyDone` proposal remains stored. With no matching claim, subsequent
payout scheduling aborts. If the same account makes a fresh claim and that
old proposal later reaches Approved, the payout helper can instead consume
the **fresh, uncompleted** claim; it does not check the completed bit. The
trace proves these source-model states and helper results, conditional on
the vote reaching approval. The model alone does not establish voting
reachability or payout receipt success.
Pinned-source tests now reach both traces through exported methods: after
give-up and a fresh claim, the default council can approve the old proposal
and its payout consumes the new uncompleted claim; with two claims by one
account, the completed first match blocks completion of the later one.
These fixtures establish reachability under their policy and timing inputs,
not a universal voting or receipt-delivery claim.
An authorized `RemoveProposal` action differs from `VoteRemove`: it deletes
the pending `BountyDone` proposal without calling the bounty rejection
helper, leaving the completed claim, claim count and lock unchanged. A new
composition theorem connects this action to the one-bounty state projection,
and the pinned-source oracle confirms the case after granting the required
`RemoveProposal` permission. The model omits the global action-log write in
this composition; `Model/ProposalAct.lean` covers that write separately.

`Model/Delegation.lean` projects the three staking-gated mutations onto a
finite balance map, including the exact saturating storage deposit and the
release profile's checked u128 arithmetic. The proofs establish that fresh
registration and successful delegate/undelegate preserve `total = sum of
balances` under the stated caller, registration and arithmetic conditions.
A checked witness shows that registering an already-delegated account resets
its balance to zero without reducing the total, so the conservation invariant
is **conditional on fresh registration**. Another witness shows that
undelegating zero from an absent account creates a zero record. The actual
`LookupMap` layout is now projected in `Model/DelegationEncoding.lean`:
prefix 2, a Borsh AccountId key, and a 16-byte little-endian u128 value.
Checked proofs establish key injectivity and bounty-key separation, bounded
value round trips, the empty image, default-zero reads, and preservation of
the raw image and width bounds by successful register/delegate/undelegate
steps. The isolated [native oracle](oracle/README.md) confirms the exact
Lean fixture bytes through the pinned source methods, including the
re-registration and zero-undelegation anomalies. The root-state serialization
of `total_delegation_amount`, attached-deposit transfer, rollback and SDK
wrapper behavior remain outside this projection.

`Model/Bonds.lean` projects one bounty's claim count, ordered claim records and
`locked_amount`. Its `paidBond` field is **ghost history**; the on-chain
`BountyClaim` does not retain the original bond. The `completed` bit reflects
the on-chain claim record. General proofs show that a
valid claim increments the count and saturating-adds its attached bond, while
timely and late give-up each remove exactly one claim and preserve count/list
coherence. Timely give-up refunds and subtracts the **current** policy bond;
late give-up refunds nothing and leaves the lock unchanged. Checked examples
show that changing the policy bond from 10 to 5 changes the refund to 5, and
that future-start time subtraction aborts. These are source-branch facts, not
a global bond-solvency theorem. They assume coherent claim counts and omit
other bounty IDs, proposal bonds, asynchronous transfer success and storage
serialization.

`Model/BountyStorage.lean` extends claim creation and removal to the source's
two-map shape: account-keyed claim vectors and bounty-keyed counts. Removal
selects the **first claim for the requested bounty ID** in that account's
vector, deletes the account key when its vector becomes empty, and leaves a
zero-valued count key present. General proofs show one-element removal,
preservation of other accounts' vectors and other bounties' counters, and
preservation in order of all other-bounty entries in the same account vector.
Creation appends to the account vector, defaults a missing count to zero,
and preserves unrelated keys. The model checks u32, u64 and u128 input bounds
needed for this source branch, including the resolved Borsh 1.6 vector-length
limit: adding to an account vector already at u32 maximum aborts. A
finite-account coherence predicate equates
the stored count for one bounty with the total number of its claims in the
enumerated account vectors. General proofs show that successful creation and
removal preserve this equation when the affected account occurs once in the
enumeration; removal also requires the source's present, positive count.
The proofs now lift to **every bounty ID simultaneously** over the same
enumerated accounts: adding or removing one claim preserves the target
count equation and all other bounty count equations. The maps are
mathematical functions. Coverage of **all** occupied accounts, Borsh key
encoding refinement, and linkage to the earlier one-bounty lifecycle still
need proof.

`Model/BountyEncoding.lean` records the pinned SDK's legacy `LookupMap`
layout: the `StorageKeys::BountyClaimers` and `BountyClaimCounts` enum tags
are bytes 5 and 6, followed respectively by a Borsh AccountId string and a
little-endian u64 bounty ID. Checked proofs establish bounded count-key
injectivity, account-key injectivity, and disjointness from each other and
the other six storage-key tags. A Borsh claim record has three u64 fields
and one Boolean byte (25 bytes); its vector has a four-byte length prefix.
The stored count is four bytes. A bounded proof shows that equal encoded
claim records have equal on-chain fields; the ghost `paidBond` does not
appear in bytes. This layout was derived from the pinned source and resolved
near-sdk 5.24.1 / near-account-id 2.5.0 code. A checked decoder round-trips
bounded single claims, claim vectors and counts, rejects invalid Boolean
bytes, truncated vectors and trailing bytes, and omits ghost bond history.
The isolated [byte oracle](oracle/README.md) compiles the pinned Rust
`BountyClaim` and near-sdk `LookupMap` code in a temporary native test copy.
It confirms the checked Lean fixture arrays for an open claim, completed
claim, a nonempty-vector rewrite, final-key removal, and retained zero
counts. One test exercises the actual source methods; the fixture does not
establish general encoder equivalence.
`Model/BountyTrie.lean` adds a functional raw-trie image relation at every
claimers key and every bounded u64 count key. Checked claim-creation and
claim-removal theorems show that their source-ordered raw writes preserve this
image relation. Removal deletes an empty account vector's key, rewrites a
nonempty vector, and retains the count key even when its new value is zero.
Conditional read theorems decode image entries back to logical physical
claims and counts when stored values satisfy their bounds.
`Model/BountyTrie.lean` also states the Borsh-width invariant for every
account vector and bounty count. `Proofs/BountySerial.lean` proves that
successful modeled claim creation, claim removal, and timely completion's
account-vector rewrite preserve it together with the raw-trie image relation.
Creation's u64, u32 capacity, and vector-length bounds are derived from its
modeled abort guards; removal preserves validity of the surviving records
and decreases the present count. Completion changes only the first matching
unfinished claim's Boolean, preserving vector length and all bounty counts.
The fresh empty-map projection satisfies both invariants and finite-account
count coherence; completion preserves count coherence for any account
enumeration. The combined invariant discharges the conditional read theorems
for each bounded key. `Model/BountyTrace.lean` restricts a reachable trace to
these three successful storage mutations from the fresh empty projection;
`Proofs/BountyTrace.lean` lifts the combined invariant by induction over any
such trace and proves that all its bounded raw keys decode to the logical
claims and counts. A second trace relation fixes a duplicate-free finite
account enumeration and requires each mutated account to occur in it.
Permutation lemmas lift the add/remove count proofs to any account order;
induction then preserves all bounty-count coherence equations along that
covered trace. A separate induction proves that accounts outside the list
have no logical claimer entry; the raw-image relation then proves absence of
their raw claimer keys. This support result does not require the list to be
duplicate-free. It applies to traces from the fresh projection, not an
arbitrary deployed snapshot. A checked duplicate example confirms that a
completed first matching claim blocks completion of a later unfinished match.
Equivalence of the Lean decoder to the pinned Rust Borsh implementation,
establishing the initial combined invariant from an actual storage snapshot
(including freshness of the two bounty namespaces), and contract-state root
serialization remain open. The trace does not yet cover every DAO entry point
or proposal-side storage write.

`Model/Upgrade.lean` projects the raw `update` export after host reads. It
distinguishes absent, stored and malformed `FACTORY` bytes; an absent value
uses the parsed parent account with `auto_update = true`. The proofs cover
malformed/missing-fallback aborts, rejection of unauthorized or disabled
factory calls, the self branch's required successful promise result, the
factory branch's required raw input, and the scheduled self receipt with
use-global-contract hash followed by `migrate` at zero deposit and static gas.
The hash function is abstract here, and the fallback parent is an input rather
than a proved parser result. The model does not prove SHA-256, global-code
publication, host receipt execution, migration success, or the governance
rules that may change factory information.
`Model/ExecuteUpgrade.lean` separately composes the approved `UpgradeSelf`
and `UpgradeRemote` proposal helpers with immediate bond return. Both schedule
an independent call, return `Value(())`, and therefore detach the **current**
proposal-bond refund without scheduling `on_proposal_callback`. `UpgradeSelf`
uses the current account's parent even when stored factory info differs;
`UpgradeRemote` requires code bytes at the raw hash key and aborts if absent.
The proofs fix receiver, method, arguments, gas/deposit and refund structure;
a pinned-source oracle checks the two receipt graphs, immediate lock decrement
and missing-hash abort. The factory JSON bytes, AccountId parsing, later
receipt results, deployed code and migration remain outside this claim.
`Model/TransferExecution.lean` projects approved transfer execution after
successful token-ID parsing. Native NEAR transfers ignore a stored message;
fungible-token transfers choose `ft_transfer` or `ft_transfer_call` based on
its presence, attach one yoctoNEAR and 10 Tgas, and use the proposal
description as memo. Every branch schedules a 10 Tgas callback to this DAO
and leaves the proposal-bond lock untouched until that callback. Under an
existing proposal, authenticated self-caller and exactly one promise result,
success marks Approved and returns the **current** policy bond; failure marks
Failed and retains the lock. The source callback has no stored-status guard,
so the proof and native test show that a second successful invocation under
those same preconditions schedules another refund even after approval. Direct
native calls bypass the generated `#[private]` wrapper: this is a conditional
behavior claim, not a claim that arbitrary external users can invoke it.
Token AccountId parsing, actual receipt delivery, external FT behavior,
solvency and NEAR host rollback remain outside this projection.
`Model/FunctionCallExecution.lean` projects approved arbitrary calls as one
promise batch to the chosen receiver with every supplied action in order,
followed by one proposal callback. An empty action list still creates that
batch and callback; neither case releases the bond immediately. Lean proves
action order/count, the empty-list case, callback plan and success/failure
bond effects through the shared callback model. The pinned-source oracle
checks two actions with distinct argument bytes, deposits and gas, plus an
empty list and both callback outcomes. The contract does not validate
nonempty actions or aggregate gas/deposit at proposal creation. AccountId
parsing, host resource limits, per-action execution, atomic batch semantics
and whether a particular promise result is reachable remain separate
runtime obligations.
`Model/SyncGovernance.lean` covers three synchronous governance execution
branches after an approved vote or successful finalization: replacing a
current policy's projected parameters, patching the four policy parameters,
and setting the staking contract. Replacement and patching refund the
**pre-execution** proposal bond, even when they install a different bond;
the model proves the unchanged fields for absent patch values. Staking is
checked again at execution and aborts if already set. The pinned-source test
creates two staking proposals while the slot is empty, approves the first,
and confirms the second then aborts. Successful branches refund immediately
without a callback. The model projects policy parameters rather than roles,
permissions or serialization, and it assumes the pre-execution policy has
already decoded to Current. A separate stored-version transition captures
the validation boundary: `add_proposal` rejects a Default-valued
`ChangePolicy`, whereas the lower-level execution branch writes a proposal's
stored `VersionedPolicy` unchanged. Lean proves the validated replacement
preserves Current and rejects Default, then inducts over any successful trace
of validated replacement and shortcut mutation actions from a Current policy.
It also shows that bypassing validation
with a stored Default proposal would make the next policy read and action fail.
The pinned-source test confirms both branches: public creation rejects Default;
a test-only synthetic proposal inserted directly into the map can be approved,
stores Borsh tag 0, and makes `get_policy` and `add_proposal` panic. This is a
conditional malformed-proposal state, not evidence that ordinary creation can
reach it. The proposal-map invariant covers validated creation, same-kind
updates and non-vote removal in their projections. A full Current-policy
invariant still requires constraints on old proposal storage, migration and
concrete storage refinement. The model does not prove host rollback of a
failed transaction.
`Model/RoleMutation.lean` projects the policy helpers for adding/replacing
and removing roles, adding/removing group members, and replacing the default
vote policy. Each name search selects the **first** matching vector entry;
duplicate later entries are preserved. A missing name or a first matching
role of the wrong kind is a logged no-op, yet execution stores the policy and
returns the old proposal bond immediately. Lean proves first-duplicate
behavior and the refund/no-callback rule; pinned-source tests check duplicate
replacement/removal, group membership changes, both no-op logs, and default
vote-policy replacement. The model carries permission and vote-policy data
as opaque role fields. Its list representation of a group corresponds to
Rust's `HashSet` only under set-equivalence (or unique-list) refinement;
HashSet order, serialization and general policy authorization are not proved
by these mutation theorems; the canonical-group condition above states the
required list invariant explicitly.
`Model/SyncSettings.lean` covers the remaining synchronous settings branches:
`ChangeConfig` replaces the stored name, purpose and metadata, while
`FactoryInfoUpdate` overwrites the raw `FACTORY` key and can thereby repair
malformed old bytes. Both return the old proposal bond immediately without a
proposal callback. The factory-write theorem composes with `runUpdate`: a
stored disabled factory cannot authorize a non-self caller; an enabled
matching factory with raw input reaches the modeled use-global-contract and
`migrate` receipt. Source tests check the config replacement, raw Borsh key
rewrite from malformed bytes, disabled flag, and the enabled raw-update
receipt. The native raw-update success test runs in a separate test process
because that entry point installs a process-wide panic hook. A direct denied
raw-update test cannot be caught safely in this native mock; the denial is
proved conditionally from the source-level authorization model. Actual
receipt execution, hashing and migration remain external obligations.
`Model/AddBountyExecution.lean` covers approval of an `AddBounty` proposal:
it writes at the old `last_bounty_id`, checked-increments that u64, leaves
claim counters unchanged, and returns the old policy proposal bond without a
callback. The proof includes the overflow abort and accepts zero `times`
and an unparsed token string, as the source does. Composed with the claim
model, zero `times` makes every claim fail the capacity guard. A pinned-source
test confirms the zero-times/invalid-token storage, immediate refund, and
claim rejection. A deliberately inconsistent reused-ID fixture confirms
that the source overwrites the bounty entry but retains its old claim count;
thus a fresh-ID/map-coherence condition is needed for a global bounty
invariant. Rust's `U128`, `u32` and `U64` field widths are explicit input
constraints in `validBountyImage`. Native panic testing confirms the u64
overflow, but transaction rollback of the earlier map write is a host
obligation. The list map projection also requires unique IDs to refine a
concrete `LookupMap` state.
The factory-info view shares `effectiveFactory` with the raw upgrade path.
Its missing-key fallback takes the suffix after the **first** dot of the
current account ID, preserving further subaccount labels, and enables
auto-update. The stored value overrides that fallback; malformed Borsh bytes
abort, as does a missing key on an account with no dot. Lean proves the
conditional fallback and override branches, while a pinned-source oracle
checks nested-account, malformed and no-dot fixtures. AccountId parsing and
general Borsh correctness remain external obligations.

`Model/Migration.lean` projects the `#[private]` `migrate` entry after state
deserialization. Its `StateCore` names every pre-existing V1 field while
treating complex values and collection handles as opaque. Checked branch
proofs show that a missing version key selects V1, V1 copies those modeled
fields into V2 with an empty action log and writes `STATEVERSION=V2`, and V2
returns the current state without a version-key write. External callers,
malformed version bytes and absent state abort. `Model/RootStateEncoding.lean`
now proves the V1 root image is the V2 image with an empty four-byte action-log
length appended. A pinned-source migration fixture confirms the 89-byte V1
root becomes a 93-byte V2 root with the original prefix unchanged. It also
confirms that migration leaves a separately stored legacy Default policy
untouched: `get_policy` then panics. Lean records both the unreadable Default
branch and readable Current branch. A reachable-policy-version invariant,
general Rust-Borsh equivalence and atomicity of the version/state writes
remain open. `Model/WrapperInit.lean` also projects the pinned SDK's
`#[private] #[init(ignore_state)]` wrapper: it rejects an external caller and
nonzero deposit, skips the root-existence guard, invokes `migrate`, then
writes the returned root. Lean proves the V1/missing-version path writes V2
before the root and the V2 path leaves version bytes untouched while
rewriting the root. A new native V2 fixture confirms direct `migrate` reads an
existing root and returns identical bytes; the wrapper's concrete Wasm
execution and rollback are not proved by this projection.
`Model/InitExport.lean` composes both initializer wrappers with their named
contract exports. For `migrate`, the version branch is selected from the raw
`STATEVERSION` bytes: absence selects V1, exactly `[0]` and `[1]` select V1
and V2, and unknown tags or trailing bytes abort. The V1 and V2 decoder
inputs are tied to the bytes read from `STATE`; Lean proves that missing root
bytes and malformed version bytes abort, and proves the version/root write
effects on the successful V1 and V2 branches. The decoders and encoder remain
explicit refinement inputs, so these theorems do not establish general Borsh
equivalence or concrete Wasm behavior.

`Model/Initialize.lean` projects `new` across all constructor fields. It
proves zero locked funds and delegated supply, zero next proposal/bounty IDs,
absent staking ID, empty collection handles and action log, a Current stored
policy after either input variant, predecessor-based enabled factory info,
and the V2 version marker. A Lean fixture proves the exact Borsh bytes for
the `FACTORY` and `STATEVERSION` writes; a pinned-source native test checks
those bytes and selected empty-state reads. `new` accepts a supplied Current
policy without validating role uniqueness or threshold arithmetic, so those
remain reachability preconditions for later proofs. `Model/RootStateEncoding.lean`
models the root `Contract` Borsh image: eight one-byte, length-prefixed
collection handles, u128 balances, optional staking account, u64 counters
and an ordered action log. The 93-byte constructor image and a 140-byte
populated fixture are checked in Lean and against independently assembled
bytes in pinned-source tests. Lean proves the locked amount, staking field
and both counter offsets for arbitrary modeled scalar values, with counter
positions adjusted for the staking account's byte length. Explicit width
and 20-log bounds are stated as preconditions; they are not established for
every reachable state. The source oracle checks all seven `Action` Borsh
tags. `Model/ConfigPolicyEncoding.lean` now covers the separate `Config` and
`VersionedPolicy` values at keys 0 and 1, including role kinds, weight
thresholds, ordered role permissions, policy-map entries, bonds and periods.
The model states u32/u64/u128 bounds, a nonzero ratio denominator and sorted
set/map entries as explicit conditions. Lean checks constructor and role
fixtures; pinned-source tests compare full bytes, including sorted HashSet
and HashMap serialization, and confirm `new` stores a Current policy after a
Default input. `Model/ConfigPolicyDecoding.lean` adds a byte parser, with
general Lean round-trip proofs for bounded Config and nested versioned Policy
values, plus trailing-byte, invalid-tag and zero-denominator rejection.
Pinned-source tests confirm malformed UTF-8, trailing bytes, unknown policy
tags and a zero NonZeroU64 denominator are rejected. They also expose a
separate constraint: the resolved Borsh decoder accepts unsorted or duplicate
HashSet and HashMap entries, then normalizes them on reserialization; a later
duplicate map key wins. The Lean parser retains raw lists, while a separate
normalization model sorts and deduplicates sets and selects the last map value.
Lean proves that normalization preserves group matching, permission membership
and every per-kind vote-policy lookup, including absent keys, and checks a
noncanonical role fixture against source behavior. The general round-trip
theorem applies to canonical ordered encodings, not arbitrary stored bytes.
`Model/ConstructorTrie.lean` composes the four direct `new` writes with the
SDK wrapper's later root `STATE` write, starting from empty storage. Lean proves
the resulting five keys are distinct, gives their exact values, excludes all
other keys, and shows every suffix under collection prefixes 2–7 is absent.
For bounded modeled values, it also parses the stored Config and Current policy
back to those values. The pinned-source fixture checks that direct `new` has no
root state, then explicitly writes the root and checks its bytes and the empty
single-byte collection prefixes. This is a fresh-storage constructor image;
`Model/WrapperInit.lean` separately projects near-sdk 5.24.1's generated
`#[init]` sequence: zero attached deposit, decoded arguments, absent root
`STATE`, then `new` and root write. Lean proves re-initialization is rejected,
the fresh run produces the five-key image, and an absent root permits
initialization even if other keys already exist. In that nonfresh case the
constructor overwrites its four auxiliary keys and preserves unrelated keys.
The native source fixture checks this direct-`new` behavior with pre-existing
malformed Config/Policy bytes and an unrelated key. Wrapper code generation,
argument-parser equivalence, rollback and concrete Wasm execution are still
refinement obligations. General equivalence of Lean
string ordering to Rust `Ord`, AccountId validation,
arbitrary Rust-Borsh equivalence and transaction rollback remain external
obligations.

`Model/Blobs.lean` projects one hash slot's raw bytes and `LookupMap` owner
index. It proves the raw-key existence check, exact `len + 32` storage-price
formula, owner gate, successful store/remove effects, and that `has_blob`
checks only the raw key. A raw key can be absent while its owner index exists;
`store_blob` then overwrites that owner. More subtly, `remove_blob` removes
the owner index first and then removes the raw key. The pinned SDK's
`LookupMap.remove` puts the serialized owner into the evicted register, and
a raw-key miss leaves that register unchanged in NearVM. The subsequent
`register_len` therefore uses the **stale owner-value length** for its refund
instead of aborting. The model represents that length as an input to be
refined from Borsh bytes. Refunds also use the current storage byte price,
which can differ from the deposit-era price. Full trie key separation,
SHA-256/base58 binding, Borsh sizes and receipt execution remain open.
`Model/BlobKeySeparation.lean` narrows the key-separation obligation. A
32-byte raw digest cannot equal any constructor key, a 9-byte proposal,
bounty or claim-count key, or its own 33-byte owner-index key. Delegation and
bounty-claimer keys instead have length `5 + account UTF-8 bytes`, so equality
with a raw digest requires a 27-byte account ID. Lean proves both conditions;
a pinned-source fixture confirms that valid 27-byte account IDs produce
32-byte keys in both namespaces and that a blob owner key is 33 bytes.
Whether SHA-256 of an actual input equals such an account-index key remains
unproved; length alone cannot exclude it.
The raw-trie collision projection makes the conditional effect explicit. If
the account key is already occupied, `store_blob` fails its raw-key existence
check. If a blob occupies the key first, a later delegation `LookupMap.insert`
must deserialize the old bytes as Borsh u128: malformed bytes abort, while a
decodable 16-byte payload permits the delegation write to replace the raw
blob and leaves the 33-byte owner index intact. An authorized `remove_blob`
then removes that same delegation key. Pinned-source tests reproduce both
the decodable overwrite/removal path and the malformed-deserialization panic
using a **synthetic digest-shaped key**; they do not exhibit a SHA-256 preimage
or prove host rollback after the panic.
The bounty-claimer namespace has the analogous alias condition, with a
different decoder. `bounty_claim` reads the old `Vec<BountyClaim>` before
rewriting it. Lean proves a malformed old vector blocks the checked write,
while a decodable vector permits replacement. A pinned-source test supplies
an empty-vector Borsh payload at a synthetic digest-shaped claimers key,
executes `bounty_claim`, and then shows `remove_blob` deletes the claimers
entry while its separate claim-count key remains at one. Lean proves the
raw blob removal cannot touch that 9-byte count key. A malformed payload
panics during `bounty_claim`; its earlier claim-count
write requires transaction rollback, which the native mock does not prove.

`Model/Views.lean` captures the common index loop in `get_proposals` and
`get_bounties`. It represents the checked u64 `from_index + limit` before
the `min` bound, then scans only that fixed ID window and skips missing map
entries. The proofs show that overflow aborts even when the stored last ID
would make the range empty; zero limits and starts beyond the last ID return
empty pages; every returned ID lies inside the requested window and has a
present lookup value; and the page has at most `limit` entries. A checked
example shows gaps are not filled from later IDs. The map lookup and
versioned-value conversion are opaque, so this does not establish JSON
serialization or storage integrity. The same module models the views' u128
storage-price saturation and sequential saturating subtraction for available
funds. It proves the reserve is bounded, exact arithmetic when the product
fits and the account has enough funds, and a zero available balance when
the reserve plus locked bonds covers the balance. Single proposal/bounty
lookups abort on a missing entry; claim and delegation lookups return their
defaults. A pinned-source native oracle checks sparse pages, overflow and
missing-entry panics, the available-balance examples and default reads.
Host-provided byte price, storage usage and account balance, value conversion,
JSON serialization and the concrete SDK entry points still need refinement.

`get_policy` has an additional storage-version precondition: it unwraps the
`LazyOption` and calls `VersionedPolicy::to_policy`, whose `Default` branch is
`unimplemented!()`. The view model distinguishes absent, legacy-Default and
Current policy values, and proves that `new`'s `upgrade` operation makes
either input version readable. The pinned-source oracle confirms that
manually storing `Default` makes `get_policy` panic. A Default-valued
`ChangePolicy` proposal cannot be created through `add_proposal`, but the
execution branch would store it if such a proposal were already in storage.
`migrate` also copies a V1 policy handle unchanged; migration does not repair
a Default value. The direct-field views
(version, staking ID, delegation totals, last IDs and action log) are simple
projections in the source, with defaults for an absent staking ID or
delegation balance; concrete SDK wrapper and JSON behavior remain open.
`Model/WrapperInit.lean` adds a read-only wrapper projection for views.
The pinned near-sdk 5.24.1 macro classifies an owned `self` receiver as a
view; therefore `get_staking_contract(self)` reads the root, returns the
staking ID or empty string, and has no generated state write or deposit check.
Lean proves the projected wrapper preserves every storage key and accepts
any attached deposit when state decoding succeeds. A native fixture confirms
that reading state and calling this owned method leaves the root bytes intact;
it does not execute the generated Wasm wrapper.

The [blueprint](blueprint/README.md) records the source surface, proof
obligations and contract-specific traps. A joined top-level dispatcher,
full storage-history invariants, JSON/receipt projection and concrete NearVM
refinement remain open.

The [export audit](audit_exports.py) pins the canonical factory-stored Wasm's
SHA-256 and verifies its 34 contract methods against the actual export
section, including the two generated callable functions and three non-callable
exports. This closes the export-inventory check, not the entry-point proof.

```sh
cd contracts/sputnikdao2-v3.2/verification
lake build --wfail
python3 ../../../tools/axiom-audit.py . --no-build --report /tmp/sputnikdao2-audit.json
python3 audit_exports.py
```
