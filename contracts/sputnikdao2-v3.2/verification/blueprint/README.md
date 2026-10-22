# Source review and proof obligations

The source has 4 regular core methods (`new`, `migrate`, `remove_blob`,
`get_factory_info`), 2 raw exports (`store_blob`, `update`), 3 proposal
methods, 3 bounty methods, 3 delegation mutations, and 19 views. Internal
policy and action helpers are reachable through those exports. The
[export audit](../audit_exports.py) checks this inventory against the
canonical factory-stored `contract.wasm`: 34 contract methods, two generated
function exports (`__contract_abi`, `contract_source_metadata`), memory and
two globals, for 39 exports total. This proves the inventory is complete for
that binary; it does not prove that every entry point is modeled. The audit
also checks the 34 names in `Model/ExportWrapper.lean`. Lean classifies them
as two initializers, ten mutating calls, twenty views and two raw exports,
and proves the shared generated-call guards and root write, conditional on
decoded inputs and an abstract method-body result. The
`sputnikdao2_original.wasm` kept in the source checkout has different bytes
and exports and is not the dataset's canonical binary.

1. **Policy and votes.** Roles are `Everyone`, delegation-threshold `Member`,
   and account `Group`. `Everyone` can authorize actions but is skipped by
   `proposal_status`, because it has no total role size. Permission strings
   include exact labels and wildcards. Vote weight is either one or the
   caller's current delegation; token-weighted thresholds use the current
   total delegation, while role-weighted group thresholds use the current
   group size. A threshold is `max(quorum, min(weightOrRatio, total))`; a
   quorum greater than total makes a decision unreachable by votes bounded
   by total. A zero total and zero quorum instead give threshold zero, so
   the approval branch succeeds with no votes. The default ratio is integer
   half plus one, capped at total. Ratio multiplication, division and addition
   need checked-width proof obligations. Role permission lookup uses a
   `HashMap` keyed by role name: duplicate names overwrite permissions, and
   its iteration order feeds the first qualifying role to status selection
   on a vote. `Finalize` instead passes names in `policy.roles` vector order.
   Thus a global deterministic status theorem needs a unique-name/consistent-
   role condition or an explicit order-independent proof. The current
   first-decisive theorem proves order independence when all decisive roles
   agree; it does not prove that reachable policies satisfy this condition.
   The authorization model proves that unique names align the first role
   lookup with the last-matching permission lookup. Its duplicate-name
   witness selects permission from a later matching entry while vote-weight
   lookup selects the first entry. `new` accepts a supplied current policy,
   and `ChangePolicy` checks only that it is the current version; neither
   validates name uniqueness. A complete authorization theorem therefore
   needs either a unique-name precondition or the duplicate-name behavior
   modeled through every affected entry point.
   The checked authorization model now characterizes the accepted name set
   and the allowed Boolean, while representing HashMap enumeration by any
   permutation of that set. A composed theorem makes status order-independent
   when all decisive authorized roles agree. A pinned-source fixture confirms
   later-permission/first-weight behavior for duplicate names; no theorem
   claims all reachable policies have unique names or agreeing outcomes.
   Inside a role,
   approval wins a tie before rejection and removal.
2. **Proposal lifecycle.** `add_proposal` requires an exact bond, validates
   three kind-specific restrictions, checks `AddProposal` permission, stores
   an in-progress proposal, advances the ID and saturating-adds the bond to
   `locked_amount`. The checked creation projection proves those guards,
   the returned old ID, the resulting proposal fields and the 20-entry log
   update, conditional on decoded policy, permission result and successful
   storage. `act_proposal` checks permission and exact kind; voting
   requires in-progress status and no previous account vote, then recomputes
   status. The checked multi-role projection counts every selected role using
   its weight mode and checked-u128 addition. A late vote still increments
   counts before strict expiry selects Expired; selected-role order and
   threshold-width conditions remain refinement inputs. `RemoveProposal`
   deletes the map entry without unlocking its bond.
   The signaling `Vote` kind now has a checked branch composition: approval
   and rejection detach the current proposal-bond refund; removal deletes
   the proposal without unlocking it; expiry and continued progress store
   the counted vote without a refund. The native oracle checks all five
   outcomes and transfer receipts. Other proposal kinds still need their
   execution and callback effects joined to the vote step.
   `MoveToHub` logs globally but does not mark the stored proposal as Moved
   or remove it; its local action-log update is discarded. The checked
   non-vote projection proves these branches under explicit permission and
   exact-kind inputs. `Finalize` recomputes from all policy roles only for
   an original InProgress or Failed status; the source comment's
   expired/failed description is narrower than the code. An InProgress
   proposal with an approving role can finalize before expiry. The checked
   selection model proves Approved and Expired branches and aborts for other
   statuses, conditional on internal execution/refund success. Expiration uses strict `<` after
   `submission_time + period`.
   `internal_return_bonds` uses current policy amounts, with two separate
   promises for `BountyDone`; the bounty transfer is detached inside the
   helper. A checked ordinary Expired branch composes Finalize selection with
   lock decrement and the detached proposal-bond receipt. Saturating locks
   do not themselves bound the value of scheduled refunds; account-balance
   solvency and asynchronous receipt outcomes need separate proof.
   Removing a proposal, rejecting it, and letting it expire have different
   bond effects. Failure of an external action is observed only in
   `on_proposal_callback`, which marks the proposal `Failed`; success returns
   bonds and may update bounty state. Prove transaction rollback for failures
   after provisional vote and log mutations, plus explicit promise-result
   cardinality and callback authenticity assumptions.
3. **Execution authority and async effects.** Proposal kinds include policy
   and membership changes, arbitrary function calls, transfers, self/remote
   upgrades, staking choice, bounty operations and factory info updates.
   Some actions return a promise and wait for the callback; synchronous
   actions return bonds immediately. The `UpgradeSelf` branch delegates to
   the factory and immediately returns a value, so local proposal success is
   not evidence that the later upgrade succeeds. The raw `update` export
   accepts self or an enabled factory predecessor, takes code from promise
   result or input respectively, hashes it, schedules use-global-contract
   plus `migrate`, and returns that promise. Receipt and migration semantics
   need a concrete host model. The raw `FACTORY` key defaults to the parent
   account with auto-update enabled when absent, while malformed bytes abort
   even for a self-call. The checked source-level upgrade projection proves
   the caller and data-source branches but treats SHA-256 and the parsed
   parent as external inputs. `UpgradeSelf` uses the derived default factory
   rather than the stored override, so governance-changing `FactoryInfo` does
   not automatically redirect that proposal action. The receipt alone is not
   evidence that the global contract is published or migration succeeds.
   The checked approved-upgrade projection now covers both proposal kinds:
   self routes to the immediate parent with weight 1; remote calls the chosen
   receiver with raw blob bytes and aborts if the raw hash key is absent.
   Both return `Value(())`, schedule no proposal callback, and detach the
   current bond refund immediately. The native oracle confirms these receipt
   graphs; it cannot establish later upgrade or refund delivery.
4. **Bonds, bounties and funds.** Bounty claims require the exact bond,
   remaining capacity and a bounded deadline; they increase the claim count
   and saturating-add to locked funds. A done claim creates a proposal.
   Expired claims can be cleared by anyone. Giving up within forgiveness
   schedules a refund and saturating-subtracts the lock; giving up after it
   removes the claim without refund or lock subtraction. The refund uses the
   **current** policy bond rather than the originally attached amount, which
   the claim record does not store. A policy update between claim and give-up
   can therefore change both refund and lock decrement. Treat these as
   explicit accounting branches, not a generic bond-conservation invariant.
   The one-bounty bond model proves conditional claim-count coherence and
   both give-up branches, with the historical bond retained only as ghost
   proof data. Proposal bonds and bounty-done callbacks must later be joined
   to this state.
   The bounty-resolution projection now joins claim removal to success and
   failure callbacks. It proves that a failed payout leaves the claim removed
   and `times` unchanged; a retry with no new matching claim aborts at claim
   lookup. Success with `times = 1` stores zero, while success starting at
   zero removes the bounty. This is conditional on one-bounty storage
   coherence and authenticated one-result callback execution. Rejected votes
   and expired `Finalize` schedule both bond refunds and remove the claim;
   Removed votes remove the claim and delete the proposal without refunds.
   Missing claims make these branches abort atomically, including provisional
   refunds. Other payout receipts and complete exported-method refinement
   remain open.
   The checked `bounty_done` projection exposes a first-match constraint:
   a completed first claim blocks later uncompleted duplicate claims from
   that account. Third-party expiry cleanup is permitted only at strict
   `now > start + deadline` and releases the claim slot without refunding or
   reducing the locked bond. At deadline equality, completion requires the
   claimer and successful proposal creation. The source's u64 deadline sum
   must fit; multi-bounty vectors and concrete rollback remain open.
   `bounty_giveup` does not inspect `completed`: the checked composition
   removes a completed claim and refunds its current-policy bond while its
   payout proposal remains stored. A subsequent payout attempt fails without
   a matching claim; if a fresh claim is added and the old proposal is later
   approved, the payout helper can consume that fresh uncompleted claim.
   Voting reachability and receipt success are still separate obligations.
   Account claim vectors may interleave bounty IDs while claim counts are
   keyed separately by bounty ID. The multi-bounty storage projection proves
   that first-match removal preserves every other-bounty entry in that vector
   and leaves unrelated accounts and count keys unchanged. For one bounty ID,
   checked creation and removal theorems preserve the equation between its
   stored count and the sum of matching claims over a finite account list,
   provided the affected account occurs once. The proof now quantifies over
   all bounty IDs in that enumeration. Proving that the list covers every
   occupied storage key still needs finite-map and concrete storage
   refinement.
   The legacy `LookupMap` stores Borsh keys under one-byte `StorageKeys`
   prefixes. The bounty claim and count prefixes are 5 and 6; checked key
   injectivity and disjointness proofs cover these namespaces. The claim
   value projection has 25-byte records, a four-byte vector length, and no
   historical bond field. The checked decoder round-trips bounded claim
   vectors and counts and rejects malformed lengths, Booleans and trailing
   bytes. An isolated native test against the pinned Rust type and near-sdk
   5.24.1 confirms the exact Lean fixture bytes for claim insert, timely
   completion, nonempty-vector rewrite, final removal, and retained zero
   counts. It calls the pinned source methods; this is finite evidence, not a
   general Rust-Borsh equivalence proof. A functional raw-trie image relation
   is preserved by claim
   creation's count and vector writes and by claim removal's vector
   rewrite or deletion followed by the count write. Successful modeled add
   and remove steps also preserve Borsh-width bounds for every logical
   vector and count. Timely `bounty_done` rewrites the first matching claim's
   completed flag without changing counts or vector length; its raw write
   preserves the same image and bounds. The fresh empty-map projection
   satisfies both invariants and count coherence, so image entries decode
   under the combined invariant. An inductive trace proof carries the image
   and bounds across any sequence of these three successful mutations and
   proves decoding at every bounded key in each reachable projected state.
   A covered-trace theorem also preserves every count-coherence equation for
   a fixed duplicate-free account enumeration containing each mutated
   account, regardless of enumeration order. In these projected traces,
   accounts outside the enumeration have neither a logical claim vector nor
   a raw claimers key; deployed-snapshot coverage remains separate.
   The trace excludes other DAO and proposal writes. Rust-Borsh equivalence,
   establishing the invariant from a real snapshot, and root-state
   refinement are still needed
   before the mathematical count invariant applies to deployed storage.
   Available NEAR is balance minus storage cost minus locks, both saturating.
   Prove conditional solvency and refund properties with changing policy
   bonds and delayed receipt failures visible in the assumptions.
5. **Delegation and storage.** Only the selected staking contract may
   register, delegate and undelegate. Registration requires an exact storage
   deposit. Delegation requires registration; undelegation reads an absent
   record as zero and checks only the user's previous weight. Prove that
   total delegation equals the sum of registered weights under explicit
   fresh-registration, no-overflow and coherent-storage conditions.
   Re-registering an existing positive balance resets it to zero without
   changing the total; `new` starts coherent but the staking contract can
   later break this invariant. Zero undelegation of an absent account also
   creates a stored zero record. The delegation `LookupMap` projection now
   proves prefix-2 AccountId key separation, bounded u128 value decoding,
   and raw-image and width preservation across the three successful
   mutations; a native pinned-source oracle confirms fixture bytes and both
   anomalous branches. Contract-root total serialization remains open.
   The release profile has
   `overflow-checks = true`, so u128 addition/subtraction failure is an
   abort whose prior writes must roll back. Views paginate over IDs and
   skip deleted records; `from_index + limit` has a u64 overflow boundary.
   The checked common pagination model proves fixed-window bounds, sparse
   lookup soundness and an overflow abort before the `min` truncation.
   Versioned-value conversion, concrete map reads and the remaining views
   are separate obligations.
   The pinned near-sdk macro treats an owned `self` receiver as a view, so
   `get_staking_contract(self)` does not write the root back or reject
   attached deposit. A checked wrapper projection proves read-only storage
   behavior, conditional on successful state decoding; a native fixture
   checks root bytes after direct owned-method invocation.
   `get_policy` has a separate version trap: `new` upgrades its input to
   Current, and `add_proposal` accepts only Current-valued `ChangePolicy`
   inputs. The execution branch stores its proposal's version unchanged.
   A test-only synthetic Default proposal bypasses creation validation and,
   when approved, makes later `get_policy` and `add_proposal` calls panic.
   Lean models both the gate and unchecked transition, and proves Current is
   preserved by successful traces of validated policy writes. A separate
   proposal-map invariant is preserved by validated creation, same-kind
   updates and non-vote removal in the checked projections. Shortcut policy
   mutations write Current, but they cannot execute once the next policy
   read hits Default. `migrate` copies the old policy handle without upgrading
   it. View totality needs a Current-policy precondition and a storage-history
   invariant covering old proposals and migration.
   Blob storage uses raw SHA-256 keys plus a `LookupMap` owner index. The
   checked one-slot projection proves the owner gate and the current-price
   refund formula. A byte-level proof separates 32-byte raw hashes from all
   constructor keys, fixed-width proposal/bounty/count keys and 33-byte blob
   owner keys. Delegation and bounty-claimer keys are also 32 bytes for a
   valid 27-byte account ID, so excluding those collisions needs a SHA-256
   image assumption or another guard. Full key separation, byte width and
   rollback remain open. In the conditional alias model, an occupied account
   key blocks raw blob insertion; if a blob occupies it first, a later
   delegation insert aborts on malformed old bytes or overwrites a decodable
   u128 payload while retaining the blob owner index. Subsequent blob removal
   deletes the delegation key. A native fixture checks this with a synthetic
   digest-shaped key, without claiming an actual SHA-256 preimage. The
   bounty-claimer alias similarly depends on decoding the old raw payload as
   a `Vec<BountyClaim>`: a valid empty vector is replaced by `bounty_claim`
   and later removed by `remove_blob`, leaving its count at one; malformed
   bytes abort after an earlier
   claim-count write, making host rollback essential. On a
   raw-key miss, NearVM leaves the evicted register holding the previously
   removed owner index value; `remove_blob` then refunds according
   to that stale value's length. A coherent raw/index layout must exclude
   this branch before any original-blob-length refund theorem. The checked
   `new` projection covers all initialized fields, Current-policy upgrade,
   enabled predecessor factory and V2 marker; a native pinned-source oracle
   checks the factory/version raw bytes. Root-state Borsh serialization now
   models all scalar fields and ordered action logs, with constructor and
   populated byte fixtures checked against a pinned-source oracle. General
   offset proofs account for the optional staking account's byte length.
   Separate Config and VersionedPolicy Borsh encoders now cover nested role
   and vote-policy values. Pinned-source fixtures check complete values and
   sorted HashSet/HashMap entries; width, nonzero-denominator and ordering
   conditions are explicit in Lean. A checked parser round-trips canonical
   bounded Config and versioned Policy values and rejects malformed tags,
   denominator zero and trailing bytes. Rust accepts noncanonical HashSet and
   HashMap vectors when strict-order decoding is disabled, then normalizes
   them; a later duplicate map key wins. Lean models that normalization and
   proves preservation of group matching, permission membership and all
   vote-policy lookups, but arbitrary-snapshot refinement remains open. A
   fresh-storage constructor trie composes direct `new` writes at Config,
   Policy, `FACTORY` and `STATEVERSION` with the wrapper's later `STATE` write.
   Checked proofs give exact values at those five keys, no other keys, empty
   collection namespaces 2–7, and bounded Config/Current-policy parsing.
   The native fixture checks direct `new` lacks a root, then checks the root
   after an explicit state write. A wrapper projection adds the SDK's deposit,
   argument-decode and root-existence guards, proving initialization is one-
   time with respect to `STATE`. The guard ignores other keys: with no root,
   direct `new` overwrites its auxiliary keys and preserves unrelated entries,
   as a native fixture confirms. Actual wrapper/Wasm execution, parser
   equivalence, rollback, general Borsh equivalence and arbitrary-state trie
   refinement remain open.
   `migrate` distinguishes V1 and V2 with a self-call guard supplied by the
   SDK. A wrapper projection adds the SDK private-caller and zero-deposit
   checks, omits the root-existence guard because of `ignore_state`, and
   models the later root write. It proves the V1 version-then-root write order
   and the V2 root-only path, conditional on supplied state encoding.
   The checked migration projection names all V1 fields and proves the V1
   copy plus empty action log and V2 version write; V2 returns current state
   without that write. The root layout proof shows V2 appends four zero bytes
   to a V1 root, and a native source fixture checks that conversion. The
   same fixture confirms a legacy Default policy value at the separate
   LazyOption key survives migration and makes `get_policy` panic. General
   wire compatibility, a Current-policy invariant, concrete wrapper
   refinement and rollback still need
   proof.

All claims above describe inspected source behavior or pending obligations,
not deployed-binary theorems. The factory-stored code hash is pinned, but
there is no identified deployed DAO instance for this entry.
