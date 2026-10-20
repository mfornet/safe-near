# Runtime verification work

This implementation is an executable prototype. Scenario success does not
establish equivalence with nearcore or correctness of deployed contracts.

## Reference and trusted inputs

The configuration exporter pins `near-parameters` and `near-primitives-core`
to crates.io version `0.37.4` in `tools/dump-runtime-config/Cargo.toml`.
The committed tables cover parameter changes through protocol 86. This is
a parameter-source pin. `reference.json` pins nearcore revision
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (release 2.13.4) for source
comparisons. The crates report that revision with `dirty=true`; their exact
published bytes are locked separately, and equivalence to the clean revision
is not assumed. `tools/runtime-conformance` now runs the pinned published VM
as an independent execution oracle. The initial gas discrepancies have been
fixed for the checked fixtures. General VM conformance remains unproved.
`tools/chain-conformance` also builds the clean source's full trie-backed
`Runtime::apply`. Its source, manifest overlay, lockfile, compiler and executable
are recorded and checked; the runtime implementation is not patched. Native
smoke checks establish deterministic raw-state replay and the transaction/
receipt chunk boundary. The Lean JSON frontend now executes explicit blocks
and serializes all represented state, queue and outcome fields; its wire format
and decoder assumptions are documented in `tools/chain-conformance/REPLAY.md`.
The cross-runtime bridge and complete observation comparison remain open.
Selecting
an older table does not select older execution semantics: the current Lean
configuration still omits most protocol feature switches. The loading-cost
fix is explicitly parsed and used. Historical replay is therefore
not a supported guarantee.

Signatures, consensus, initial state, block context, and receipt delivery are
externally supplied. Contract code enters as a decoded module, an independently
supplied size, and a hash label. Neither byte-to-module correspondence nor the
hash label is checked by the runtime. `codeOf` is an externally supplied decoder.
`ContractCode.decodeIssue` marks unavailable decoding explicitly. Calling or
deploying flagged code, including conversion of a deployment promise, rejects
the entire apply as a model issue with no committed state, outcomes or fees.
Replay adapters must use that flag instead of substituting an empty executable
module. Successful decoding still remains a trusted byte-to-module assumption
that must be carried into any theorem about deployed bytes.

## Chunk boundaries

Transaction acceptance charges the signer, updates its access-key nonce and
produces a transaction outcome. Only signer-is-receiver action receipts run
locally in that chunk. Other transaction receipts are outgoing work; their
receiver state changes when those receipts are delivered in a later chunk.
The routing follows `Runtime::process_transactions` in the pinned source.

An unsupported contract host operation is discovered when the function-call
receipt executes. A cross-account transaction can therefore be accepted in
one chunk before delivery encounters a model issue in a later chunk. The
issue rolls back the failing chunk; it does not erase already committed
transaction charges or nonce updates. Likewise, an implicit account's initial
key nonce uses the block that executes its transfer receipt, not the block
that accepted the originating transaction.

## Gas purchase and refund accounting

Receipt gas is purchased at `max(block price, min_gas_purchase_price)`.
Source-derived configuration also supplies the `AccountCostIncrease` feature,
account-creation charge and refund penalties omitted by the RPC view. Current
feature semantics distinguish purchase/burn prices, return price surplus,
charge successful account creation and pay contract rewards at the burn price.
Older feature settings retain the reference's purchase-price accounting.
System refunds report execution gas without charging gas tokens; failed system
refunds burn their deposit separately. Gas refunds identify the signer key and
restore its current function-call allowance on delivery, saturating at u128.

Forty targeted native/Lean cases compare all represented state, receipt and
outcome fields for successful transfers/account creation across protocols
83–86 and zero, increasing and decreasing prices. Creation-order renaming
relates native receipt hashes to model counters; transaction hashes remain
abstracted. Native metadata, compute and opaque trie/statistics fields are
retained as explicit observation gaps. This is a restricted financial regression,
not general runtime conformance. Runtime tests separately cover replaced/deleted
keys, failed refunds, allowance saturation and refund chunk-capacity usage.
The general comparison bridge, other actions/failures and bounded arithmetic
remain separate obligations.

## Current implementation and gaps

| Boundary | Implemented | Remaining obligations |
| --- | --- | --- |
| VM | Host context, storage, registers, logs, promises, gas counter, rollback on abort | Exact instrumentation and trie costs; host limits and error ordering; cryptographic semantics; module validation and decoding |
| Actions | Create, deploy, call, transfer, add/delete key, delete account; basic stake rejection checks | Reference validation; integer bounds; staking/epoch semantics; newer action variants |
| Receipts | Proved per-call graph conversion and acyclicity; input/output dependencies, postponement, failure data, refunds | Global state well-formedness/freshness; receipt-layer reference oracle; yield/resume lifecycle |
| Chain | Block application, delayed queue, explicit bounded-run completion, reachability restricted to supported applies | Scheduling assumptions; indirect interaction predicates; sufficient prepaid gas specification |
| wNEAR | Completed local model proofs; checked callback projection; refinement proposition with explicit resources and accounting | Binary refinement proof; callback parsing/serialization proofs; chain-level solvency and availability proofs |

Known unsafe approximations still requiring implementation changes:

- The functional host has injectable cryptographic defaults. The metered VM
  rejects cryptographic and validator operations instead of invoking those
  defaults. Concrete cryptographic and validator semantics remain to be supplied.
- The metered VM rejects yield/resume operations. Their receipt lifecycle is
  not implemented; the low-level promise conversion is not a yield executor.
- Unstaking is explicitly rejected as unsupported epoch semantics.
- Natural-number arithmetic does not by itself reproduce bounded protocol arithmetic.
- Scenario code supplies a synthetic deployed code size.
- Fuel exhaustion has a structured execution issue. `VMOutcome.issue?` separates
  model limitations from protocol outcomes. An issue makes `Near.apply` atomic:
  input state is preserved and no protocol outcomes, fees or refunds are emitted.
- Both execution loops are total. Receipt recursion decreases the postponed map
  length. Their surrounding well-formedness and transition properties remain open.

These are limitations, not accepted conformance exceptions. Until closed or
explicitly rejected by execution, affected runs cannot support NEAR claims.

## Completion gates

1. Pin a nearcore execution reference and define the supported protocol semantics.
2. Make execution total and expose incomplete and unsupported execution explicitly.
3. Preserve all observations needed for financial and asynchronous refinement.
4. Establish state/receipt well-formedness and close implementation discrepancies.
5. Compare Lean and nearcore on identical reproducible inputs, including failures,
   interleavings, boundary values, and protocol changes.
6. Prove reusable rollback, conservation, authorization, and dependency properties.
7. Prove deployed wNEAR refinement and end-to-end solvency and availability under
   explicit gas, scheduling, storage, and environment assumptions.
8. Run scenario, conformance, and axiom checks in CI for all affected packages.

## Validation commands

From the repository root:

```sh
just near-test
just runtime-adapter-test
just near-conformance
python3 tools/axiom-audit.py near-lean/vm --report /tmp/safe-near-vm-audit.json
python3 tools/axiom-audit.py near-lean/runtime --report /tmp/safe-near-runtime-audit.json
python3 tools/axiom-audit.py near-lean/chain --report /tmp/safe-near-chain-audit.json
```

The VM fuel loop is now structurally recursive. `runMetered_zero`,
`runMetered_done`, and `runMetered_trapped` expose its terminal equations to
kernel-checked proofs. They do not establish conformance, gas sufficiency,
or termination before fuel exhaustion.

`apply_issue_atomic` proves atomic rejection of model limitations.
`foreign_deploy_denied` proves the actor check rejects foreign deployment;
receipt execution tracks authority changes after account creation. This is not
yet a general authorization-preservation theorem.
`settle_completed_quiescent` and `runIsolated_completed_quiescent` prove that
reported completion leaves no receipt pending, delayed, or postponed.
`measureCallGasBurnt` returns a measurement only for successful, settled runs;
it does not claim to compute sufficient prepaid gas.

The wNEAR adapter uses real JSON escaping and parsing. It rejects unknown
receipt actions, invalid accounts and graphs not representable by its model.
The refinement proposition requires absence of model issues and valid successful
observations; neither is an exclusion hypothesis that can hide a failed run.
The binary-to-model refinement proof remains open.

The wNEAR model now proves balance and registration authorization across every
method. A callback can reduce only the receiver's balance, by at most the original
transfer amount, and cannot change registration. These proofs use only the three
standard Lean axioms. Their connection to deployed execution still requires the
binary refinement proof. The adapter passes actual balance and storage usage from
the enclosing action rather than inventing zero resources; the refinement states
local funding/bounds preconditions, exact successful accounting, and failure
rollback, including gas exhaustion. Chain solvency must establish those funding
preconditions.

The model also proves per-call conservation: the increase in total supply plus
registration liabilities is bounded by attached NEAR minus all outgoing promise
deposits. Refund resolution preserves registration, creates no NEAR transfers,
and can only decrease supply. Storage coverage bounds the encoded records by the
`STATE` record plus the measured per-account allocation. Encoder injectivity and `project (encode s) = some s` are now proved for every
well-formed state, including unregistered zero balances and bounded integers.
The bridge from these model theorems to runtime/chain solvency remains open.
`just wnear-audit` checks the entire verification package without an exemption
for unfinished proofs; the deployed refinement remains a proposition to prove.

The callback adapter now forwards exact raw result lists; the model view is a
separate total `U128` string projection with a proved output bound. Typed numeric
arguments carry a representability condition. Independent callback fixtures
compare malformed UTF-8, noncanonical/escaped JSON, integer overflow, missing and
extra results. Interleaving fixtures serialize receiver spending and account
unregistration before resolution. They test the VM seam, not scheduling or
transaction validation. A missing promise result now uses the structured
`invalidPromiseResultIndex` host error, matching the independent oracle.
The full deployed refinement also still needs treatment of input/log/temporary
storage limits and proofs connecting the projection to SDK serialization.

The public VM boundary now validates raw promise handles and emitted receipt
indices. `promisesValidFrom_iff` and `receiptsValidFrom_iff` connect executable
checks to creation-order predicates. `run_receipts_valid`,
`run_dependency_before`, `run_returnedReceipt_lt` and `run_no_receipt_cycle`
prove that every public VM result has backward-only dependencies, an existing
returned receipt and no dependency cycle. Invalid raw handles or converted
graphs become model issues with balance/storage/usage rollback; logs and burnt
gas remain diagnostic observations. These predicates concern dependency indices,
not full action/account validity or global identifier freshness. Accepted outputs
are checked regardless of the preservation proof. Join conversion is now related to explicit ordered graph
semantics by the proofs described below.
The join oracle covers ordinary, nested, duplicate and empty joins, illegal
joint returns/actions, nonexistent handles, view restrictions and low-gas error
precedence. It exposed and fixed joint promises incorrectly returning success,
panic-style index errors and action fees charged before invalid-handle checks.
The `promise_return` view guard retains its own host fee, as nearcore does.

The converter is now an incremental total `Option` computation in
`NearVM/PromiseGraph.lean`. `convertPromises_iff` relates it in both directions to
`ConvertsPromises`; `ExpandsDependencies` specifies ordered concatenation with
duplicates. `convertPromises_accepts_iff` proves exact agreement with the raw
handle well-formedness check, so no valid supported graph is rejected.
`convertPromises_valid` and `convertPromises_receipts_valid` establish graph
validity without invoking the output validator. Handle-count and returned-index
lemmas connect the handle table to receipt identities. These are proofs of the
Lean graph semantics, not a universal proof of equivalence with nearcore.
The old fuel-based converter and its silent invalid-return fallback are removed.
A nearcore regression also found that `value_return` after `promise_return` kept
the old promise selected; successful selectors now clear each other's state,
with kernel-checked overwrite lemmas and exact comparisons in both call orders.

`NearVM/HostPromises.lean` now proves raw dependency preservation for the 14
functional promise creation/action functions, the three promise result/return
functions, and `value_return`. The property includes returned, trapped and thrown
stores. `metered_preserves_promises` lifts any such host proof through pre/post
charges, deposit deductions and storage-usage updates. Post-call metering was
extracted into `finishMeteredCall` without changing its execution order or
behavior. Initialization has an empty well-formed graph, and
`HostPreservesPromises.convertible` connects successful host execution directly
to the proved converter and receipt-graph validity. Full state
well-formedness, action validity, integer bounds, global freshness and conservation
remain separate obligations.

`NearVM/HostDispatch.lean` now covers the complete metered host registry.
`meteredHostFns_preserves` includes deprecated and unsupported rejection paths,
structured panic handlers and the gas import. `resolveMetered_preserves` lifts
this invariant to every function in a successfully resolved environment.
`resolveMeteredImports_aligned` and `resolveMetered_length` prove positional
alignment and multiplicity for the structurally recursive import resolver.
These are dependency-preservation guarantees, not complete host semantic
conformance; the interpreter lifting is described below.

`NearVM/ExecutionPromises.lean` now proves dependency preservation for every
`SmallStep.Step`, finite `SmallStep.Steps` trace, and every `runMetered` exit,
including fuel/gas exhaustion and diagnostic errors. The invariant includes
all callable hosts in all module instances and foreign-function slots.
Indexed-memory selection changes only memory metadata, with a proved host-table
frame; GC execution, exception preparation and memory restoration have host-state
frames as well. Successful resolved initialization establishes the invariant.
`runResolved_promises_convertible` connects that initialization and actual
metered execution to a valid converted graph without using the output checker.
The initial promise list must be well formed (ordinary VM contexts start empty).
These proofs do not establish complete state well-formedness, account/action
validity, bounds, global freshness or conservation,
nor do they prove equivalence between interpreter steps and nearcore.

Returned-promise selection is now a separate preserved invariant in
`ReturnSelection.lean`: an optional selection names an existing non-joint raw
handle. Creation and action append preserve earlier selected slots;
`value_return` clears selection and `promise_return` checks existence and kind.
`HostSelection` and `MeteredSelection` cover the complete resolved registry,
including errors and unsupported rejection. `InterpreterInvariant` provides
one generic step/trace/initialization proof, and `MeteredInvariant` lifts it
through execution with an explicit gas-frame premise. Both the dependency and
selection proofs specialize these shared results.
`ReturnGraph` proves non-joint slots retain receipt identities through all
subsequent conversion, and bounds their returned receipt indices.
`runResolved_return_selection` in `ExecutionSelection.lean` combines resolved
initialization, metered execution, graph validity and return resolution.
`PromiseGraph.returnData?` is extracted from the existing VM return branch;
its totality is proved for convertible graphs with valid selection, including
exact value bytes when no promise is selected. Yielded raw handles remain
excluded by dependency well-formedness; this invariant does not implement yield.
Bounds/freshness, complete state validity, conservation and deployed refinement
remain open.

The metered join path now loads `max_number_input_data_dependencies` from the
protocol configuration and checks expanded prefixes before functional invocation.
Duplicate receipt indices count repeatedly; joins of empty joints can exceed
128 input handles while contributing zero dependencies. Earlier limit violations
precede later invalid handles. The u64 `count * 8` overflow check occurs after
base/promise-and-base charging and before per-element/memory charging. Memory
bounds errors use the structured host error. Independent boundary fixtures found
five mismatches, including overflow/error-message differences, now covered by
regressions. `joinedDependenciesError_none_iff`,
`joinedDependenciesError_expands` and `preInvokeError_join_bounds` prove the
prefix condition, ordered expansion and accepted-span/dependency bounds.
Both existing execution invariants cover the new pre-invocation error exits.
Other host limits remain separate obligations.

Promise allocation now checks `max_promises_per_function_call_action` for
`promise_create`, `promise_then`, `promise_and`, `promise_batch_create`, and
`promise_batch_then`. Empty joints consume handles even though they emit no
receipts. Receiver reads/UTF-8/V2 syntax and callback-handle errors precede the
capacity error. Receipt dispatch fees are paid before that error; subsequent
function-action argument reads, the second base fee, action fees and prepaid
gas are omitted. Successful combined create/then calls retain both base fees.
Their view errors name the underlying batch operation, matching the reference.
The context installs V2 account syntax validation (legacy rules retain their
unvalidated behavior); structured creation-prefix errors preserve gas ordering.
The count regression fixture covers capacity, invalid receiver/handle/method
precedence, ordinary combined calls, view restrictions and account boundaries.
`promiseCapacityError_none_iff`, `preInvokeError_count_bound`, and
`checked_nextPromiseIdx_fresh` establish capacity and local raw-handle freshness
under a u64-sized limit. Global identifier freshness, complete state validity,
remaining host limits and deployed refinement are still open.

Even zero-length join spans validate their pointer before capacity checks.
The additional empty-span regressions exposed two discrepancies;
`preInvokeError_join_span_bound` now proves the entire accepted pointer/length
span lies within guest memory, while the existing join proof bounds its u64
length and expanded dependency vector.

`functionCallPlan` now validates and charges function-call inputs in reference
order: u128 amount, method bytes/nonemptiness, argument bytes, then target
receipt/joint distinction. Invalid input stops the charge list before later
reads, fees or gas prepayment. Direct batch actions and combined create/then
calls share the plan; creation-prefix and capacity errors still precede it.
Missing-register memory-or-register reads fail before any register-read charge.
The new fixture exposed 15 mismatching cases, including overlapping errors and
an empty method that must fail before action-fee gas exhaustion.
`FunctionCallValidation` proves successful plans admit exact readable inputs,
nonempty methods, receipt targets, and matching functional action construction;
it also connects pre-invocation acceptance to that action result.
One-yocto sponsorship is enabled from the pinned v85 configuration. Eligible
function-call deposits of exactly one yocto at zero liquid balance increment
`VMOutcome.subsidizedAmount`; transfers and larger deposits remain unfunded.
Failed VM calls retain attempted subsidy diagnostics, matching the VM reference.
Receipt execution commits subsidy only on success and clears it on any later
action or storage-staking failure. Apply results aggregate committed subsidy
separately from gas burn, and model issues commit zero subsidy (kernel proved).
The 770-byte storage-staking exemption follows pinned nearcore's verifier.
The local deposit accounting equation is kernel proved; a full chain conservation
theorem incorporating minted grants and deployed wNEAR refinement remain open.

## Purchased gas and token settlement

Transaction conversion now buys receipt gas at `max(block price, minimum purchase
price)` and carries that price through promises. The pinned v85+ rule burns gas at
`min(purchase price, block price)`, refunds the burnt-price surplus, and subtracts
bounded refund penalties and account-creation charges. Prior configuration behavior
retains the price surplus in burnt tokens. Function-call rewards use the correct
burn/purchase price for each rule. Failed system refunds burn their transfer funds
in apply statistics while their execution outcome still reports zero gas/tokens.

`Fees.settleGas_conservation` proves the v85+ partition of purchased gas into
refunds, burnt tokens and gas reserved for onward execution, including general
bounded penalties and creation charges. It assumes `burnt ≤ used ≤ prepaid`;
receipt/VM execution must still establish these budget premises compositionally.
`Fees.receiptFunds` and `Snapshot.totalFunds` count deposits and purchased gas in
pending, delayed and postponed receipts. Whole-chain conservation is still open.

`tools/runtime-finance-reference` compares transaction costs and actual private
refund routines from the clean pinned nearcore implementation through an appended
adapter module. Its 72 exact comparisons cover v84/85/86 financial parameters,
price changes and account creation. It is not a full receipt execution oracle.

## Finite-map and transaction invariants

`StateInvariants` defines `AccountsUnique` and `MapsUnique` for the association-list
key domains. It proves insert/erase lookup frames, uniqueness preservation by the
state update primitives, and exact account balance changes for insertion,
replacement and removal. These predicates do not establish numeric bounds,
receipt consistency or global identifier freshness.

`TransactionInvariants` connects the actual successful `convertTransaction`
execution to its validated commit. Kernel-checked theorems establish exact account
debit, conservation of account funds plus the newly backed receipt and conversion
gas burn, preservation of all map-key domains, unrelated-account isolation, and
the receipt counter's exact increment. Conservation assumes unique account keys
and excludes the reserved system signer, whose receipts use free-refund semantics.
`AccessKeyInvariants` proves successful conversion installs the authorized key,
sets its nonce, respects restricted receiver/method/zero-deposit constraints,
checks the allowance and deducts exactly the transaction cost from finite
allowances. Signatures remain trusted; these are properties of the implemented
conversion, not a proof of equivalence with nearcore transaction admission.

The transaction interface models monotonic and strict regular-key nonces.
`verifyNonce` follows the pinned validator's checked strict increment, saturating
u64 height ceiling and error precedence; Apply always supplies its block height.
The default apply context starts at height one. Explicit height zero rejects every
nonce, matching the reference. Strict requests require the generated v85+ gate.
`NonceInvariants` proves exact acceptance, increasing nonces and the ceiling/u64
bounds; `convertTransaction_nonce_bounds` connects those properties to successful
conversion while retaining the earlier conservation and authorization proofs.
`tools/runtime-nonce-reference` compares 126 cases to the actual private validator
and feature table. Native v1 decoding, gas-key nonce slots, pending-mempool overlays,
remaining admission bounds/error ordering, gas-refund allowance restoration,
whole-receipt state-invariant preservation and global conservation remain open.

`NearChain.step_applyResult` exposes the exact apply result for compositional
proofs, and `Reachable.firstStep` proves first-step reachability generically.
The chain scenario uses this universal proof rather than elaborating a redundant
concrete execution witness inside its IO program; runtime checks are unchanged.
