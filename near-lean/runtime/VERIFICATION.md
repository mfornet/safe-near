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
Selecting
an older table does not select older execution semantics: the current Lean
configuration still omits most protocol feature switches. The loading-cost
fix is explicitly parsed and used. Historical replay is therefore
not a supported guarantee.

Signatures, consensus, initial state, block context, and receipt delivery are
externally supplied. Contract code enters as a decoded module, an independently
supplied size, and a hash label. Neither byte-to-module correspondence nor the
hash label is checked by the runtime. `codeOf` is an externally supplied decoder.
These assumptions must be carried into any theorem about deployed bytes.

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
not full action/account validity or global identifier freshness. Preservation of
raw handle validity by every host operation remains open; accepted outputs are
checked regardless. Join conversion is now related to explicit ordered graph
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
