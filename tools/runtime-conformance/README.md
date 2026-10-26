# Independent VM conformance

`just near-conformance` builds and runs two independent executors on identical
requests: `near-vm-runner =0.37.4` with its Wasmtime backend, and Lean's
`NearVM.run`. Rust dependencies are locked in `Cargo.lock`; `reference.json`
under `near-lean/runtime` records the source and crate pins.

Requirements: the project's Lean toolchain, Rust 1.93.1, Python 3, and
`wasm-tools 1.251.0`.

The fixture pins the deployed Wasm by SHA256. The driver prints fresh WAT from
that binary and passes its real byte size to Lean. Both executors receive the
same initial context, storage and callback results. Each next case receives
the reference's prior storage and balance, ensuring identical inputs even after
a discrepancy. Fixtures can start from imported storage byte pairs and a chosen
`initialStorageUsage`.

The comparison is exact for the normalized outputs: balance, storage usage,
return bytes and returned receipt index, gas burnt and used, ordered logs,
storage bytes, receipt actions and dependencies, failure text, model issues,
and subsidized amount. No tolerance, field exclusion, or expected-difference
allowlist is used. Unknown reference actions fail normalization.

The normalization includes receipt-level rollback of VM storage, balances and
new receipts on contract failure, matching the seam exposed by `NearVM.run`.
It preserves gas and logs. This wrapper does not execute transactions or
schedule receipts. `MockedExternal` supplies map storage, not a real trie, so
this is not evidence for trie costs, transaction fees, refunds, scheduling,
epoch transitions, or historical replay. It also omits the old-value byte
charges issued by native `RuntimeExt`. `NearRuntime.functionCallContext` enables
those charges for receipt execution; `VMContext.chargeStorageValueAccess`
defaults to false for this mock-adapter seam.

`storage_inputs_v83` through `storage_inputs_v86` add 41 exact comparisons of
key/value read errors, length checks, discarded old-value registers and missing
keys. They include key-limit precedence over an invalid value pointer and an
actual 4 MiB value-limit violation. Argument validation retains only the charges
incurred before its native failure point.

```sh
python3 tools/runtime-conformance/compare.py
python3 tools/runtime-conformance/compare.py --no-build --report /tmp/comparison.json
```

The command exits nonzero for any discrepancy. The report retains every exact
request and both outputs, differing field paths, binary digest, reference pin,
and the complete generated WAT. The recorded temporary WAT path can be restored
from that content when replaying a single request against either executable.
CI runs the same strict comparison and uploads the evidence even on failure.

The initial run exposed gas discrepancies across all tested successful wNEAR
methods, error-rendering discrepancies, and incorrect gas charging on method
resolution failure. Matching functional fields alone does not establish VM
conformance. Those observed discrepancies have been fixed for these fixtures;
the comparison remains strict. Extend it to more contracts, boundary cases
and protocol versions before making broader conformance claims.

`wnear_callbacks.json` preserves exact raw callback bytes (including malformed
UTF-8, escaped numbers, overflow, missing results and additional result slots).
It caught an invalid-result-index host error that was incorrectly reported as a
contract panic; the regression compares its exact error and gas. The
`wnear_interleavings.json` fixture executes calls where a receiver spends or a
sender/receiver unregisters before refund resolution. These are controlled VM
call sequences on shared storage, not an independent receipt scheduler oracle.

`global_contract.json` (v86) and `global_contract_v78.json` (the first version
with `global_contract_host_fns`) compare `promise_batch_action_use_global_contract`
and its `_by_account_id` variant: both identifiers, malformed hashes,
out-of-bounds reads, invalid, over-long and non-UTF-8 account ids (accepted at
v78, rejected by v86's account id rules), invalid promise indices, view calls,
rollback on panic and fee exhaustion. The fees come from nearcore's `77.yaml`
(the config view omits them); these comparisons confirm them exactly.
`global_contract_v73.json` checks that before v78 nearcore does not link these
hosts: importing one fails with "unknown or invalid import" after the loading
charge, even when the method does not exist.

`value_return.json` returns values below, at and one byte over
`max_length_returned_data`, and from out-of-bounds memory, with and without
output data receivers: nearcore reads and checks the length before burning
the data receipt bytes. A case may set `outputDataReceivers`.

Outcomes carry each receipt's `yieldDataId` and the successful
`promise_yield_resume` payloads (`resumes`); the executor reads both from the
mocked external. No fixture creates a yield yet: the mock's data ids are not
the ones the model derives, so a yield case needs those ids normalized first.

`logs.json` drives `log_utf8` and `log_utf16` into the number-of-logs limit,
the per-message and running-total length limits, bad UTF-8 and UTF-16,
out-of-bounds reads, a non-ASCII UTF-16 message and gas exhaustion mid-loop.

`prepare_*.json` (written by `gen_prepare_limits.py`, which keeps the large
modules out of WAT) checks nearcore's `prepare_v3` limits at and one over
each protocol-86 limit (types, functions including imported ones, function
body size, tables, table elements, locals) and the rejected imports (another
module, globals, tables, memory): a no-op outcome with `PrepareError` and no
gas. A module at the locals limit is left out: Wasmtime fails to compile it.

`promise_graphs.json` checks exact ordered receipt dependencies and returned
receipt identity for ordinary, nested, duplicate and empty joins. Failure cases
cover joint return/action restrictions, nonexistent handles, view calls and
invalid-handle errors that precede later action-fee gas exhaustion. Its WAT and
binary are pinned together; replay still regenerates WAT from the binary.

The promise-graph fixture also covers both orders of `value_return` and
`promise_return`. It exposed a stale receipt selection after a later value
return; the host now gives the last successful selection precedence. The same
fixture validates the incremental converter against the reference after removal
of the bounded join walk.

Join boundary cases check 128 versus 129 expanded dependencies, nested joint
expansion, duplicate counting, more than 128 empty input joints, invalid-index
ordering, u64 count-to-byte overflow, out-of-bounds index reads, and view
precedence. They exposed five discrepancies before the metered join limit and
overflow checks were added. Comparisons include exact error text and gas profiles.

`promise_counts.json` exercises the 1,024-handle boundary with empty joints and
all five supported allocating operations. It compares receipt-fee charging and
errors when receiver parsing or callback lookup fails before capacity, and when
function-call argument failure would occur after capacity. Ordinary combined
create/then calls and view errors cover their nested host calls; account cases
cover V2 syntax, UTF-8, and the 2/64-byte endpoints. The initial cases exposed
12 discrepancies before count enforcement and charge/validation ordering fixes.

Empty join spans with an invalid pointer are rejected before capacity, including
at the handle limit. These cases found two further mismatches and guard against
bypassing memory bounds when the index count is zero.

`function_call_inputs.json` compares direct and combined function-call action
validation: amount/method/argument memory failures, register failures, empty
methods, invalid and joint handles, and overlapping errors. Success cases cover
memory and register inputs; a low-gas case checks empty-method precedence over
later action-fee exhaustion, and a view case checks restrictions before reads.
The initial fixture found 15 mismatching cases. Comparisons retain exact bytes,
error text, fee profiles and prepaid/used/burnt gas.

`sponsorship*.json` checks the v84/v85 protocol boundary and v86 accounting:
paid, zero, repeated and combined function-call deposits, ineligible transfers,
invalid methods, view restrictions, and attempted grants retained after panic or
later balance failure. VM subsidy is diagnostic; receipt-level rollback and
committed minting are covered by runtime scenarios rather than this VM oracle.
The initial sponsorship comparisons also exposed a missing period in the
`BalanceExceeded` error text; the Lean text now matches the reference exactly.

`stake_promises.json` and `stake_promises_zero.json` compare stake-action scheduling
at positive and zero liquid balance. They cover zero/one/over-balance/max-u128
amounts, another receiver, repeated stakes, panic rollback and a preceding
transfer. These 16 cases exposed 12 differences: Lean incorrectly deducted the
stake target as an outgoing deposit and could fabricate balance-exceeded errors.
Scheduling now preserves liquid balance while retaining the exact gas charges.
This verifies VM promise construction; runtime staking execution still requires
unsupported epoch machinery and reports an explicit model issue.

`implicit_transfers_v69.json`, `implicit_transfers_v70.json` and
`implicit_transfers_v86.json` cover 60 transfer-scheduling cases across the ETH
implicit-account feature boundary. They compare named, NEAR implicit, ETH and
deterministic addresses, hexadecimal lookalikes, zero/repeated transfers, panic
rollback, invalid handles, amount-pointer failures, one-Tgas budgets and views.
The first 30 cases exposed 17 implicit-address fee discrepancies. Expanded cases
then exposed nine amount-read charging/error-precedence discrepancies. The
strict comparison retains exact gas and error observations for every case.
These VM fixtures schedule transfers; runtime scenario checks separately cover
existing ETH/deterministic receivers and explicit unsupported creation rollback.

`key_methods.json` covers eight function-call-key scheduling cases: unrestricted
methods, one/two/three names, UTF-8 names, positive and maximum allowances, and a
tight gas budget. The initial five cases exposed zero allowance being emitted as
finite zero and comma separators being double-counted in gas. The comparison
checks the complete emitted access-key permission as well as burnt/used gas.
`key_input_errors.json` adds 44 exact comparisons for malformed method lists,
invalid receiver IDs and UTF-8, memory/register reads, promise targets, serialized
public keys, view restrictions, and gas exhaustion at validation boundaries.
The model follows the observed read/validation order, including charging action
fees before reporting an invalid serialized public key. Empty method lists are
unrestricted; empty comma-separated entries are rejected.

The pinned VM oracle uses MockedExternal, which enables post-quantum keys.
These tests do not establish historical runtime feature gating. The method-encoding
fixtures below separately exercise runtime-style UTF-8 external validation.


`method_encoding.json` adds 38 method-encoding cases; the initial probe exposed
11 discrepancies. `method_encoding_zero.json` adds five zero-balance cases,
including one-yocto subsidy/error ordering. These fixtures compare invalid UTF-8,
Unicode/NUL methods, register inputs, function-call creation/callbacks, access-key
CSV methods, earlier failures and exact logs/gas/rollback.

The request field `validateActionMethodUtf8` defaults to false in both replay
adapters, matching nearcore's `MockedExternal`. Strict cases use a native
`MethodValidatingExternal` adapter which delegates the entire external interface
to that mock, except for the ordinary function-call and function-call-key UTF-8
checks from the pinned `runtime/runtime/src/receipt_manager.rs`. Native VMLogic
still controls fees, prepayment, balance deductions and error precedence. This
adapter tests that external seam; it is not a trie-backed/full Runtime oracle.
Actual Lean receipt execution always uses strict validation, as does a default
public `VMContext`. Opaque VM outputs must not be treated as validated runtime
actions.

`host_gates_v84.json` and `host_gates_v86.json` import `chain_id`, `p256_verify` and a gas key
host, which nearcore links only from protocol 85: at v84 every call fails to link (only the
loading gas burnt), at v86 the module links. The v86 `chain_id` result itself is not compared:
the mocked external reports a chain id the Lean replay is not given.
