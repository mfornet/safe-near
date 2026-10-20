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
