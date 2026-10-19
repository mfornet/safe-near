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
epoch transitions, or historical replay.

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
