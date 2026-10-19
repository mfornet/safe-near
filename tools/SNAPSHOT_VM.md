# VM scenarios from captured accounts

`snapshot_vm.py` imports a complete account captured by `near_snapshot.py`,
then sends identical VM requests to reference and model executables. It is a
bridge from real deployed code and storage to the independent conformance
runner. It executes hypothetical calls, not a recorded on-chain transaction.

```sh
just snapshot /tmp/lockup.json lockup.near
just snapshot-vm /tmp/lockup.json lockup.near tools/examples/lockup_snapshot_calls.json \
  --reference /path/to/near-runtime-reference \
  --model /path/to/vm-replay \
  --config-dir /path/to/near-lean/vm/configs \
  --reference-manifest /path/to/near-lean/runtime/reference.json \
  --report /tmp/lockup-comparison.json
```

The executables must already be built and implement the JSON VM request and
normalized-output contract used by the conformance runner. The adapter never
builds or changes them. It requires `wasm-tools 1.251.0` to decode the captured
Wasm into WAT. The default executable/configuration paths match the repository's
VM conformance components; the flags also support separate worktrees.

## Imported and supplied inputs

The snapshot supplies the selected account ID, deployed bytes, liquid and
locked balances, actual storage usage, all raw storage keys/values, effective
protocol version, block height, and nanosecond timestamp. Code hashes are
checked again before execution. Incomplete prefix-filtered storage is rejected;
missing keys outside a prefix must never be interpreted as absent.

The scenario supplies `epochHeight`, a 32-byte `randomSeed`, and `calls`.
Those values are explicit trusted context. A block's `random_value` is not
silently substituted for a receipt-specific VM seed, and an epoch ID is not
treated as an epoch height. The example deliberately chooses epoch height zero
and an all-zero seed for getters that do not consult them. It does not claim
those were the inputs of a historical receipt.

Every call names `name`, `method`, `signer`, `predecessor`, `signerPublicKey`,
`gas`, and `view`. `signerPublicKey` is serialized bytes: an ed25519 key is
tag 0 followed by 32 bytes, a secp256k1 key is tag 1 followed by 64 bytes.
There are no signing keys and no transactions are submitted.

Supply exactly one of `args` (JSON, encoded as deterministic compact UTF-8) or
`input` (raw byte list). Optional fields are `deposit` (decimal string, default
`"0"`), `promiseResults` (byte lists or null for failed promises), and
`outputDataReceivers` (account IDs). Unknown scenario/call fields are rejected.

The snapshot is post-state at the captured block. All calls in a scenario use
that block context. Outgoing receipts are observed but not applied, and
account keys are not used to authenticate the supplied caller context. These
are trusted VM scenarios, not chain or transaction authorization tests.

## Exact comparisons and evidence

Every returned JSON field is compared, including gas profiles, errors, storage,
logs, and receipt observations. No tolerances or difference allowlists apply.
After a case, the reference's state seeds **both** executors' next case, even
when the model disagreed. An executor crash or malformed reference state stops
the scenario and marks remaining calls as unrun. An ordinary protocol failure
is compared as an outcome and does not itself stop the scenario.

Executables and configuration JSON files are copied to a private temporary
directory before running, so concurrent rebuilds do not change the scenario's
inputs. The report includes executable and input digests, all exact requests
and outputs, differing paths, generated WAT, and the complete frozen
configuration files. `--reference-manifest` adds the reference's source pins.
The temporary directory is removed after the run; its files can be recovered
from the snapshot and report when reproducing a request.

Reports are published atomically and never overwrite an existing file.
Exit codes: 0 means every comparison matched; 1 means differences or unrun
cases; 2 means invalid inputs or setup failure. The default per-executor
timeout is 120 seconds and can be changed with `--timeout`.

A live test seeded from `lockup.near` at height 220701709, block hash
`GXdjU1zVDi5HJNh2YmnTEWiqGPZA2b4iegU28kVvXhpn`, passed exact comparisons
for `get_foundation_account_id`, `get_lockup_master_account_id`, and
`get_min_attached_balance`. This demonstrates those scenarios only; it does
not establish general VM conformance or transaction/receipt equivalence.
