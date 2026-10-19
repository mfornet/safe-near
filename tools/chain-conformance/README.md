# Full-runtime reference side

This adapter executes the **regular trie-backed nearcore `Runtime::apply`**,
not `near_vm_runner` with mocked storage. It is the reference side of the
transaction/receipt differential harness. The
[Lean JSON replay frontend](REPLAY.md) executes complete represented state and explicit block schedules. The cross-runtime bridge and comparison
still need connecting; passing either component's checks does not establish
Lean/nearcore equivalence.
The `Chain reference smoke` workflow builds and exercises this source oracle
on Linux; it uploads the raw trace and build metadata separately from the
existing VM comparison evidence.

## Build and exercise

From the repository root:

```sh
just chain-reference-build
just chain-reference-test
```

The first build downloads the clean source revision from
[`near-lean/runtime/reference.json`](../../near-lean/runtime/reference.json),
uses its pinned Rust toolchain and Cargo lockfile, and compiles RocksDB and
the VM dependencies. Sources and build outputs are cached under ignored
directories. To reuse an existing **clean checkout at exactly that revision**:

```sh
python3 tools/chain-conformance/prepare.py --source /path/to/nearcore
```

`--check` type-checks the adapter without publishing an executable. The default
binary is `tools/chain-conformance/target/near-apply-reference`; its adjacent
`.build.json` records source, lockfile, adapter, compiler and executable hashes.

The build adds one temporary binary target to the upstream Cargo manifest
and copies the adapter into that package. All implementation sources remain
unchanged. The builder rejects unrelated tracked/untracked modifications,
serializes builds with a kernel lock, verifies the exact overlay after
compilation, and restores the checkout afterward. It can recover an interrupted
overlay only when its ownership record and every owned byte still match.

Features are `test_features` for the in-memory store fixtures, `estimator` for
the public primitive fixture helpers, and `near-crypto/rand` for deterministic
example signing keys. The adapter calls `Runtime::apply`, not the estimator
execution shortcut. It uses the real parameter store without free-gas or fee
overrides. The source's architecture-dependent VM selection is retained and
reported: Wasmtime on this ARM host, NearVM where the pinned source selects it.

The smoke runner freezes the executable before running scenarios and records
the complete request and native trace in `audit/chain-reference-smoke.json`.
It checks transaction/receipt timing, idle blocks, deterministic full traces,
replay from an exported raw trie and pending queue, invalid schedule atomicity,
and rejection of malformed transaction Borsh.

## Raw replay interface

```sh
tools/chain-conformance/target/near-apply-reference --metadata
tools/chain-conformance/target/near-apply-reference --example > /tmp/apply-request.json
tools/chain-conformance/target/near-apply-reference < /tmp/apply-request.json > /tmp/apply-result.json
```

The generated example contains signed transactions using a deterministic test
key. It supplies all external block inputs explicitly. Borsh byte arrays use
the pinned upstream types, preserving transaction versions, receipt variants,
access keys and contract bytes without flattening them through a custom action
schema.

Request fields:

| Field | Encoding |
| --- | --- |
| `formatVersion` | `1` |
| `protocolVersion` | A version supported by the pinned runtime, currently 83–86 |
| `initialEntries` | Array of `[raw trie key bytes, raw trie value bytes]`; duplicate keys fail |
| `pendingReceipts` | Array of Borsh-encoded upstream `Receipt` byte arrays |
| `blocks` | Explicit sequence of block objects below |

Each block supplies:

| Field | Encoding |
| --- | --- |
| `blockHeight`, `blockTimestamp`, `epochHeight` | Unsigned 64-bit integers |
| `gasPrice` | Unsigned 128-bit decimal string |
| `gasLimit` | Unsigned 64-bit gas limit, or `null` |
| `randomSeed`, `prevBlockHash` | Exactly 32 bytes each |
| `congestionInfo` | Array of `[shard id, Borsh CongestionInfo bytes, missed chunk count]` |
| `bandwidthRequests` | Borsh encoding of `BTreeMap<ShardId, BandwidthRequests>` |
| `transactions` | Array of Borsh `SignedTransaction` byte arrays |
| `incomingIndices` | `null` for all pending receipts, `[]` to defer all, or ordered queue positions |

Receipt positions are relative to the pending queue at the start of that block.
Missing/repeated positions reject the block before applying transactions.
Deferred receipts precede newly outgoing work. A runtime error stops the
sequence without committing that block's trie changes. A malformed request or
Borsh payload fails the process rather than returning an empty success trace.

The trace also exposes `initialPendingReceiptViews`. Each attempted apply
has `inputs.transactions` rows containing the native transaction `version`,
canonical `borsh` bytes and upstream `SignedTransactionView`, plus
`inputs.incomingReceipts` in actual delivery order. Runtime-error attempts
retain these inputs; a rejected schedule stops before decoding transactions.
These projections prepare the Lean bridge without introducing another Borsh
decoder. Views are not lossless replacements for the authoritative raw bytes.

Every committed block exports its complete raw trie, root, outcomes, outgoing
and pending receipts, state changes, stats, validator proposals, congestion
and bandwidth outputs. Protocol structs without a JSON view remain available
as Borsh bytes. Outcome views are accompanied by complete outcome Borsh and
the separate compute counter that upstream Borsh omits.

`decodedRecords` is a readable projection. Unknown shard columns remain marked
`opaque`, and **every key/value is still present in `state.entries`**. The
projection does not remove bandwidth-scheduler or queue state from replay.

## Scope of the external environment

The current epoch fixture has one shard and no validators. Epoch id is fixed;
validator-account updates and sandbox state patches are empty. Transactions
are supplied as valid-period inputs; the regular runtime still performs its
own protocol transaction checks. This is a trusted apply harness, without
consensus, networking or historical chain replay.

The independent full-runtime oracle now exists. Remaining work includes the
cross-runtime bridge, explicit treatment of abstract counter ids versus
nearcore hashes, complete observation comparison, and captured-account import.
The existing `just near-conformance` remains a VM-level comparison.

## Targeted financial comparison

After building both executables, run `just chain-gas-test`. Forty native/Lean
cases cover successful transfers and account creation across protocols 83–86,
zero and nonzero prices, and price increases/decreases between submission and
delivery. Source-signed requests come from `--financial-examples`. The runner
freezes both executables and configuration tables, checks native provenance,
and saves raw requests/traces plus field differences in
`audit/transfer-gas-regression.json`.

It compares every represented state/receipt/outcome field for this restricted
corpus, including ordered pending work and model counters. Native receipt
hashes are renamed by independently observed creation order; transaction hashes
map to the model's zero transaction outcome id. Association-list map order is
canonicalized, while receipt order is preserved. Native metadata, compute,
account representation versions, opaque trie columns and statistics outside
derived token burn remain explicit observation gaps. This targeted regression
is not a general runtime comparator or a proof of conformance. Other action
kinds, initial contract/data state and failures are rejected rather than dropped.

The CI financial job consumes the exact binary/metadata artifact produced by
the native job, so it does not repeat the expensive source build.
