# Full-runtime reference side

This adapter executes the **regular trie-backed nearcore `Runtime::apply`**,
not `near_vm_runner` with mocked storage. It is the reference side of the
transaction/receipt differential harness. The
[Lean JSON replay frontend](REPLAY.md) executes complete represented state
and explicit block schedules. A targeted financial bridge is available below;
general cross-runtime comparison remains incomplete. Component checks do not establish general
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
nearcore hashes, complete observation comparison, and broader action/failure coverage.
[Captured-account import](SNAPSHOTS.md) now prepares matching queue-free initial
state for both executors; it does not establish general execution equivalence.
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

## Contract/data comparison

`just chain-compare FIXTURE` compares an imported fixture against both executors.
The contract corpus exercises actual callback data and postponed/delayed queues;
see [SNAPSHOTS.md](SNAPSHOTS.md#compare-contract-executions) for commands, id
renaming, failure mapping and the remaining storage-trie gas gap. Receipt VM
calls charge `storage_write_evicted_byte` and `storage_remove_ret_value_byte`
from the actual old value before attempting the output register. The storage
mutation regressions retain their mismatches; their gas delta must equal only
native `touching_trie_node` and `read_cached_trie_node` charges. No trie fees are
inferred from observed native output or subtracted from comparison results. Native traces
now include `processedReceipts`, typed `balanceStats`, and
`nextCongestionInfo` for explicit subsequent chunk inputs. Callback index columns
are decoded with native types and validated by exact `TrieKey` re-encoding;
complete raw trie/statistics bytes remain available. Delayed receipt records
include their native `queueIndex`, so Borsh key byte ordering cannot reorder the
logical queue.

`just chain-action-test` compares 64 administrative-action scenarios across
protocols 83–86, including registrar restrictions, multi-action rollback,
missing methods/code, final storage failures and key nonce initialization.
Mapped failures preserve semantic parameters and action indices; unsupported
error variants fail closed. Raw diagnostic formatting remains in evidence.

`just chain-permission-test` compares restricted-key success, atomic rejection
and native failure precedence in 72 scenarios across protocols 83–86. Missing
keys, receiver/method mismatches and insufficient allowances preserve every
native semantic parameter, including the actual transaction cost.

`just chain-validation-test` compares stateless action admission and binds
actual deployment bytes to signed native transactions. Native RPC views mask
deployment payloads as hashes, so the bridge uses separately exported typed
actions decoded from canonical Borsh, retaining the RPC view for provenance.

`just chain-staking-test` checks 2,355 key classifications and 68 native apply
scenarios. Staking admission now checks Edwards decompression and prime-order
subgroup membership; epoch-dependent staking execution remains unsupported.

## Canonical trie and cache diagnostics

`just chain-trie-test` compares native `near_store::Trie` traversal with
`NearRuntime.TrieAccounting`. Build the source oracle first, as above. For an
individual request:

```sh
just chain-trie-compare tools/chain-conformance/fixtures/trie_lookups.json
```

The native `--trie-lookups` mode builds a canonical on-disk trie from unique raw
key/value `entries`. Each `lookups` row requires raw-byte `key`, Boolean
`accountNodes`, `dereference`, and `resetCache`. `accountNodes` selects the native
counted (`MemOrTrie`) or uncounted (`MemOrFlatOrTrie`, without a flat store) node
lookup path. Value dereferences always use the accounting cache. The cache is
shared by node and value hashes and persists until explicitly reset.

The output retains the canonical root, complete Borsh object set and actual
ordered native node/value accesses, including fresh/cached classifications.
After recording the requested accesses, the oracle enumerates the remaining
objects without changing the query cache. The driver independently checks
witness SHA256 bindings. Lean receives only the original raw entries and queries:
it constructs the canonical compressed hexary trie, Borsh node encodings,
subtree-size fields and pure SHA256 identities, then interprets its own nodes
and derives the cache events/counts. Root hashes, every node/value object's
bytes and all observations must match. Object-set order is immaterial; access
order is preserved. Native roots, witnesses, paths and counts never enter the
constructor.

The separate witness-input mode also checks object bindings with pure Lean
SHA256 before decoding all four node variants and following compact paths and
branch bitmaps. Missing objects, malformed/trailing node bytes, cycles, invalid
byte/hash widths, inconsistent value lengths and duplicate hashes fail closed.
The native reference, Lean executable, inputs, outputs and differences are
retained with build identities; execution errors remain mismatches with native
evidence retained.

The regression includes prefix keys, empty values, all sixteen branch slots,
misses, repeated reads, shared subtrees/values, cache resets, uncounted node reads,
and a value whose bytes are also a trie node. Seven complete states exported by
real `Runtime::apply` rebuild the same native canonical roots and match Lean's
lookups. The counter/event increment lemmas and SHA256 output width are kernel-checked.
SHA256 is independently compared to hashlib on padding boundaries and multiblock
vectors, including the million-byte standard vector; full cryptographic refinement
and general constructor canonicality are not proved.

This diagnostic does **not** supply receipt gas totals or close the remaining
runtime gas gap. Encoding modeled runtime records into raw entries, updates/prospective overlays,
receipt-wide cache lifetime, flat storage and memtries still need integration.
The complete object set is for the trie built from the supplied entries; it does
not establish that all state of an original blockchain was captured.
