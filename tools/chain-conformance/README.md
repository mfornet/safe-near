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

`just chain-state-encoding-test` compares `NearRuntime.StateEncoding.encode` on
actual typed `ChainState` records with native `--encode-state`. It checks account
V1 Borsh bytes, ordinary Ed25519/secp256k1 access keys, finite/unlimited
function-call permissions, raw contract code and binary contract storage. Native
permission receivers are strings; they may contain values invalid as account IDs.
The Lean `state-encode` executable accepts `{formatVersion: 1, codes, initialState}`
using the same catalogue and state transport as `chain-replay`. It returns
`initialEntries`, `root` and the complete `witness`, constructed independently.
Native encoded state, roots and objects never enter the Lean request.

Catalogue bytes must match the canonical base58 SHA256 code hash and model size;
arbitrary replay labels cannot be used for trie encoding. Wasm byte-to-WAT
correspondence still depends on the external decoder. Duplicate records, missing
owners, invalid account IDs, unsupported key encodings, numeric overflow and
nonempty receipt/data queues without explicit queue context fail closed. Model counter IDs cannot stand in for
native receipt/data hashes. `nextId` is manipulator metadata with no trie column.

The output is a selected-account synthetic genesis, not an original shard trie.
Opaque shard records, automatic runtime hash-ID registration, receipt cache lifetime and trie
gas in runtime execution remain open. Account serialization follows the pinned
native encoder even at the u128 maximum sentinel; serialization agreement alone
does not establish that every such synthetic account can deserialize or execute.
Evidence is saved in `audit/state-encoding-regressions.json`.

`just chain-receipt-encoding-test` checks native hash ancestry and V0 receipt
envelopes with legacy or V2 action payloads, plus data receipts.
`NearRuntime.NativeIdentity` derives child
receipt IDs from parent hash, execution block height and output index. Action
hashes use `u64::MAX - actionIndex` as salt; callback data IDs derive from the
action hash, block height and a per-action data counter. The message is exactly
32 parent bytes, eight little-endian height bytes and eight little-endian salt
bytes. VM random seeds hash the action hash followed by the block seed. The
native adapter invokes the actual nearcore helpers; Lean uses its pure SHA256.

The `receipt-encode` executable accepts `{formatVersion: 1, codes, identities,
receiptIds, dataIds, receipts, actionFormats, receivedData}`. Receipts/catalogues use the existing
replay transport. Each identity graph node has a `kind`: `hash` hashes original
`bytes`; `input` takes an explicit initial 32-byte `hash`. Derived nodes refer to
an earlier node by zero-based `base`: `transaction` also takes `blockHeight`,
`receipt`/`action`/`data` take `blockHeight` and `index`, and `randomSeed` takes a
32-byte `seed`. Bindings are `[logicalId, graphPosition]` pairs. Missing,
duplicate or aliased bindings and malformed ancestry fail closed. `actionFormats`
contains one `legacy` or `v2` entry per receipt; data receipts require `legacy`.
The runtime uses V2 for VM-created promises even at protocol 83; transaction and
refund receipts use the legacy payload. V2 encodes `refund_to=None`; custom refund
receivers are unrepresented and rejected by the native diagnostic. Output contains
`hashes`, Borsh `receipts`, and Borsh `receivedData` values; `None` differs from
`Some(empty)`. All eight represented action kinds and both ordinary key families
are serialized, including actual hash-bound deployment bytes.

The runtime identity regression starts from original signed Ed25519 transaction
body bytes and the supplied schedule. It independently derives transaction,
receipt, action and callback-data identities, then compares them with actual
successful/failed callback execution across protocols 83–86. A two-function-call
receipt also checks distinct action salts and the data counter resetting per
action. Generated native
IDs are comparison outputs, never graph inputs. This establishes the derivation
and serialization primitives, not an automatically maintained identity registry
inside `Runtime::apply`. Queue-state encoding below consumes explicit receiver
ownership, indices and storage formats. Automatic identity/ownership/format
registration during execution remains open alongside receipt cache lifetime and
trie-backed runtime gas.
Evidence is saved in `audit/receipt-encoding-regressions.json` and
`audit/runtime-identity-regressions.json`.

`just chain-queue-encoding-test` checks `NearRuntime.QueueEncoding` against native
typed trie keys and Borsh records. `state-encode` additionally accepts
`queueContext` with `receiptIds` pairs `[logicalId, hashBytes]`, `dataIds` objects
`{id, hash, receiverId}`, `actionFormats` pairs `[logicalId, "legacy" | "v2"]`,
and `delayed`. The latter is either null (absent header) or an object with
`firstIndex` and one storage `forms` entry per delayed receipt. This preserves
empty queues whose stored indices have advanced. It does not reset them to zero.

Storage forms are `{kind: "receipt"}` for unwrapped receipts,
`{kind: "storedV0", gas, size}` / `{kind: "storedV1", gas, size}` for existing
metadata, and `{kind: "newStored"}` for a newly stored V1 wrapper. Existing gas
and size fields are preserved as supplied, including values different from
current fees and lengths. `newStored` requires the additional `runtimeConfig`
object `{configDir, protocolVersion}`; it computes the ordinary receipt's
prepaid execution gas and encoded length. Data receipts carry zero congestion
gas. Named, NEAR implicit, Ethereum implicit and deterministic account charges
are accounted for, using the loaded Ethereum feature flag. Congestion metadata
is separate from execution gas; this does not extend runtime execution to
unrepresented account-creation behavior or delegate actions.

The encoder emits received data, postponed data-to-receipt links, u32 pending
counts, postponed action receipts, delayed indices and delayed receipt entries.
It checks the ownership of every referenced input/output data ID, rejects missing
or aliased identities/formats, duplicate keys, orphan indices and overflow, and
retains supplied pending counts rather than repairing them. Queue mode adds
`queueEntries` to the existing state/root/witness output. Synthetic corpora compare
all account/queue bytes, roots and complete trie objects independently.

The runtime regression checks the complete represented queue columns in 24 real
callback-first, data-first and delayed programs across protocols 83–86, including
failed callbacks and emptied persistent queues. Its context comes from original
signed transaction bytes, the supplied schedule and Lean's FIFO transitions;
native generated IDs, indices, wrapper metadata and queue bytes are comparison
outputs only. Fixtures retain full origins and executor identities. The current
context construction is explicit for this corpus; general automatic registration
inside receipt execution remains open. Opaque shard/yield/buffer columns and
original shard roots remain outside this represented state. Evidence is saved
in `audit/queue-encoding-regressions.json` and
`audit/runtime-queue-encoding-regressions.json`.

`just chain-transaction-encoding-test` checks original typed transaction bodies
and automatic registration of admitted transaction receipts. The pure
`NearRuntime.TransactionEncoding` serializes V0 and ordinary-key V1 envelopes,
including the V1 nonce tag and trailing nonce mode, all eight actions, both
ordinary public key families, actual deployment bytes and an explicit original
32-byte `blockHash`. It checks body length against the existing size model and
computes the transaction hash from the complete unsigned body. Signatures and
signature verification remain external. Native signed bodies and hashes are
comparison outputs, never inputs to the Lean encoder.

The `transaction-replay` executable takes `{formatVersion: 1, codes, transactions}`;
each row is `{transaction, blockHash}` using the existing replay transaction and
catalogue transport. It returns each `body`, `hash` and `bodySize`. An optional
`admission` object with `configDir`, `protocolVersion`, `blockHeight`, `gasPrice`,
`initialState` and existing `receiptIds` bindings enables the registration
observer. Its transport starts from a queue-free synthetic genesis. The library
also accepts an existing typed queue context, which it validates and preserves.

`NearRuntime.TransactionRegistry.observe` calls the existing
`convertTransaction` transition sequentially, leaving rejected transactions out
of both state and registration updates. Each admitted receipt gets its native
hash from the independently encoded transaction hash and supplied execution
height, and a legacy action-format entry. Logical-ID overwrites, hash aliases,
malformed bodies and model limitations fail closed. A kernel-checked frame
guarantees registration cannot rewrite established data ownership or delayed
queue metadata. The output's `stateAfterTransactions` is the conversion stage,
before any receipt execution or delayed-queue insertion. This observer does not
replace `apply` or add a second receipt-execution implementation.

The regression compares 366 original transaction bodies and hashes, then 24
native admission batches across protocols 83–86, both key families, rejected
transactions between admitted ones, strict/monotonic nonces, height/price
variation and restricted or unfunded callers. Automatically registered IDs
also encode the actual zero-budget local delayed queues without manual receipt
bindings. General promise/data registration, action-derived VM seeds, queue
context evolution during receipt execution and trie-backed runtime gas remain
open. Evidence is saved in `audit/transaction-encoding-regressions.json` and
`audit/transaction-registry-regressions.json`.

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

## Staged ContractData updates

`--trie-updates` exercises the actual native `TrieUpdate` on a canonical on-disk
base trie. The matching Lean mode accepts only the original raw `entries`, a
validated `accountId`, `formatVersion: 1`, and ordered `operations`. For example:

```sh
just chain-trie-compare tools/chain-conformance/fixtures/trie_updates.json
```

Operations are `set` (`key`, `value`), `remove` (`key`), `get` (`key`, Boolean
`accountNodes` and `dereference`), `has` (`key`), `commit`, `rollback`,
`checkpoint`, and `resetCache`. Keys are raw contract storage bytes; both sides
independently encode native ContractData keys. Set/remove are storage-update
primitives: they do not implicitly read the old value or charge VM host fees.

Each step compares its complete visible key/value map, immutable base root,
prospective/committed distinct-key counts, memory/trie pointer kind, read result,
and exact ordered fresh/cached node/value accesses. Prospective writes override
committed changes and the base, including deletion tombstones. Commit transfers
updates to the committed overlay without rebuilding the base. Rollback clears
only prospective changes; it does not rewind cache accesses. Memory pointers
bypass trie accounting even after commit or cache reset.

Checkpoint requires an empty prospective overlay. Native incremental
finalization is compared with independent Lean canonical reconstruction; the
base root changes and overlays clear. The accounting cache persists across root
changes until explicitly reset, allowing unchanged node/value hashes to remain
cached. The Lean rollback/commit frame properties are kernel-checked.

This remains a low-level diagnostic. Commits use the `InitialState` cause;
state-change histories, contract-code caches, proof-size accounting, host fees,
and actual receipt cache lifetimes are outside this comparison. Snapshot reads
use non-accounting native access and do not warm the observed query cache.
Encoding all modeled runtime records and connecting these primitives to receipt
execution remain open.
