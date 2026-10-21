# Historical runtime replay

The goal is an offline integration test that executes real NEAR history through
Lean and pinned nearcore, comparing protocol outputs byte for byte. The existing
tools provide substantial synthetic differential coverage, but do not yet capture
or replay historical shard execution. Downloading several account states and
filtering transactions is useful for a separate synthetic regression; it does
not generally preserve historical execution results.

## Current implementation

The initial capture and offline native replay tooling now lives in
[tools/history-replay](../../tools/history-replay/README.md). It instruments the
pinned runtime, retains original trie/code reads and checks archived chunk
outputs and successor commitments. Native synthetic witness regressions cover
the transport. Capturing and validating the first real historical bundle still
requires an archival data source; this milestone is not yet established.

| Component | Available behavior | Remaining boundary |
| --- | --- | --- |
| [Account capture](../../tools/near_snapshot.py) | Pins account, code, keys, storage and configuration to one block hash; checks code hashes | Trusted RPC input; no shard queues, original trie or epoch state; large state may exceed RPC limits |
| [Snapshot import](../../tools/chain-conformance/import_snapshot.py) | Builds native and Lean initial states, frozen code/config assets and a hashed manifest | Creates a selected-account genesis with empty queues and a synthetic signed caller |
| [Native oracle](../../tools/chain-conformance/reference.rs) | Calls the real trie-backed `Runtime::apply`; exports raw state, outcome/receipt Borsh, stats and contexts | Single shard, mock epoch provider, fixed protocol, all transaction validity flags true, always a new chunk |
| [Registered replay](../../near-lean/chain/ChainReplay/Registered.lean) | Derives transaction/receipt/action/data hashes, action randomness and queue encodings; uses a shared chunk trie accounting cache | Reconstructs the complete represented synthetic trie; scheduler starts from the synthetic initial state |
| [Comparator](../../tools/chain-conformance/compare_fixture.py) | Compares typed execution, exact outgoing receipt bytes, represented state/queue bytes, complete synthetic chunk entries and chunk entry roots | Does not compare complete native outcome bytes, compute/metadata, state-change histories or all shard features |

The reference pin is nearcore 2.13.4, revision
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`. The apply harness accepts protocols
83–86. Configuration tables for other versions do not establish execution
support. See [reference.json](../../near-lean/runtime/reference.json), whose
historical and general execution conformance flags remain false.

Storage mutation gas is no longer an entirely missing component:
[chunk storage tests](../../tools/chain-conformance/test_chunk_storage_accounting.py)
require exact comparisons for writes, removals, shared caches, rollback, large
values and account recreation across protocols 83–86.
[Contract comparison tests](../../tools/chain-conformance/test_contract_comparison.py)
also require mutation cases to match. Some older prose in the harness guides
still describes these cases as expected mismatches. These implemented tests
are distinct from evidence of a fresh successful run.

## Why selected transactions change history

NEAR executes asynchronous receipts. A transaction included after the snapshot
can create work executed later on another shard; a receipt executed immediately
after the snapshot may originate before it. Callbacks need data receipts and
postponed dependency records. Refunds can touch accounts outside the selected
contracts. Receiver-based transaction filtering misses these dependencies.

There are also dependencies beyond account values. Trie shape affects charged
node accesses, and earlier execution in the chunk can warm shared node/value
hashes. Chunk budgets, proof limits, congestion and bandwidth state affect what
executes. A smaller synthetic trie can therefore produce different gas, refunds,
contract rewards and balances even when application storage starts identically.
This follows from the trie accounting and cache behavior modeled by the current
registered runner; dependency closure over account names alone is insufficient.

The proposed exact replay unit is a **complete shard chunk transition**. Account
selection finds interesting chunks and limits the initial corpus. It must not
silently filter the inputs of a test claiming historical equality.

## Two test modes

1. **Selected-account differential replay.** Reuse capture/import/comparison to
   run real contract binaries and captured account values in a synthetic
   environment. Adding original transactions requires a new import path that
   preserves their bodies, signatures, hashes and signer states; the current
   scenario importer signs new transactions. Exact agreement means agreement
   between executors in this constructed environment. It does not mean matching
   the historical chain's outputs.
2. **Historical chunk replay.** Preserve the original pre-state root, ordered
   transactions and incoming receipts, persistent queues, environment and shard
   identity. First establish that nearcore reproduces the archived result, then
   compare Lean against that independently anchored result.

Both modes are useful. Only the second satisfies historical byte equality.

## Proposed capture and fixture format

Add a versioned historical bundle alongside the existing synthetic format.
Capture once using an archival nearcore store, then run offline without RPC.
Ordinary account RPC remains a discovery/debugging tool. Its account queries
are block-pinned, but do not provide a complete runtime invocation. See the
[account RPC](https://docs.near.org/api/rpc/contracts) and
[block/chunk RPC](https://docs.near.org/api/rpc/block-chunk) interfaces.

Use the pinned state viewer's chunk input construction as the extraction seam.
It already gathers transaction validity flags, incoming receipts and historical
block/shard context. Its recorded-storage path obtains an execution storage
proof. The new capture adapter wraps that path; the upstream `apply-range`
command alone is not a portable fixture exporter.
See the pinned
[apply range source](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/tools/state-viewer/src/apply_chain_range.rs).

The proposed bundle contains:

| File | Required contents |
| --- | --- |
| `manifest.json` | Format, network/genesis identity, nearcore revision, protocol/config hashes, runtime feature/backend selection, input asset hashes, captured transition identities, expected-output hashes and declared comparison scope |
| `headers/` | Original block and chunk headers, epoch/shard layout identity and the precise pre/post roots for each apply |
| `inputs/` | Original signed transaction Borsh, valid-period flags, exact ordered incoming receipt Borsh, block/apply context and runtime epoch queries |
| `state/` | Original pre-state trie objects or an authenticated partial trie witness, including queue/scheduler records and required absence paths |
| `code/` | All required raw Wasm modules, code hashes, decoder version and frozen decoded assets; include deployments occurring during the interval |
| `expected/` | Archived outcome/receipt evidence and roots, plus complete canonical output from verified nearcore re-execution |

Store binary payloads as files or base64, avoiding large JSON integer arrays.
Use content hashes and relative paths so the bundle is relocatable. Reject
unknown versions, missing objects, duplicate keys and unsupported features.
Distinguish a proven absent key from unavailable witness data. Missing data must
stop execution rather than turn into an empty account, storage value or code.

The pre-state is the state immediately before the selected shard application,
identified through nearcore's chunk input construction. Do not assume that an
account query at height H or a root on block H is automatically that pre-state.
Missing chunks and carried chunk headers require explicit handling.

## Preserving the original trie economically

A complete shard dump is a useful correctness baseline but may be too large
for routine fixtures. Prefer an execution witness containing the original
trie nodes and values needed by the full transition, with sibling hashes retained
so the original root and updates can be verified. Rebuilding a trie from only
the observed account key/value pairs loses its historical shape.

Nearcore's pinned recorded-storage path is a promising source of that witness.
The exporter must validate proof completeness, contract-code availability and
the execution mode before relying on it. Storage proofs and IO traces serve
different purposes; IO traces alone are not authenticated state snapshots.
The [nearcore IO tracing guide](https://near.github.io/nearcore/practices/workflows/io_trace.html)
is useful for diagnosing access differences.

Lean needs a witness-backed trie reader/updater that preserves the original
root and cache semantics. Its existing canonical trie builder remains useful
for synthetic tests, but cannot substitute for this historical backend. Compare
logical runtime roots and protocol bytes, not physical RocksDB file layouts.

First support independent single-chunk fixtures. A later contiguous replay must
carry each executor's own state forward and verify pre-root/post-root continuity.
It may add authenticated backing nodes for later accesses, but must not replace
Lean state with nearcore's intermediate values. Independently restarting each
chunk from a captured pre-state establishes per-chunk equality only.

## Missing implementation work

| Priority | Work | Completion criterion |
| --- | --- | --- |
| 1 | Historical exporter and lossless input loader | Native round-trip preserves original transaction/receipt bytes, ordered inputs, roots, validity and context; no signing or synthetic caller |
| 1 | Native historical environment | Real shard layout/epoch context, initial scheduler/queues, validator update inputs and apply flags replace fixture defaults; native replay matches archive |
| 1 | Lean witness-backed storage | Verify original pre-root, exact access/cache accounting, absence and writes; derive post-root without rebuilding a selected-account trie |
| 1 | Historical receipt delivery | Accept newly arriving external receipts for each chunk, initialize in-flight/delayed/postponed/data state, preserve actual order and processed/deferred work |
| 2 | Complete protocol output encoding | Independently encode execution outcomes/errors/metadata and state-change records; represent compute, limits, proposals and congestion/bandwidth outputs |
| 2 | Feature inventory and support | Preflight checks every action, key, receipt and trie column; implement or explicitly reject global contracts, gas keys, delegation, yield/resume, buffers and epoch-dependent behavior |
| 2 | Portable offline runner | Immutable inputs and expected outputs, explicit candidate executable selection, full diffs and reproducible evidence |
| 3 | Continuous and multi-shard history | Carry state across chunks, model missing chunks and protocol/epoch boundaries, then extend routing/resharding support |

The current `pendingReceipts` plus `incomingIndices` API only selects from work
already in the harness queue. It cannot directly introduce arbitrary external
receipts newly arriving from historical shards. Extend the replay transport and
identity registry for these inputs. Hashes of boundary receipts/data are
legitimate captured inputs; hashes of children generated inside the test must
remain independently derived outputs.

Capture historical epoch-provider requests/responses or export sufficient
epoch data for a real provider. Recording responses is an explicit trusted
environment boundary, not verification of epoch consensus. The single-shard
mock cannot stand in for a historical shard just because the selected contracts
happen to reside there.

## Defining byte equality

Compare each transition's ordered outgoing receipt Borsh; canonical outcome
Borsh and separately omitted compute counters; exact status/error parameters,
return bytes, logs and gas/token charges; raw changed trie keys/values and
deletions; persistent queue records; and original post-state root. Add native
state-change causes/order, validator proposals, scheduler/congestion/bandwidth
outputs and runtime statistics to the declared complete output surface.

Use typed checks to explain byte differences, not to erase them. JSON map
formatting and diagnostic `Debug` strings are not canonical protocol bytes.
Unsupported output fields make a case incomplete; a narrower passing projection
must identify its scope and cannot report full byte equality. In particular,
the present comparator's typed failure mapping does not establish complete
native outcome serialization equality.

## Proposed milestones and acceptance

1. Choose a short historical interval whose actual protocol is supported by
   the pin. Start with one shard chunk in a stable epoch, ordinary accounts and
   a small contract/storage workload; inventory all other work in that chunk.
   If it contains unsupported features, report them and select another case.
   A quiet testnet interval is an option, not an assumed existing fixture.
2. Export and replay that chunk with nearcore alone. Require agreement with
   archived state roots and available outcome/receipt commitments. Validate
   the chain's commitment encoding rather than hashing RPC JSON. This is the
   first gate: a differential pass without it could merely validate an exporter
   mistake shared by both executors.
3. Feed the same immutable bundle to Lean. First expose current field coverage
   and differences; finish the missing storage/environment/output work before
   marking the fixture a complete byte-equality test.
4. Extend to consecutive chunks, receipts originating before the interval,
   callbacks, writes/removals, failed actions/rollback, refunds and delayed work.
   Add independent fixtures from several contracts, then expand feature coverage.

Current capture and verification commands are documented in the
[tool guide](../../tools/history-replay/README.md). For example:

```sh
just history-build --source /clean/pinned/nearcore --neard --smoke
just history-capture --near-home /archive --shard-id SHARD --height H --out BUNDLE \
  --neard /path/to/neard --replay /path/to/safe-near-history-replay
just history-verify BUNDLE --replay /path/to/safe-near-history-replay
```

The existing Lean registered frontend cannot yet consume historical witnesses.
The tool accepts a future historical adapter through `--model`, passing only
captured inputs and withholding expected native observations.

Capture needs archive access; normal tests need only the downloaded bundle and
executables. Keep the capture-time Lean digest as provenance, while allowing
the test runner to select a newly built candidate and record its digest. The
existing synthetic comparator requires exact manifest executor hashes and
re-import after changes; reusing that rule unchanged would prevent a downloaded
historical bundle from testing future Lean implementations.

A test passes only if every requested transition executes, the native/archive
anchor validates, the declared complete output surface matches, and no feature
or witness gap was skipped. Include regressions that remove a witness node,
alter a byte/context/receipt position, and mutate expected outputs; each must
fail. Report unfinished receipts at interval end explicitly; do not invent
extra historical settlement blocks.

Start with a small offline fixture in routine CI once implemented and measured.
Keep larger histories in a versioned downloadable corpus, run by the existing
manual/periodic expensive-check infrastructure. Expanding history length before
completing one faithful chunk would multiply unresolved differences.
