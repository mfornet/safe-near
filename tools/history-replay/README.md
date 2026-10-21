# Historical chunk capture and offline replay

This tool captures the original inputs of one nearcore `Runtime::apply`, exports
its trie witness and required code blobs, and re-executes it without an archive
or network connection. A separate archive anchor compares the result with the
exact block/shard's persisted outcomes, outgoing receipts and chunk extra, plus
the following chunk's state, outcome and receipt commitments.

The first real historical fixture has **not yet been captured**. Public RPC
discovery is available under ignored `audit/history-discovery/`; those headers
and configuration responses are not replay fixtures. Capture requires an
database retaining the selected pre-state, or an export made on a host with
such a database. An archival database supports older selections; a recent shard
sync may provide a smaller retained window. Public peer acquisition is currently
being tested; it has not yet produced a verified public fixture.

## Build

```sh
just history-build --source /path/to/clean/pinned/nearcore --neard --smoke
```

Omit `--source` to fetch the pin. The builder creates its own ignored checkout,
leaving the supplied source unchanged. It adds a guarded capture wrapper at the
runtime boundary, an observational storage wrapper and archive export code
in state-viewer. Nonselected applies call upstream `Runtime::apply` directly;
selected applies also replay the captured witness independently. This is an
instrumented nearcore build, distinct from the existing clean-source synthetic
oracle. `target/build.json` records every overlay hash and executable digest.

`--target-dir` can reuse a native dependency cache. The pinned compiler is Rust
1.93.0. The first `neard` build is substantially larger than the runtime-only
replay build. `--smoke` additionally builds the test-only capture driver; its
inputs and outputs must not be mistaken for history.

## Acquire recent shard state

Public snapshots may require provider access. An alternative is a bounded,
non-validator mainnet node tracking the shard containing a selected account:

```sh
just history-build --neard --direct-state-sync
just history-bootstrap --near-home /path/to/new-node \
  --neard /path/to/target/debug/neard --account a.near \
  --direct-state-sync --max-seconds 1800 --max-gib 10
```

The parent directory must exist. The command binds local listeners to loopback,
uses fresh boot peers from the configured mainnet RPC, and stops after syncing
and observing additional blocks. It leaves a candidate finalized block and a
retained database for capture. The account selects a **whole shard**; this does
not download only that account's state. A shard can exceed the default budget.
Time or disk limits stop the node and leave a resumable owned directory; repeat
with `--resume` to continue. No validator key is accepted, and no transactions
are signed or submitted. Limits cover the node run; initialization/build have
separate network and disk costs. Disk checks occur between polling iterations,
so the cap can be exceeded by writes during an iteration.

`--download-concurrency N` controls concurrent part requests (default 2, maximum
16); `--apply-concurrency N` separately controls local part application (same
bounds). Start conservatively because application can create disk contention.
Progress, including header/state-sync stages, is saved in the node directory
and printed every 30 seconds. Interrupting the command stops its child node;
creating `bootstrap-stop` in the node directory also requests a stop. Remove
that file before resuming.

If general boot peers do not track the desired shard, `--boot-peers peers.json`
accepts an explicit JSON array of `peer-id@host:port` strings and restricts
outbound connections to those peers. A running node's local
`/debug/api/snapshot_hosts` and `/debug/api/peer_store` endpoints can identify
advertised snapshot hosts and known addresses. Match the snapshot's shard and
sync hash (the state-sync block's previous-previous hash), rather than assuming
that every block producer serves that state. Endpoint metadata is discovery;
nearcore still validates received data.

The optional build overlay sends upstream state-header/part requests over
existing outbound Tier2 connections, allowing acquisition behind NAT without
inbound Tier3 callbacks. It is enabled only by the bootstrap's explicit flag;
upstream response handling and state validation are unchanged. Its source hash
is recorded in build provenance. Successful sync alone does not establish replay:
the selected chunk must still pass capture and offline archive verification.

## Capture one chunk

Use the executable paths from `target/build.json`:

```sh
just history-capture \
  --near-home /path/to/archive \
  --height 220940000 --shard-id 11 --temperature cold \
  --neard /path/to/target/debug/neard \
  --replay /path/to/target/debug/safe-near-history-replay \
  --out /path/to/new-bundle
```

The height/shard above is a discovery candidate, not an established successful
capture. Select an interval supported by the archive and pinned runtime.
`cold` selects nearcore's split store; use `hot` for a database whose required
data resides in hot storage. The command runs state-viewer in read-only mode
with trie-free access to reproduce flat-storage gas costs. It does not enable
state writes, transition persistence or synthetic transaction signing.

Initial scope is a new chunk at protocol 83–86, within an epoch, with no
validator-account updates or VM-upgrade prewarming. The immediately following
block must contain a new chunk for the same shard in the same epoch. Unsupported
inputs and missing state fail; they never produce an empty successful fixture.
All transactions, expiry flags and incoming receipts are preserved in order.
Persistent delayed/postponed/data/scheduler state comes from the original trie.

## Offline bundle

The portable directory contains:

| File | Contents |
| --- | --- |
| `request.json` | Complete runtime context, original transaction/receipt Borsh, validity flags, captured epoch queries, pre-root, witness and native expected observations |
| `archive.json` | Original and successor block/chunk headers, archived chunk extra, exact archived outcomes/outgoing receipts and network/genesis context |
| `capture-build.json` | Capture compiler/source-overlay/executable provenance |
| `manifest.json` | Asset hashes, transition identity, verification evidence and trust boundary; published last |

Borsh payloads use lowercase hex. `witness` encodes upstream
`PartialState::TrieValues`: original serialized trie nodes/values plus required
base contract code indexed by its original content hash. The storage observer also captures code-existence reads marked
`NO_SIDE_EFFECTS`, keeping them separate from the consensus proof recorder so
proof-size admission and gas accounting retain their original behavior.
Deployments within the chunk remain in the original transaction/receipt bytes.
The witness is not a selected-account genesis and is never rebuilt from account
JSON.

The recorded epoch provider is an explicit environment boundary. Uncaptured
queries stop replay. The archived store and its block history are trusted;
consensus signatures and a light-client chain of trust are not reverified.
The offline verifier recomputes header hashes, chunk-header membership roots,
transaction roots, outcome roots and successor receipt commitments, and checks
the native post-state root against archived state. It does not use RPC JSON
hashes as protocol commitments.

```sh
just history-verify /path/to/bundle \
  --replay /path/to/target/debug/safe-near-history-replay
```

Each run checks every asset hash and performs fresh native execution. Complete
captured observations include outcome Borsh, separately recorded compute,
outgoing receipts, state-change bytes, queue processing, stats, proposals,
congestion/bandwidth state and contract updates. Persisted outcome Borsh omits
compute in upstream nearcore: its historical comparison covers the persisted
encoding, while compute is checked between capture and offline execution.

## Lean boundary

The bundle is intended to become the input to Lean historical replay. The
current registered Lean frontend reconstructs a synthetic trie and does not yet
consume this witness format. A future adapter can be selected with:

```sh
just history-verify /path/to/bundle --replay /path/to/native-replay \
  --model /path/to/candidate-historical-lean-adapter
```

The candidate receives the runtime request **without** `nativeExpected`, and
must return the same canonical observation object. Its executable digest is
recorded independently of capture provenance, allowing a frozen bundle to
test future implementations. Current Lean executables cannot be substituted
directly. `leanExecutionEstablished` stays false until an actual candidate run
matches; native verification alone never sets it true.

## Validation

```sh
python3 -m unittest discover -s tools/tests -p 'test_history_replay.py'
just history-witness-test --reference /path/to/near-apply-reference
just history-localnet-test
```

The Python tests cover custody/publication, archive/runtime binding and failure
boundaries. The native witness test uses the existing oracle's synthetic
example, tests transfers, expiry, contract writes and missing-method failures
with both trie accounting modes, and rejects mutated witnesses and inputs.
The local-node integration test also exercises state-viewer extraction, the
archive sidecar and offline commitment verification against a real local
database, and rejects corrupt archive fields. It explicitly verifies that this
synthetic chain cannot be published as a mainnet/testnet historical bundle.
These tests do not establish public historical replay. See the
[design](../../notes/todo/replay_near_history.md) for the milestone and
remaining Lean/storage work.
