# Real-chunk corpus for the Lean runtime (M3)

`near-lean/chain/corpus/` holds chunks that a **neard 2.13.4 localnet** applied at protocol 86, each as an
immutable bundle: everything `Runtime::apply` read, and everything neard itself recorded when it applied the
chunk. `just chain-replay-corpus` replays them through the Lean runtime and compares the results field by field.
This file is the manual: how to rebuild neard, run the localnets, regenerate the workload and the corpus, what a
bundle contains, and how the oracle and the Lean harness check it.

## Why a localnet, and why the full shard state

Gas depends on the number of trie nodes a chunk touches, so exact replay needs the real trie shape. Public RPC
cannot supply trie nodes (`view_state` proofs are refused for large contracts). A Merkle-Patricia trie is a
deterministic function of its key/value set, so the **complete raw state of a shard before the chunk** rebuilds
the original trie exactly: the oracle rebuilds it from the entries and checks the root against neard's. On a
localnet we control the node, so the full state of every shard is available before every chunk. The chunks are
synthetic in content (our workload) and real in execution: the pinned neard produced every expected number.

The corpus lives next to its consumer, `near-lean/chain`, like the node and crypto fixtures live beside their
packages. The generator stays in `tools/localnet`.

## Layout

```
tools/localnet/
  build.py          build neard + the two adapters from the pinned source, record metadata
  exporter.rs       overlay on `state-viewer`: reads a stopped node's database, writes raw bundles
  checker.rs        overlay on `node-runtime`: re-applies a bundle with Runtime::apply (also --decode)
  sandbox_shim.c    LD_PRELOAD shim for restricted sandboxes (descriptor limit, no IPv6); used by localnet.py only
  localnet.py       init / start / stop the two topologies
  workload.py       the deterministic transaction workload
  nearcodec.py      Ed25519, base58 and Borsh encoders for it;  wasmgen.py: a tiny wasm writer
  generate.py       init + start + workload + stop + export for one topology
  corpus.py         pack / unpack / tags / selection / oracle self-check / manifest
  lean_input.py     bundle -> Lean `registered-replay` request, and the comparison
  replay_corpus.py  the harness behind `just chain-replay-corpus`
near-lean/chain/corpus/
  manifest.json     per-chunk feature tags and sizes, tag coverage, build and workload metadata
  build.json        neard / adapter build metadata and the workload that produced the chunks
  blobs/<sha256>.bin.gz        large values (contract code), stored once for the whole corpus
  chunks/<topology>-h<height>-s<shard>/
      meta.json  context.json  pre_state.json.gz  decoded.json.gz  inputs.json.gz  expected.json.gz
```

## 1. Build neard and the adapters (`just corpus-build`)

`build.py` downloads the clean pinned source (`near-lean/runtime/reference.json`: nearcore
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, release 2.13.4, protocol 86) into `tools/localnet/.nearcore/<revision>`
(ignored), uses the revision's own `rust-toolchain.toml` channel (1.93.0) and `--locked`, and builds in
`tools/localnet/target` (ignored; about 4 GB):

1. **neard** from the untouched tree, so its version string says `build 44f7ae6` and not `-modified`.
2. **safe-near-corpus-export** and **safe-near-corpus-check**, two build-only binaries added by a temporary `[[bin]]`
   stanza in the manifests of `tools/state-viewer` and `runtime/runtime` (the same overlay method as
   `tools/chain-conformance/prepare.py`). No implementation file changes; the builder verifies that the checkout and
   `Cargo.lock` are unchanged afterwards and restores the manifests.

Profile: `release`, with `lto = off`, `codegen-units = 16`, `debug = 0`, `incremental = false`. The pinned release
profile uses fat LTO, which needs more RAM and time than a 4-core/15 GB machine has and cannot share compiled
dependencies between binaries; none of these settings changes execution semantics. They are recorded in
`target/bin/build.json` together with the source revision, `Cargo.lock` hash, rustc version, adapter source hashes,
binary hashes and the hashes of the test contracts (`test_contract_rs`, `estimator_contract`, `sharded_contract`
from nearcore's own build of `near-test-contracts`, `fungible_token`). `build.json` is copied into the corpus.

Cold build: about 20 minutes on 4 cores. Binaries and contracts end up in `tools/localnet/target/bin`.

Sandbox note: neard exits when the hard descriptor limit is below 65535, and `neard localnet` reserves IPv6
loopback ports. Where the sandbox forbids both (`ulimit -Hn` below 65535, no IPv6), `localnet.py` preloads
`sandbox_shim.so`, which reports the required limit and binds those sockets on 127.0.0.1, and then rewrites every
address of the generated configuration to IPv4. Elsewhere nothing is preloaded.

## 2. The localnets (`localnet.py`)

| Topology | Validators | Shards | Chain id | RPC / p2p ports |
|---|---|---|---|---|
| `single` | 1 (`node0`) | 1 | `safe-near-localnet-1s` | 18100 / 18101 |
| `sharded` | 2 (`node0`, `node1`) | 4 (boundaries `test1`, `test2`, `test3`) | `safe-near-localnet-4s` | 18200.. / 18201.. |

Both start at protocol version 86 (`neard localnet` writes the binary's `PROTOCOL_VERSION`). `init` runs
`neard localnet` and then fixes what is random or clock dependent: chain id, genesis time
(`2026-01-01T00:00:00Z`), ports, epoch length 30, transaction validity period 60 (nearcore requires at most two
epochs), `gc_num_epochs_to_keep = 10000` so no history is collected before the export. Validator keys are
derived from the account names by nearcore itself. Accounts are placed by lexicographic comparison with the
boundary accounts: `a.node0` is in the first shard, `test1.node0`, `test2.node0`, `test3.node0` in the next three,
so transfers and calls between them cross shards.

## 3. The workload (`workload.py`)

`python3 tools/localnet/workload.py` drives a started localnet over JSON-RPC with transactions it signs itself
(pure-Python Ed25519; keys are `sha256("safe-near-localnet/<seed>/<name>")`). Transactions of one round are
submitted back to back, so they share blocks and chunks; the next round starts when the previous is final.
Rounds, in order:

| Round | What it exercises |
|---|---|
| create-accounts, transfers | `CreateAccount`+`Transfer`+`AddKey`; transfers within and across shards; a transfer to a missing account (refund); two transfers in one transaction |
| implicit-create / -spend | NEAR-implicit account creation and use |
| deploy, calls-* | `DeployContract` of nearcore's `test_contract_rs` (4 accounts), the estimator contract, a fungible token and a generated host-call contract; storage write/read/remove, logs, `sha256`, `ripemd160`, context getters, `validator_stake`, failing calls (panic, abort, bad UTF-16, out of gas, missing method) with and without deposit; fungible-token storage deposit, transfer and `ft_transfer_call` with its callback |
| promises | cross-shard promise chains with callbacks, a failing callee, fan-out, nested `call_promise`, account creation and an implicit account from a receipt |
| keys | function-call and full-access keys, use of a function-call key, `DeleteKey`, deleting a missing key |
| staking | `Stake` below the minimum (rejected), by the validator itself, an accepted stake and its removal |
| delete-accounts | `DeleteAccount` with a cross-shard beneficiary, with a contract and storage, then calls to the deleted accounts |
| hostcalls | `ecrecover`, `ed25519_verify`, `p256_verify`, `keccak256`, `sha256`, alt_bn128 and bls12381 operations, one call out of gas, and `sanity_check` (every host function once, creating accounts and deploying) |
| burst | 14 heavy calls in one block: the chunk exceeds its gas limit and receipts are delayed |
| delegate | `Delegate` (meta transactions): accepted, stale nonce, expired |
| eth-implicit | ETH-implicit account creation (global wallet contract) |
| yields | `promise_yield_create` resumed in the same call, resumed by a later transaction, and one that times out after 200 blocks |
| global-contracts | `DeployGlobalContract` by hash and by account, `UseGlobalContract` of both, calls through them |
| gas-keys | `AddKey` with a gas key, `TransferToGasKey`, a strict-nonce transaction, `WithdrawFromGasKey` |

State that never goes away (yield queues, global contracts, the ETH-implicit account, gas keys) is created last,
so the chunks before it stay representable by the Lean state model.

**Not exercised**, with the reason: `DelegateV2` and `DeterministicStateInit` (no Python encoder written);
transactions signed with secp256k1 or ML-DSA keys (the workload signs with Ed25519 only); a transaction that is
valid in the pool but marked invalid in the chunk (neard's chunk producer already drops them); resharding,
protocol upgrades and missing chunks (a healthy localnet at one protocol version has none); `gas-key` function
calls signed by the gas key (only its funding and withdrawal). The exporter handles missing chunks by skipping
them, as `apply_chain_range` does.

Determinism: the workload is a pure function of the seed (default 1): account names, keys, contract bytes
(pinned), arguments, round order, and the order of transactions inside a round. What the chain's own clock decides
is **not** reproducible: block timestamps and therefore block hashes, random seeds, epoch ids, which transactions
land in the same block, receipt ids and transaction hashes (a transaction names a recent block hash), and the exact
heights. Regenerating therefore yields an equivalent but not byte-identical corpus. The committed bundles are the
source of truth: they pin every one of these values, and the oracle self-check proves each is internally consistent.

## 4. Export (`generate.py`, `exporter.rs`)

`just corpus-generate single` and `just corpus-generate sharded` stop any running node, `init`, `start`, run the
workload, stop the nodes and run `safe-near-corpus-export` on the stopped database of `node0` (all shards are
tracked). For every height and shard whose chunk is new the exporter assembles the inputs exactly as
`NightshadeRuntime::process_state_update` does and **re-applies the chunk with the pinned `Runtime::apply` on the
database trie**. It aborts unless that reproduces what the database says neard recorded: post-state root, every
execution outcome (Borsh), the outgoing receipts, gas used, balance burnt, validator proposals, congestion info
and bandwidth requests. Output: `data/<topology>/raw/h<height>-s<shard>/bundle.json` (the *raw bundle*) and
`data/<topology>/workload.json`, a log of every transaction and its final status.

## 5. The bundle

A raw bundle is one JSON document; bytes are lowercase hex, balances decimal strings. Sections:

* `meta`: chain id, height, block, previous block and chunk hashes, shard id and `ShardUId`, protocol version.
* `context`: the `ApplyState`-level inputs: `applyReason`, `blockHeight`, `prevBlockHash`, `epochId`, `epochHeight`,
  `gasPrice`, `blockTimestamp`, `gasLimit` (the chunk's), `randomSeed`, `currentProtocolVersion`, `isNewChunk`,
  `shardLayout` (Borsh), `congestionInfo` (rows `[shard, Borsh CongestionInfo, missed chunks]` of every shard),
  `bandwidthRequests` (Borsh of all shards' requests of the previous height), `validatorAccountsUpdate` (null, or at
  an epoch start the stake returns, rewards, last proposals and treasury account), `epochInfo` (what
  `EpochInfoProvider` answers: chain id, the validators and stakes, total stake, minimum stake) and
  `proofSizeSoftLimit`. nearcore 2.13.4 has no migration flags in `ApplyState`; the protocol version selects the
  runtime configuration, which `RuntimeConfigStore` supplies.
* `preState`: `root` and **every raw trie entry** of the shard at the chunk's previous state root. The columns are
  accounts, contract code, access keys, received data, postponed receipt ids, pending data counts, postponed
  receipts, the delayed receipt queue, contract data, yield queues and statuses, buffered receipts, the bandwidth
  scheduler state, global contract code and nonces: whatever is in the shard.
* `inputs`: `transactions` (Borsh `SignedTransaction`, validity flag, hash, readable view, and the typed actions, which
  carry the deployed code that the view only hashes) and `incomingReceipts` (Borsh `Receipt`, in apply order, with
  readable and typed views).
* `expected`, what the database recorded for this chunk: `postStateRoot`, `outcomes` (each `ExecutionOutcomeWithId`
  in Borsh and as a view, plus `computeUsage`, which the Borsh form does not carry), `outcomeRoot`,
  `outgoingReceipts` (Borsh and views), `gasUsed`, `balanceBurnt`, `validatorProposals`, `congestionInfo`,
  `bandwidthRequests`. Derived by the same `Runtime::apply` call (checked equal to the record where the database
  has the field): `stateChanges` (Borsh), `stateDiff` (entries added or changed, and removed ones as `null`),
  `balanceStats`, `bandwidthSchedulerStateHash`, `delayedReceiptsCount`, `processedYieldTimeouts`,
  `contractUpdates` (counts only).

A *packed chunk* is the same data split into files; values of 1 KiB or more (contract code, also inside transaction
and receipt views) go to `blobs/` once and are referenced as `{"blob": "<sha256>"}`. `decoded.json.gz` is the
pre-state as upstream's own decoders read it (`StateRecord`), which the Lean converter consumes so that it needs
no Rust. `corpus.unpack` rebuilds the raw bundle exactly; packing is deterministic (sorted keys, gzip without
timestamps), and `manifest.json` lists per chunk its size and **feature tags**: transaction and receipt action
kinds (`action:`, `tx-action:`, `outgoing-action:`), receipt kinds, outcome statuses and failure kinds, the host
functions that executed (`host:`, from the gas profile), state columns present and changed, epoch start, delayed
receipts, yield timeouts, validator proposals, single or multi-shard.

## 6. Selection (`just corpus-pack`)

`corpus.py build` packs every raw bundle into a staging directory, then keeps a subset within a 20 MB budget: all
chunks of the first 24 heights of each topology (small, continuous from genesis), then greedily the chunks that add the
most uncovered tags per byte (rare and required tags weigh more, shared blobs are paid once), then every other chunk
that carries transactions or incoming receipts, smallest first. It prints the required tags no chunk has (none).
Result: 2520 candidates (512 single-shard, 2008 four-shard), 436 kept (148 and 288), 7.7 MB in 2639 files. Empty
chunks beyond the first 24 heights are kept only where they carry a feature (epoch start, yield timeout, queue state).

## 7. Oracle self-check (`just corpus-selfcheck`)

`corpus.py check` re-applies every corpus chunk with the pinned runtime from **exactly the bundle data**:
`safe-near-corpus-check` rebuilds the shard's trie from `preState.entries` (the rebuilt root must equal
`preState.root`), runs `Runtime::apply` with the `ApplyState` of `context`, an `EpochInfoProvider` made from
`context.epochInfo`, and the recorded proof-size limit, commits the trie changes, and prints the results in the
shape of `expected`. `compare_oracle` then requires every field to be equal. A bundle that does not reproduce is an
exporter bug; it is fixed, never dropped. Result: all 436 committed chunks, and all 2520 chunks of the two exports
before selection, reproduce bit for bit.

## 8. The Lean harness (`just chain-replay-corpus`, `just chain-replay-corpus-report`)

`replay_corpus.py` handles each chunk in three steps, `lean_input.py` holds the code:

1. **Blockers.** Features the Lean input format or model cannot express are listed, not approximated:
   pre-state columns outside the state model, actions outside the model's eight (or `UseGlobalContract`, which the runtime reports as an
   unsupported execution), receipt kinds other than action and data, accounts that use a global contract, an invalid
   transaction, a gas-key nonce. The first becomes the `unsupported` reason; all are kept in the audit file.
2. **Conversion and input fidelity.** The decoded pre-state becomes the model state (accounts, access keys, contract
   storage, code catalogue by hash), the transactions and incoming receipts become model values with model ids and a
   `queueContext` binding them to their native hashes, the epoch (`context.epochInfo`: minimum stake, each
   validator's stake, the total) and, at an epoch's first chunk, `context.validatorAccountsUpdate` go into the block, the scheduler state in column 15 becomes
   `initialScheduler` (raw), the outgoing buffer columns 13/14/16/17 become `initialBuffers` (Lean decodes them), and
   the shard layout, previous block hash, congestion info of all shards and previous bandwidth requests go into
   `schedulerInputs`. Lean must then re-encode the converted state to **the bundle's pre-state entries,
   byte for byte**, and re-hash every transaction to the recorded hash; otherwise the chunk is `unsupported: pre-state
   not reproduced ...`, naming the first differing key's column.
3. **Replay and comparison.** The chunk runs through `registered-replay`, which derives native receipt and data
   hashes and the action-derived random seeds itself. Compared, in this order and against `expected` only: each
   outcome's id, executor, status (kind, value or receipt id), logs, receipt ids, gas burnt, tokens burnt; the
   outgoing receipts as Borsh bytes (buffered ones that now fit, then new ones, in order); total tokens burnt and
   subsidized amount against `balanceStats`; the chunk's validator proposals (Borsh `Vec<ValidatorStake>`, deduplicated as
   `Runtime::apply` does), the chunk's own `CongestionInfo`, bandwidth requests, scheduler state
   hash and delayed receipt count; and the
   **complete post-state**, the pre-state entries with `stateDiff` applied, against Lean's encoding of its state
   (key by key, so the root agrees when nothing differs). A model execution issue is a `fail`. Failure detail
   compares the status kind, not the error text.

`audit/chain-replay-corpus.json` holds, per chunk, `pass`, `fail` with the first differing field, or `unsupported`
with the first reason, plus all blockers, tags and seconds; `--report` always exits 0.
Not compared yet: gas profiles, `computeUsage`, state changes in Borsh, the outcome root, the exact failure error
variants.

## 8b. State roots (M4)

`just node-state-roots` (`state_roots.py`) writes a case file per chunk (raw pre-state, `stateDiff`, recorded post-state
root and Lean's replayed post-state) and runs `node-state-roots`, which rebuilds the trie, applies the diff and
compares roots: see the M4 section of `notes/design/NEAR_NODE.md`.

## 9. Regenerating everything

```sh
just corpus-build                 # about 20 min cold
just corpus-generate single       # about 6 min each; run them one after the other or together
just corpus-generate sharded
just corpus-pack
just corpus-selfcheck
just chain-replay-corpus-report
python3 -m unittest discover -s tools/tests -p 'test_corpus.py' -v      # format checks, no neard needed
```

## 10. Current result (M3d)

`just chain-replay-corpus-report`, 436 chunks, about 15 minutes on four cores (`--jobs`, default `min(4, cpus)`):

```
  pass         426
  fail         10
  unsupported  0
by first reason (unsupported / fail):
      5  model execution issue: Unsupported host semantics: env.ecrecover
      4  model execution issue: Unsupported host semantics: sha256
      1  model execution issue: Unsupported host semantics: ripemd160
```

M3a measured 70 pass, M3b 129, M3c 405. M3c closed the multi-shard layout (scheduler, congestion info, forwarding and
buffering of outgoing receipts, bandwidth requests) and the converter gap (pre-state postponed receipts, their
data ids and pending counts, received data, delayed receipts with their stored forms). M3d closed the staking and
epoch chunks: `Stake`/`Unstake` with their validator proposals (compared), `validator_stake` and
`validator_total_stake` from `context.epochInfo`, and the 12 epoch-start chunks, where `context.validatorAccountsUpdate`
(rewards, stake return, treasury) is applied before the chunk runs.

What remains:

* M3e (crypto hosts): `ecrecover` (5), `sha256` (4) and `ripemd160` (1). The four `sha256`/`ripemd160` chunks of
  `h48` and `h205` also call `validator_stake`, whose gas is then checked only up to the crypto host.

Bandwidth requests are empty in every corpus chunk, so the request grants and the random tie breaks of the
scheduler are covered by unit tests with values from the Rust crates (`runtime-tests`), not by replay.
