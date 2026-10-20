# Captured accounts as synthetic chain genesis

`chain-import` connects the block-pinned RPC snapshot tool to both full-runtime
executors. It preserves selected accounts' balances, locked balances, storage
usage, ordinary access keys, raw contract bytes and complete binary storage.
The native adapter uses upstream `Account`, `AccessKey`, `TrieKey` and Borsh
types to encode the genesis. Both executors then load it and must agree on
all represented initial fields before a fixture is published.

From the repository root:

```sh
just chain-reference-build
just snapshot /tmp/lockup.json lockup.near
just chain-import /tmp/lockup.json /tmp/lockup-chain
just chain-import-test
```

Contract imports require `wasm-tools 1.251.0`. The importer validates and prints
actual Wasm bytes into the model's frozen code catalogue. The correctness of
this byte-to-WAT/decoder connection remains an external assumption.

## Evidence and execution

The destination must not exist. It contains the original snapshot and scenario,
portable `native.json` and `model.json` requests, relative configuration/code
assets, and both zero-block traces. `manifest.json` records hashes of every
input/asset, native build provenance, model/wasm-tools executable hashes and
whether the captured RPC configuration matches the pinned table. The manifest
is published last; a directory without it is incomplete. Existing paths are
never overwritten. Runtime executables are frozen for validation but are not
included in the portable directory.

Run requests with that directory as the working directory, using the binaries
whose hashes are recorded in the manifest:

```sh
cd /tmp/lockup-chain
/path/to/near-apply-reference < native.json > native-run.json
/path/to/chain-replay < model.json > model-run.json
```

The importer validates **initial state**, not execution equivalence. Its manifest
keeps `executionComparisonEstablished` and `historicalReplayEstablished` false.
Execution outputs remain separate diagnostics; adding them does not extend the
manifest's original file hashes. Current differential financial coverage is
specified in [README.md](README.md).

## Synthetic transactions

Pass `--scenario /path/to/scenario.json` to add explicit blocks. Transactions
use one explicitly funded **synthetic caller**, with a deterministic local test
key. It cannot replace a captured account. Its seed is public fixture data;
never provide a real private key. The tool does not contact or submit to a
network. All eight modeled action kinds are encoded and signed through native
protocol types; this does not assert that their execution is equivalent.

A scenario has this shape:

```json
{
  "caller": {
    "accountId": "fixture-caller.near",
    "seed": "public-test-seed",
    "amount": "100000000000000000000000000"
  },
  "blocks": [{
    "blockHeight": 100,
    "blockTimestamp": 1000000000,
    "epochHeight": 0,
    "gasPrice": "100000000",
    "gasLimit": null,
    "randomSeed": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    "prevBlockHash": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    "incomingIndices": null,
    "transactions": [{
      "receiverId": "lockup.near",
      "nonce": 1,
      "actions": [{"FunctionCall": {
        "method_name": "get_foundation_account_id",
        "args": "e30=",
        "gas": 100000000000000,
        "deposit": "0"
      }}]
    }]
  }]
}
```

Transaction `blockHash` optionally overrides the block's `prevBlockHash`.
Actions use the native `Action` JSON representation (including base64 arguments
and code); unknown or silently discarded action fields fail round-trip checks.
`codeBlobs` optionally supplies extra base64 module bytes for dynamically
created/deployed code. Transaction deploy bytes are added automatically.

`incomingIndices` uses the pending queue at each block's start: `null` delivers
all, `[]` defers all, and an ordered list selects positions. Add subsequent
blocks explicitly for outgoing receipts and refunds; execution never drains
work after the last block. Native congestion/bandwidth fields optionally
override the pinned one-shard example defaults. These native-only contexts are
retained in the request, outside the current model's represented interface.
The integration test provides an executable four-block example without RPC.

## Scope and rejection

This constructs a new trusted, single-shard genesis from selected accounts.
Unselected accounts are absent, and receipt/data/delayed queues start empty.
RPC data is not the original raw shard trie; state proofs are not verified.
Balances/usage are copied rather than reconstructed from a historical genesis.
A captured block identifies the source data, not a historical execution context.
The pinned configuration and caller/block inputs define the synthetic run.

Supported protocols are 83–86. Filtered/incomplete storage, missing or mismatched
code, duplicate accounts/keys/storage, global contract references, gas-key lanes,
unsupported key permissions and out-of-range values are rejected. Ordinary
Ed25519 and secp256k1 access keys retain native Borsh bytes and permissions.
Captures with unsupported account fields fail instead of dropping those fields.
