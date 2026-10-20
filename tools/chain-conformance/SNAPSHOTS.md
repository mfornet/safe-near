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

The optional caller `accessKey` uses native JSON: for example
`{"nonce":0,"permission":{"FunctionCall":{"allowance":"1000000000000000000000000","receiver_id":"captured.near","method_names":["read"]}}}`.
Omitting it keeps the default nonce-zero full-access key. Setting it to `null`
creates a funded caller without the signing key, for missing-key admission tests.
The native serialized key determines synthetic storage usage; finite and
unlimited permissions retain their complete fields in both executors.

`just chain-permission-test` checks 72 scenarios across protocols 83–86,
including rejected transactions between accepted ones. Admission compares the
complete missing-key, receiver, method and allowance error parameters. Native
failure order after envelope/key/nonce checks is balance, allowance, storage
stake, then permission constraints;
within a single function call, attached deposits precede receiver mismatches.

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

## Compare contract executions

```sh
just chain-compare /tmp/lockup-chain --report /tmp/lockup-comparison.json
just chain-contract-test
just chain-contract-probe --protocol 86 --report /tmp/contracts.json
```

`chain-compare` verifies the manifest's file hashes and exact executor build
identities, copies assets and executors into a temporary frozen run, binds the
model transactions to native-decoded signed inputs, and checks common block
contexts. Re-import a fixture when either executor changes. It retains both raw
traces, the complete fixture files and field differences in its report. An
unsupported projection also fails and is recorded; it never becomes a pass.

The current projection handles account/key/code/storage state, action and data
receipts, postponed dependency indices, received data, ordered delayed work,
ordered outgoing/pending queues, outcomes, gas, token burn and subsidies.
Native action V2 receipts are accepted only with `refund_to = null`. Other
native receipt variants, gas-key nonce lanes and unmapped failure kinds are
rejected. Ordinary-key V0 and V1 envelopes preserve their actual version and
nonce mode through native signing and replay. Transaction admission mappings
preserve version and nonce error parameters. Mapped receipt failures preserve
account, actor, registrar and public-key parameters, function-call errors and
the failed action index (including no index for final storage checks). Unknown
error variants or extra native parameters fail closed. Lean diagnostic repr
and message formatting remains in raw evidence; comparison uses typed semantic
errors instead. Native public execution-error messages are compared exactly.

`just chain-action-test` checks administrative actions, successful key changes,
late-delivery key nonces and multi-action rollback across protocols 83–86.
Added-key nonces use the actual delivery block height, ignoring supplied nonces.

Receipt ids are renamed using **native events**, independently of model output:
new action receipts, their newly introduced dependency ids, then refunds and
final data receipts. Native outcome `receipt_ids` excludes data receipts. Transaction outcome hashes
map to the model's zero id; the full native hash identity remains in raw evidence.
Map
entry order is canonicalized; receipt/delivery order is preserved. An absent
per-account storage map and an explicitly empty one both denote an empty
storage function and compare equally. No key/value, gas or balance difference
is removed. Native account/receipt representation versions, compute/metadata,
shard scheduler columns and other unmodeled observations remain in raw evidence.

The offline contract fixture has binary storage, named typed parameters, a
read, write, delete, panic-after-write, successful callback and failed callback.
Its tests compare successful and failing calls across protocols 83–86, including
callback-before-data, data-before-callback, reversed delivery, explicit idle
blocks, delayed work and a deliberately unfinished block script. This fixture
is synthetic test data and has no claimed RPC origin.

For delayed receipt continuation, `congestionInfo` must reflect the preceding
native output. The corpus planner materializes this explicit input using the
adapter's `nextCongestionInfo`; resetting it to empty while delayed work exists
causes native queue-gas underflow. The final requests and all inputs remain in
the report. Bandwidth/epoch contexts remain the one-shard fixture environment.
Native uses compute/proof limits; the model's positive chunk budget is still a
gas approximation. Zero-budget deferral is compared directly.

**Storage mutation gas remains incomplete.** Native trie-backed writes/removals
charge trie-node access and old-value bytes through the external storage
adapter. The VM mock does not charge these costs, and the model currently
represents that mock storage environment. Storage values, usage and rollback
are compared, but full-runtime gas differences propagate into refunds, rewards
and balances. The full `chain-contract-probe` corpus includes these mutations
and exits nonzero; it does not subtract or tolerate the differences. Integration
tests separately assert that the comparator catches these known gaps, saving
raw evidence with `expectedToMatch = false` in
`audit/contract-chain-regressions.json`. A passing regression test is not a
claim that those native/model executions match.

## V0/V1 transaction envelopes

Scenario transactions optionally supply `version` (`0` or `1`) and `nonceMode`
(`monotonic` or `strict`). Defaults preserve V0 monotonic behavior. V0 cannot
encode strict mode, and the importer and JSON replay parser reject that shape.
Use `{"version": 1, "nonceMode": "strict", ...}` for sequential V1 nonces.
The native adapter constructs `TransactionV1` and signs its actual hash; signed
bytes and native envelope tags/views remain in the evidence.

The model and native runtime apply the pinned `GasKeys` **envelope** gate to all
V1 transactions, even when their nonce mode is monotonic. The separate
`StrictNonce` gate applies to strict mode. Both currently activate at v85, but
the configuration records each source feature independently. Pre-v85 V1 requests
are valid replay inputs that produce `InvalidTransactionVersion` outcomes; they
are not misclassified as malformed JSON or accepted as V0. Invalid nonce and
nonce-ceiling outcomes are mapped with both numeric parameters preserved.

`just chain-version-test` compares mixed V0/V1 batches at protocols 83–86,
including accepted transactions around rejected ones, strict gaps, stale nonces,
ceiling equality and gate/error precedence. It checks full state, charges,
queues, outcomes and completion, retaining raw evidence in
`audit/transaction-version-comparison.json`. This supports ordinary access keys;
V1 gas-key nonce lanes remain unsupported and are rejected explicitly.

## Stateless action admission

`just chain-validation-test` checks 84 action-boundary and precedence scenarios
across protocols 83–86, two actual 4 MiB overflow cases on protocol 86, and a
signed deployment-byte binding regression. It exercises action/deploy counts,
ordered delete checks, zero/total/overflowing gas, UTF-8 method byte limits,
argument/code sizes, key receiver validation and terminated key-method totals.
Rejections happen before signer charging, allowance updates or nonce changes;
valid transactions around a rejection still execute. Structured native errors
retain every mapped parameter, including the byte-truncated invalid key receiver.
The separate transaction-size gate runs after envelope-feature checks and before
stateful admission. Staking-key curve eligibility remains an open boundary.

RPC `SignedTransactionView` masks deployment code as its hash. The native
adapter therefore exports both the original RPC `view` and actual typed
`actions` decoded from the signed Borsh input. The importer and comparator use
those actual actions; code bytes are never reconstructed from an RPC code hash.
A regression changes only the model deployment label and confirms that the
signed bytes cannot be rebound to a different catalogued module.

Synthetic request and initial-trace JSON files use compact encoding to avoid
inflating multi-megabyte byte arrays. Their complete contents remain covered by
the manifest hashes. Configurations, capture/scenario records and manifest
metadata remain readable JSON. Reports retain all raw inputs and observations.

## Transaction envelope sizes

`just chain-size-test` compares 48 imported native/Lean fixtures (192 signed
transactions). It covers every modeled action encoding, finite/unlimited key
permissions, UTF-8 method names, V0/V1 envelopes and Ed25519/secp256k1 signers.
The optional synthetic caller `keyType` is `ed25519` (default) or `secp256k1`;
other schemes are rejected. These keys and seeds are public local fixture data.

The model computes Borsh body size from field widths and byte lengths. Ordinary
V1 contributes three bytes beyond V0's layout: transaction tag, nonce tag and
nonce mode. Native `SignedTransaction::get_size`, `wire_size` and
`size_for_limits` are exported separately and compared to each model block's
`transactionSizes`. Wire size is also checked against actual signed Borsh length.
The source-derived `runtime_admission.transaction_size_includes_signature` flag
starts at protocol 85; it selects body-only size before that feature and full
wire size afterward. Ed25519 signatures occupy 65 Borsh bytes; secp256k1 occupies 66.

Boundary fixtures use native empty-argument encoding to choose payload lengths,
then independently compare the model sizes and complete execution traces.
Exact-limit transactions execute, and one-byte overflows reject atomically.
Version gates precede size checks; size precedes signer/key/nonce/balance checks.
Unknown or malformed signature/key representations stop as a model issue without
charges rather than receiving a guessed signature width.

Large reports live in `audit/transaction-size-cases/`; the small regression index
binds every per-case file by SHA-256. CI uploads the index and all full raw cases.
