# Lean chain JSON replay

`chain-replay` executes the existing `Near.step` on exactly the supplied blocks.
It accepts complete represented state, transactions and an ordered receipt
schedule. It records state, pending and outgoing receipts, outcomes, burnt tokens and committed
promise subsidies after every attempt. Idle blocks remain idle; it never adds settlement
blocks automatically. This is the Lean side of the full-runtime comparison
harness, not evidence of agreement with nearcore by itself.

From the repository root:

```sh
(cd near-lean/chain && lake build chain-replay)
near-lean/chain/.lake/build/bin/chain-replay \
  < tools/chain-conformance/fixtures/transfer.json
just chain-replay-test
```

The executable reads one complete JSON document from stdin (pretty JSON is
accepted) and writes one compact JSON document to stdout. Malformed input,
missing/unknown fields, invalid numeric bounds, duplicate map keys, missing code
labels and unparseable WAT fail the process without publishing a partial trace.
All blocks are parsed before any block executes.

## Request

Every field is required, including empty arrays and explicit `null` values:

| Field | Representation |
| --- | --- |
| `formatVersion` | `1` |
| `protocolVersion` | Currently 83–86, selecting the committed configuration table |
| `configDir` | Path to the configuration tables |
| `codes` | Array of `{hash, codePath, watPath}` catalogue entries |
| `initialState` | Complete represented state described below |
| `pendingReceipts` | Ordered receipt array available for block delivery |
| `blocks` | Explicit block array |

Each catalogue entry loads actual binary bytes (which determine code size) and
a decoded WAT module. Hash labels and byte arrays must be unique. The caller
must independently establish the hash and byte-to-WAT correspondence, freeze
the files for the run, and retain those bindings in the comparison evidence.
The executable does **not** verify those correspondences or implement binary
Wasm validation. A successful WAT parse is not full module validation.
These are the same external decoder assumptions as the existing runtime.

Direct deployment actions and initial account code must name a loaded label.
Code deployed through a contract promise is resolved by exact binary bytes.
An unrecognized blob becomes an explicit decoder issue and rejects the entire
apply atomically, retaining the input snapshot and suppressing protocol
outcomes, outgoing work and fees. It cannot become an empty executable module.

## State and actions

Association lists use JSON pairs, preserving their original order:

| State field | Representation |
| --- | --- |
| `accounts` | `[accountId, {amount, locked, codeHash, storageUsage}]` rows; `codeHash` is a catalogue label or `null` |
| `accessKeys` | `[[accountId, publicKeyBytes], {nonce, permission}]` rows |
| `storage` | `[accountId, [[keyBytes, valueBytes], …]]` rows |
| `postponed` | `[receiptId, receipt]` rows |
| `pendingDataCount` | `[receiptId, count]` rows |
| `postponedByData` | `[dataId, receiptId]` rows |
| `receivedData` | `[dataId, bytesOrNull]` rows; failure (`null`) differs from successful empty data (`[]`) |
| `delayed` | Ordered receipt array delayed internally by runtime gas limits |
| `nextId` | Model receipt/data counter |

Balances, deposits, stakes, allowances and gas prices are decimal strings
bounded by u128. Block heights/timestamps, epoch heights, gas, storage usage
and access-key nonces are bounded by u64. Bytes are integer arrays bounded
by u8. Receipt/data ids are model natural-number labels, not NEAR hashes.
Initial global state validity and identifier freshness remain trusted inputs;
shape/bounds/duplicate checks do not prove those invariants.

Permissions are `{kind: "fullAccess"}` or `{kind: "functionCall", allowance,
receiverId, methodNames}`; allowance is a decimal string or `null`.

Supported action objects:

- `{kind: "createAccount"}`
- `{kind: "deployContract", codeHash}`
- `{kind: "functionCall", methodName, args, gas, deposit}`
- `{kind: "transfer", deposit}`
- `{kind: "stake", stake, publicKey}`
- `{kind: "addKey", publicKey, accessKey}`
- `{kind: "deleteKey", publicKey}`
- `{kind: "deleteAccount", beneficiaryId}`

Recognizing an action is not a claim that every execution is supported.
For example, runtime epoch limitations still stop staking/unstaking attempts
as documented in `near-lean/runtime/VERIFICATION.md`.

A receipt has `predecessorId`, `receiverId`, `receiptId` and `receipt`.
The payload is either `{kind: "data", dataId, data}` or
`{kind: "action", signerId, signerPublicKey, gasPrice, outputDataReceivers,
inputDataIds, actions}`. Output receivers are `[dataId, receiverId]` pairs.
Transactions have `signerId`, `publicKey`, `nonce`, `receiverId` and `actions`.
Signature verification remains external.

## Blocks and results

A block contains `blockHeight`, `blockTimestamp`, `epochHeight`, `gasPrice`,
`gasLimit` (u64 or `null`), `randomSeed` (32 bytes), `transactions` and
`incomingIndices`. Receipt delivery uses positions in the pending queue at
block start: `null` delivers all, `[]` defers all, and a list delivers those
original positions in that order. Missing/repeated positions reject the block
before transactions. Deferred work precedes newly outgoing receipts.

The result contains the initial state/pending queue, protocol version, code
catalogue labels/sizes, per-block trace, `stop`, `unrunBlocks` and `quiescent`.
A complete supplied sequence reports `blocksExhausted` even if receipts remain;
`quiescent` separately observes pending, delayed and postponed work. Schedule
errors and model execution issues record the rejected attempt and stop before
later blocks. Protocol action failures remain ordinary outcomes and allow
later supplied blocks to execute.

Each apply also exports `subsidizedAmount`, separately from burnt tokens.
Every represented outcome field is exported: id, executor, status, logs,
receipt ids, gas burnt and tokens burnt. Failures retain both the complete
Lean error constructor representation and its readable message. Native
compute counters, action error indices, gas metadata, trie roots and opaque
shard columns are not represented by this runtime output type. A comparison
must report these gaps explicitly; agreement of a chosen projection must
never be presented as full-runtime equivalence.

The serialized state and pending queue can seed another request with the same
catalogue. Tests check complete continuation trace equality, all state/queue
fields, all eight action encodings, an executed account create/deploy/call/key/
delete lifecycle, known/unknown deployment promises, rejected schedules and
malformed requests. CI also rebuilds the committed Wasm fixture with the
pinned `wasm-tools` version and checks its bytes.

Transaction objects now optionally carry `version` (0/1, default 0) and
`nonceMode` (`monotonic`/`strict`, default `monotonic`). V0 strict mode cannot
be encoded and is rejected. Ordinary-key V1 protocol/nonce admission is checked
by the runtime, preserving rejected-transaction outcomes and later valid batch
entries. Gas-key nonce indices remain unsupported.
