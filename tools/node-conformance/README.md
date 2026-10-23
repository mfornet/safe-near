# Node type conformance oracle

The Borsh oracle for the NEAR node's `near-primitives` types (milestone M1 of
`notes/design/NEAR_NODE.md`). `node-conformance-fixtures` links the published
nearcore crates pinned in `Cargo.toml` and `Cargo.lock`
(`near-primitives`, `near-crypto`, `near-primitives-core` at `=0.37.4`, the
crates of nearcore 2.13.4 and protocol 86 in `near-lean/runtime/reference.json`),
builds values of every type in scope, and writes their bytes. It refuses to run
unless the crates' `PROTOCOL_VERSION` is 86 and equals `reference.json`. As for the
configuration crates, equality of the published crates with the clean nearcore
revision is not assumed.

## Regenerating

```sh
cd tools/node-conformance
cargo run --release --locked --bin node-conformance-fixtures -- ../../near-lean/node/fixtures/types
```

The output is a pure function of the code and the locked crates: a second run
produces identical files. The fixtures are committed and **CI never builds this
crate**; the Lean side reads only the committed files. Regenerate when the pin
moves or a type is added, and commit the result with the pin change.

Requirements: Rust 1.93.1 (`rust-toolchain.toml`) and network access to crates.io
on the first build.

## Fixture format

`manifest.json` records the protocol version, the nearcore release, the crates, the
seed and the number of accepted and rejected lines per type. Each type has one
`<Type>.jsonl`; one JSON object per line:

```json
{"type":"Transaction","name":"rand-3","borsh":"<hex>","hash":"<hex>"}
{"type":"Transaction","name":"rand-3/trunc","borsh":"<hex>","reject":true}
```

- `borsh`: the input bytes. Accepted lines are produced by `borsh::to_vec` on a value and have
  been decoded and re-encoded to the same bytes by the pinned crates. Rejected lines
  (`"reject":true`) are inputs the crates' `try_from_slice` rejects (truncation, a flipped
  byte, tag `0xff`, trailing bytes, plus hand-written cases such as invalid UTF-8, a bad
  `bool`, invalid account ids and the Ed25519 signature check).
- `hash`: the derived hash, or `null` when the type has none. `Transaction` and
  `SignedTransaction`: the transaction hash (SHA-256 of the Borsh `Transaction`).
  `SignedDelegateAction` and `VersionedSignedDelegateAction`: the NEP-461 hash the delegate
  action is signed under (`get_nep461_hash`).
  `ExecutionOutcomeWithId`: the hash of the Borsh `Vec<CryptoHash>` returned by
  `to_hashes()`; its `hashes` field is the concatenation of those hashes.
- M1b derived values, one hex field each (the Lean test computes every field present on a line and
  fails on one it does not know): `innerHash` (block header: `compute_inner_hash`; chunk header:
  hash of the Borsh inner part), `hash` (block hash; chunk hash; `BlockBody::compute_hash`;
  `Challenge` and `OptimisticBlock` hash; `ChunkExecutionResult` hash; `ShardChunk` and
  `PartialEncodedChunk` chunk hash; `ReceiptProof`: hash of the `ReceiptList`; `HashList` and
  `BytesList`: `merklize` root; `ValidatorStakes`: `compute_bp_hash_from_validator_stakes` with the
  versioned format, `hashV1` without), `paths` (Borsh `Vec<MerklePath>` of `merklize`), `root`
  (`ReceiptProof`: root its proof reaches from the hash of `hash`; `EncodedShardChunkBody`: merklize
  root of the parts, present only when every part is), `sigData` (`Approval::get_data_for_sig`,
  and the spice endorsement signing data), and on `Block`: `bodyHash` (V3 and V4), `stateRoot`,
  `receiptsRoot`, `chunkHeadersRoot`, `chunkHeadersPaths`, `txRoot`, `outcomeRoot` and `validity`
  (one byte: 0 for `check_validity` Ok, then `InvalidStateRoot`, `InvalidReceiptRoot`,
  `InvalidChunkHeaderRoot`, `InvalidTransactionRoot`, `InvalidChunkMask`). `PartialMerkleTree`:
  `hash` (root), `wellFormed` and `inserted` (Borsh tree after inserting `sha256([7])`).
  Chunk and block hashes are not on the wire; decoding recomputes them, so every line also checks
  that. The oracle is built in release mode: `prev_state_root` of a spice (V6) chunk is the zero
  hash there, a debug assertion otherwise.
- `canonical`: present when the input is accepted but re-encodes to other bytes (the profile
  data decoders pad or truncate their arrays, and a `BTreeMap` decodes unsorted input).

Names ending in `/trunc`, `/half`, `/flip<n>`, `/tag255` and `/trailing` are mutations of the
named value, classified by the crates. Values are the hand-written edge cases (every enum
variant at least once, empty and large vectors, `u128::MAX`, every key type, nested
delegate actions, every receipt kind) and seeded random ones. ED25519 and SECP256K1
signatures are real. ML-DSA-65 signing is randomised, so those signatures are seeded random
bytes of the right length; Borsh does not verify them.

`just node-conformance-types` decodes every line with the Lean `Impl` and `Spec` Borsh codecs,
re-encodes with both, and compares with the fixture and with the derived hashes.
