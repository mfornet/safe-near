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

`near-primitives` is built with its `rand` feature, which `EpochInfo::sample_chunk_validators` needs.

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
- M1c derived values (one field each, hex; an empty string means that nearcore panics or overflows, or
  that the oracle skips a case that would allocate without bound, and the Lean function returns
  `none`):
  - Signed stateless messages (`ChunkEndorsement`, the partial witnesses, the contract-distribution
    messages, `SpicePartialData`, ...): `sigData`, the bytes the signature covers. nearcore does not
    expose them, so the oracle signs with a real ED25519 key, asserts that the crate's `verify`
    accepts the signature, and emits the Borsh prefix before it (`SpicePartialData`: that prefix and
    the Borsh string `"SpicePartialData"`). `ChunkEndorsement` also has `metaSigData` (the metadata
    signature) and `key` (the `ChunkProductionKey`); `ChunkStateWitness`: `key` and `ack`. `HashMap`
    fields decode in any key order, so the witnesses have unsorted and repeated-key cases.
    `CodeHashes`: `compute_contract_accesses_hash`.
  - `ShardLayout`: `version`, `numShards`, `shardIndexes` and `shardIds` (Borsh `Vec<Option<u64>>`
    of `get_shard_index` over shard ids 0..7, 1000, 2000, `u64::MAX` and `get_shard_id` over 0..7)
    and `accountShards` (`account_id_to_shard_id` over six accounts and the layout's boundaries).
  - `EpochInfo`: `validatorAccounts` (Borsh `Vec<AccountId>`), `validatorIds` (`get_validator_id` of
    each validator and two others), `bp` (`sample_block_producer`) and `cp` (`sample_chunk_producer`
    for each shard of the layout, then three more shard ids, over each height), both Borsh
    `Vec<Option<u64>>` over the 46 heights of `sample_heights` (`epoch_fam.rs`, the same list as
    `NodeConformance/Epoch.lean`), and `cv` (`sample_chunk_validators`, Borsh of the results at every
    seventh of those heights). V1 to V4 have no layout of their own: the shard id is the index.
    `cv` is empty for a mandates config of more than 4096 shards or 10^6 mandates.
  - `StakeWeights` (`Vec<u128>`): `hash`, the Borsh `StakeWeightedIndex::new`. `StakeWeightedIndex`:
    `samples`, `sample` of the SHA-256 of 0..39. `MandatesInput` (config and validators, with at most
    64 shards and a target of at most 1000): `hash`, the Borsh `ValidatorMandates::new`.
    `RngCase` (a seed and a count of 1 to 4096): `u32s`, `u64s` (`ChaCha20Rng` words), `range`
    (`gen_range(0..n)`) and `shuffle` (the shuffle of 0..n, then the next `u64`).
  - `BlockInfo`: `hash`, `height`, `prevHash`, `epochId`, `isGenesis`.
    `EpochSyncProofLastEpochData`: `hash`, `compute_epoch_sync_data_hash`.
  - State sync: `StateRootNode` and `ShardStateSyncResponseHeader`: `numParts`
    (`get_num_state_parts`; empty where the sum overflows, as nearcore is built with overflow
    checks and this crate is not); the header also `heightIncluded` and `prevStateRoot`;
    `StatePart`: `payloadLength` and `partialState` (`to_partial_state` of an uncompressed part,
    with the entry limit; empty for a compressed one, which needs zstd);
    `ShardStateSyncResponse`: `partId` and `payloadLength`; `AnnounceAccount`: `hash`.
  The compressed types (`EncodedChunkStateWitness`, `CompressedContractCode`,
  `CompressedEpochSyncProof`, `StatePartV1`) are zstd frames made by the crates and stay opaque.
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

## Crypto oracle (M2)

`crypto-fixtures` writes the fixtures of `near-lean/crypto` (milestone M2). It uses the same
locked crates, plus the ones nearcore's VM and `near-crypto` use directly: `sha2` 0.10.9,
`sha3` 0.10.9 (`Keccak256`, `Keccak512`, the legacy padding), `ripemd` 0.1.3, `ed25519-dalek`
2.2.0 and `curve25519-dalek` 4.1.3 (the last two with the feature set `near-crypto` builds).

```sh
cd tools/node-conformance
cargo run --release --locked --bin crypto-fixtures -- ../../near-lean/crypto/fixtures
```

The output is a pure function of the code and the locked crates: two runs give identical files.
`manifest.json` lists the crates and the number of lines of each kind. `just crypto-tests` checks
all of it in Lean; CI never builds this crate.

- `hash.jsonl`: `{"alg", "name", "msg", "digest"}` for `sha256` (through `CryptoHash::hash_bytes`),
  `sha512`, `keccak256`, `keccak512` and `ripemd160`: the classic vectors, random messages of 59
  lengths around every block and padding boundary (0 to 20000 bytes), all-zero and all-ones
  messages at those boundaries, and one million `a`, spelled `{"unit", "count"}` instead of `msg`.
- `ed25519.jsonl`, one object per line, by `kind`. The verdicts are those of
  `near_crypto::Signature::verify`, which is `ed25519_dalek::VerifyingKey::from_bytes` followed by
  the non-strict `Verifier::verify` (no `legacy_compatibility` feature); key decoding is checked
  with `VerifyingKey::from_bytes` itself.
  - `keypair`: `seed`, `public`, `keypair` (`near-crypto`'s 64-byte `ED25519SecretKey`: seed then
    public key): the five RFC 8032 seeds, edge seeds and random ones.
  - `keypair-check`: `keypair`, `valid`: `SigningKey::from_keypair_bytes` accepts only when the
    public half is the derived one, byte for byte.
  - `sign`: `seed`, `public`, `msg`, `sig` by `near_crypto::SecretKey::sign` (deterministic).
  - `verify`: `public`, `msg`, `sig`, `valid`. Per signature: wrong message, a flipped bit in
    `R`, in `S` (including the top bits) and in the key, another key, `S + kℓ` for `k` up to 15,
    swapped halves; the scalar boundary (`S` = 0, ℓ-1, ℓ, ℓ+1, 2^253-1, 2^256-1); the ZIP 215
    matrix (196 vectors: the 14 encodings of the 8 small-order points, canonical or not, as both
    key and `R`, `S` = 0, message `Zcash`); the identity key (accepts every message); small-order
    keys with a real accepting `R` found by search; mixed-order keys `A + T` that verify when
    `k ≡ 0 (mod 8)` and fail otherwise.
  - `pubkey`: `public`, `valid`: key decoding, including `y ≥ p`, `x = 0` with the sign bit set,
    the small-order encodings and 120 random strings.

`crypto-bench` times the same primitives natively (release mode, `std::time`, at least 0.3 s each)
and prints one JSON line per benchmark; the names match `node-bench`:

```sh
cargo run --release --locked --bin crypto-bench
```
