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
bytes of the right length (none is valid; `signatures.jsonl` records the verdict `false`); Borsh does not
verify them.

`just node-conformance-types` decodes every line with the Lean `Impl` and `Spec` Borsh codecs,
re-encodes with both, and compares with the fixture and with the derived hashes.

### Signature records

The Borsh fixtures do not carry the key of most signatures (an approval, a block header, an
endorsement, ...), so `node-conformance-fixtures <out dir> [signatures file]` also writes
`signatures.jsonl` (default `<out dir>/../signatures.jsonl`, that is
`near-lean/node/fixtures/signatures.jsonl`) and leaves the type files byte for byte unchanged.
`sigs.rs` records every ED25519 signature the oracle makes (`G::sign`, the spice endorsements, the
signed stateless messages) and the key of every validator signer; each accepted line that is not a
mutation or a hand-written byte string gets one record:

```json
{"type":"Approval","line":12,"name":"rand-3","sigs":[{"sig":"<64 B>","public":"<32 B>","msg":"<hex>"}],"signers":["<32 B>"]}
```

`line` is the 0-based position in `<type>.jsonl` (names repeat within a file). `sigs` are the
signatures made while the value was built, with the key and message; `signers` are the keys of
validator signers whose signatures nearcore's constructors make internally (a `ChunkEndorsement`,
the partial witnesses, the contract messages), which the Lean side tries for the signatures of that
value. Lines of a mutation are not recorded: their signatures are no longer valid. A value built
once and reused in several lines is recorded with the first line only.

`just node-conformance-types` verifies the signatures with `NearCrypto`: every recorded signature
found in a line's bytes, and, for the signed types, the signatures recomputed from the decoded value
(transaction and delegate hashes, block and chunk hashes, the Borsh of an `inner`), with the key from
the value or the record. ED25519 and SECP256K1 signatures are checked (the records hold 64-byte
signatures with 32-byte keys, and 65-byte ones with 64-byte keys). The ML-DSA-65 "signatures" are random
bytes (see above) and are recorded too, with a 1952-byte key and `valid`, the verdict of
`Signature::verify`, which is `false`; Lean must reach the same verdict. Real ML-DSA signatures are in the
crypto fixtures (`mldsa.jsonl`).

## Crypto oracle (M2)

`crypto-fixtures` writes the fixtures of `near-lean/crypto` (milestone M2). It uses the same
locked crates, plus the ones nearcore's VM and `near-crypto` use directly: `sha2` 0.10.9,
`sha3` 0.10.9 (`Keccak256`, `Keccak512`, the legacy padding), `ripemd` 0.1.3, `blake2` 0.10.6,
`ed25519-dalek` 2.2.0, `curve25519-dalek` 4.1.3 and `secp256k1` 0.27.0 (with the feature set
`near-crypto` builds; its `libsecp256k1` is the C code of `secp256k1-sys` 0.8.2), and for ML-DSA-65
`aws-lc-rs` 1.16.2 (`aws-lc-sys` 0.39.1), which `near-crypto`'s `MLDSA65` key type calls.

```sh
cd tools/node-conformance
cargo run --release --locked --bin crypto-fixtures -- ../../near-lean/crypto/fixtures
```

The output is a pure function of the code and the locked crates: two runs give identical files.
`manifest.json` lists the crates and the number of lines of each kind. `just crypto-tests` checks
all of it in Lean; CI never builds this crate.

- `hash.jsonl`: `{"alg", "name", "msg", "digest"}` for `sha256` (through `CryptoHash::hash_bytes`),
  `sha512`, `keccak256`, `keccak512`, `ripemd160`, `blake2b256` (`Blake2bVar::new(32)`) and
  `blake2b512`: the classic vectors, random messages of 59
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

- `secp256k1.jsonl` (`src/crypto_secp.rs`), by `kind`; keys are `near-crypto`'s 64 bytes `x ‖ y`,
  signatures its 65 bytes `r ‖ s ‖ v`, and the verdicts those of `near_crypto::Signature::verify`
  (`verify`), `secp256k1::PublicKey::from_slice` (`pubkey`), `SecretKey::from_slice` (`secret`),
  `ecdsa::RecoverableSignature::from_compact` and `recover_ecdsa` (`recover`, with `v` as any `i32`,
  checked against `Secp256K1Signature::recover` for `v < 4`) and, for `ecrecover`,
  `Secp256K1Signature::check_signature_values` followed by `recover` as the VM's `ecrecover` does for
  well-formed arguments (`near-vm-runner` is not linked; its body is read, not run):
  - `secret`: `secret`, `valid`. `keypair`: `secret`, `public`, `compressed`: edge scalars, five seeds
    of `SecretKey::from_seed(SECP256K1, ..)` and random keys. `sign`: `secret`, `public`, `msg`, `sig`
    by `SecretKey::sign` (deterministic RFC 6979).
  - `pubkey`: `bytes`, `valid`, and for valid ones `public` and `compressed`: the forms of each key,
    other tags and lengths, hybrid forms with either parity, flipped bits, `x` over the edge values
    (`p`, `p + 1`, `2^256 - 1`), small `x` and random strings.
  - `recover`: `msg`, `sig` (`r ‖ s`), `v`, `valid`, `public`: valid signatures with every id, high `s`,
    wrong message, `v` 4, 5, 255 and -1, `r` and `s` over the 16 edge values (`0`, `n`, `p - n`, ...), small
    `r` (the abscissae `r` and `r + n`), `r` around `p - n`, random.
  - `verify`: `public`, `msg`, `sig`, `valid`: per signature wrong message and lengths, every `v`,
    high `s` with either `v`, another key, flipped bits of `r`, `s` and the key, `r + n`, `s + n`; edge
    `r` and `s`; keys that are not points.
  - `ecrecover`: `hash`, `sig` (64 bytes), `v`, `malleability` (0 or 1), `valid`, `public`.
- `vrf.jsonl` (`src/crypto_vrf.rs`), by `kind`: `ristretto` (`bytes`, `valid`, `double`: decoding by
  `CompressedRistretto::decompress`), `basemul` and `vmul2` (products encoded), `key` (an ed25519 seed,
  its public key, the VRF secret `convert_secret_key` derives and the VRF public key), `convert`
  (`convert_public_key` of 32-byte strings), `compute` (`compute_vrf_with_proof`), `vrf-public` and
  `vrf-secret` (decoding of keys), `verify` (`is_vrf_valid`) and `block` (a nearcore
  `ValidatorSigner`'s VRF over a previous random value, and its SHA-256).

- `shake.jsonl` (`src/crypto_mldsa.rs`): `{"kind": "shake", "alg", "name", "msg", "outLen", "digest"}` for
  SHAKE128 and SHAKE256 of `sha3` 0.10.9: messages of 0 to 4096 bytes around the rates (168 and 136) and
  outputs from 1 byte to 5000, every output length around the first blocks, and one million `a`; and
  `sha3_256` (`Sha3_256`, the padding `0x06`, which `near-crypto` applies to public keys) on messages around
  its rate of 136.
- `mldsa.jsonl` (`src/crypto_mldsa.rs`), by `kind`. `near-crypto` 0.37.4 `MLDSA65` is `aws-lc-rs`: keys are
  `PqdsaKeyPair::from_seed` (the 32-byte FIPS 204 seed, `ml_dsa_65_from_seed` is private so the oracle makes the
  same two calls) and `from_raw_private_key` (`SecretKey::from_str`, `SecretKey::sign`), a signature is
  `PqdsaKeyPair::sign` (`EVP_DigestSign`, pure mode, empty context, 32 fresh random bytes), and
  `Signature::verify` is `UnparsedPublicKey::new(&ML_DSA_65, pk).verify` (empty context). Signing is never
  reproducible, so the oracle calls the C function under it with the randomness chosen
  (`ml_dsa_65_sign_internal`, declared by hand because `aws-lc-sys` does not bind it; the symbol name carries
  the crate version) and checks with `near-crypto` that each signature verifies. Verdicts are those of
  `near_crypto::Signature::verify` for 1952-byte keys and 3309-byte signatures, and of `aws-lc-rs` for other
  lengths (asserted equal where both apply).
  - `keygen`: `name`, `seed`, `public` (1952 bytes), `secret` (4032 bytes, `ρ ‖ K ‖ tr ‖ s1 ‖ s2 ‖ t0`).
  - `secret`: `secret`, `valid`, and `public` when valid: what `from_raw_private_key` accepts: the keys
    above, a flipped bit in `K` (accepted), `ρ`, `tr` or `t0`, nibbles 9 and 15 in `s1` and `s2` (out of the
    range `[-4, 4]`), an in-range change of one coefficient, other lengths.
  - `handle`: `key` (or a literal `public`), `handle`: `MlDsa65PublicKey::to_public_key_handle`, the SHA3-256
    of `near:ml-dsa-65-pubkey-hash:v1` and the key, which names an ML-DSA access key in the trie.
  - `sign`: `key` (a `keygen` name), `msg` (or `unit` and `count`), `rnd` (all-zero for the deterministic
    variant), `sig`; includes signatures with the most hints found by search.
  - `verify`: `key` or a literal `public`, `msg`, `sig`, `valid`: per base signature a changed message
    (flipped, extended, truncated), another key, bit flips in `c~`, `z` and the hint, `z` coefficients at
    and next to the bound `γ1 - β`; malformed hints on a real prefix (unsorted, duplicate, decreasing or
    over-large counts, nonzero padding, a full hint of 55 indices); other lengths of signature and key;
    garbage signatures; and the other modes of FIPS 204 (non-empty contexts of 1, 3 and 255 bytes, no
    domain prefix, HashML-DSA with SHA-256, ExternalMu) that `near-crypto` must reject, with one that it
    accepts (ExternalMu of the pure `μ`).

- `bn254.jsonl`, `bls12381.jsonl`, `p256.jsonl` (`src/crypto_bn.rs`, `src/crypto_bls.rs`,
  `src/crypto_p256.rs`; `src/crypto_vm.rs` is the harness): the verdicts are those of `near-vm-runner`
  0.37.4's own `VMLogic` host functions (`alt_bn128_g1_multiexp`, `alt_bn128_g1_sum`,
  `alt_bn128_pairing_check`, the nine `bls12381_*`, `p256_verify`), run over a flat memory under
  the free configuration of the current protocol; `zeropool-bn` 0.5.11, `blst` 0.3.11 and `p256` 0.13.2 only build
  the valid points and signatures. A line is `{"kind", "name", "input", "ok", "output" | "result"}` for BN254
  (`ok = false` is a trap of the host function, `output` the 64 bytes written, `result` the pairing check's
  boolean), `{"kind", "name", "input", "v0", "v1"}` for BLS12-381 (`v0`: `bls12381_not_in_group_fix` off, as at
  protocol 86; `v1`: on, NEP-488; each is `{"trap": true}`, `{"ret": 1}` or `{"ret": 0 | 2, "output"?}`) and
  `{"kind", "name", "sig", "msg", "pk", "ok", "result"}` for P-256. Inputs: valid points, sums and
  products (up to 64 points), infinity in every position, repeated and opposite points, non-canonical
  field elements, off-curve points, points of `E'` outside `G2`, points outside `G1` (accepted by the
  sums, rejected by multiexp and pairing), the order-3 points `(0, ±2)`, flag combinations, wrong lengths,
  pairing checks that hold and that do not, field elements where the SSWU denominator vanishes, and
  signatures with every edge of `ecdsa` 0.16.9's parsing and `p256_verify`'s order of checks.

`crypto-bench` times the same primitives natively (release mode, `std::time`, at least 0.3 s each)
and prints one JSON line per benchmark; the names match `node-bench`. The pairing-friendly curves and
P-256 run the host functions themselves, on inputs taken from the committed fixtures, and
`crypto-bench curves` runs only those:

```sh
cargo run --release --locked --bin crypto-bench
```
