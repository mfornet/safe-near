# NEAR node

A full NEAR validator node written in Lean. It runs in a localnet next to
`neard` and both make progress together (SAF-8).

## Requirements

- **Exact protocol.** The node implements the protocol version pinned in
  `near-lean/runtime/reference.json`, without simplifications. It is a full
  validator: it produces blocks and chunks, sends approvals and endorsements,
  and the chain needs its stake for finality.
- **Pure Lean.** Large parts of the protocol are to be verified, so everything
  that can be written in Lean is.
- **Performance.** The node must keep pace with `neard` as a real peer.
- **Isolation.** Contract verification compile time is unaffected. A developer
  working only on contract verification never builds the node.

## Layers

| Package | Library | Responsibility |
|---|---|---|
| `near-lean/crypto` | `NearCrypto` | Hashes, signatures, curves, VRF, Merkle |
| `near-lean/node` | `NearNode` | Wire types, chain, epochs, consensus, network, storage |
| `tools/node-conformance` | (Rust) | nearcore oracle pinned to `reference.json` |

`NearNode` depends on `NearChain`, `NearRuntime`, `NearVM` and `NearCrypto`. Nothing depends on
`NearNode`. `NearCrypto` depends on nothing in the repository (not even Mathlib), so `NearVM`
can adopt it later.

## Rules

1. **No custom native code.** No `@[extern]` and no `@[implemented_by]` in our
   sources. The only native code is Lean's own runtime, including the libuv
   binding (`Std.Internal.UV.TCP`) used for networking. It sits behind a
   `NearNode.Net` interface because that API is internal to Lean.
2. **Spec and Impl.** Hot paths (field arithmetic, hashing, trie, Borsh) have a
   simple `Spec` used in proofs and a fast pure-Lean `Impl`. They are linked by
   equivalence theorems, or `@[csimp]` once proved. Until then, differential
   tests check that they agree.
3. **Import isolation.** Nothing node-only enters the `Wasm` or `NearVM`
   import closure. `just vm-dependencies` enforces this.
4. **Pinned oracle.** Every acceptance test compares against the nearcore
   revision in `reference.json`. Bumping the protocol bumps oracle and node
   together.

## Trusted base

The Lean kernel and compiler, the Lean runtime and libuv, and the C toolchain
that builds them.

## Milestones

Each milestone is done when its `just` target passes locally and in CI.

| | Linear | Scope | Depends on | Acceptance |
|---|---|---|---|---|
| M0 | SAF-14 | Guardrails and harness | — | `just node-guardrails` |
| M1 | SAF-15 | Borsh and all `near-primitives` types | M0 | `just node-conformance-types` |
| M2 | SAF-16 | Crypto in pure Lean | M0 | `just crypto-tests` |
| M3 | SAF-17 | Complete runtime | M2 | `just chain-replay-corpus` |
| M4 | SAF-18 | Trie and storage | M1 | state roots on M3 corpus, restart test |
| M5 | SAF-19 | Chain and epoch manager | M1, M2, M4 | `just chain-validate-corpus` |
| M6 | SAF-20 | P2P networking | M1, M2 | `just localnet-peer` |
| M7 | SAF-21 | Syncing observer | M3–M6 | `just localnet-follow` |
| M8 | SAF-23 | Validator | M7 | `just localnet-validator` |
| M9 | SAF-22 | RPC and operability | M6 | RPC conformance suite |
| M10 | SAF-24 | Performance and soak | M8 | `just localnet-soak` |

The detailed acceptance criteria live in each Linear issue.

### M0 gates

`just node-guardrails` runs all three:

- `just node-isolation` (Python only, in automatic CI): no contract
  verification package requires the node or chain packages, even
  transitively (the runtime is allowed: contract adapters run the binary
  through it); only the node requires the node; no `@[extern]` /
  `@[implemented_by]` in our Lean and no native link settings in lakefiles;
  `NearNode.Protocol` matches `reference.json`.
- `just vm-dependencies`: the compiled NearVM import closure contains no
  `NearRuntime`, `NearChain`, `ChainReplay`, `NearNode` or `NodeBench` module.
- `just verification-buildtime`: copies `contracts/w-near/verification` and its
  local packages to a fresh directory (sharing built mathlib), builds it, and
  fails if it is more than 5% slower than this machine's entry in
  `tools/verification-buildtime/baseline.json`. Record an entry with
  `--record`. The baseline builds `Model Spec`, because `Proofs.Refinement`
  still imports the removed Talos decoder; switch to the default targets once
  that is ported.

`just node-bench [--filter S] [--out FILE]` runs the benchmarks and prints a
JSON report (the crypto ones are described under M2 below). The Rust oracle
`tools/node-conformance` arrived with M1.

### M1 types

`just node-conformance-types` checks every Borsh type against fixtures from
the pinned nearcore crates.

- **Borsh.** `NearNode.Borsh` has a reference semantics over `List UInt8`
  (`Spec`) and a fast path over `ByteArray` (`Impl`). A type defines its codec
  once, from shared combinators (struct as tuple, tagged enum, `Vec`, `Option`,
  `BTreeMap`), and gets both. The decoders reject truncation, bad tags, bad
  `bool`, invalid UTF-8 and, in `decodeAll`, trailing bytes. Until the
  per-combinator equivalence theorems exist, the test decodes and encodes
  every fixture with both.
- **Oracle.** `tools/node-conformance` links `near-primitives`, `near-crypto`
  and `near-primitives-core` `=0.37.4` and refuses to run unless the protocol
  is 86. It writes `near-lean/node/fixtures/types/<Type>.jsonl` and
  `manifest.json` (one line: type, name, hex Borsh, derived hash, or `reject`).
  The files are committed; CI never builds the crate.
- **Covered (M1a).** Scalars, `CryptoHash`, `AccountId`, keys and signatures,
  accounts and access keys, every action and the delegate actions,
  transactions V0 and V1, receipts and their state-stored forms, execution
  outcomes with metadata and profiles, proofs, and the error trees reachable
  from `ExecutionStatus`.
- **Covered (M1b).** `ValidatorStake` (V1 is the only version) and
  `ValidatorStakeV1`; `Approval`, `ApprovalInner`, `ApprovalMessage` with
  `get_data_for_sig`; `BlockHeader` V1 to V7 over `BlockHeaderInnerLite` and
  `BlockHeaderInnerRest` V1 to V7; `Block` V1 to V4 and `BlockBody` V1 to V3
  (V3 is the spice body); `ShardChunkHeader` V1 to V3 over inner V1 to V6;
  `ShardChunk`, `EncodedShardChunk`, `PartialEncodedChunk` (V1, V2),
  `ReceiptProof`, `ShardProof`; `CongestionInfo`, `BandwidthRequests`,
  scheduler state; `ChunkExtra` V1 to V5; challenges and the spice
  endorsement and execution-result types; `Tip`, `OptimisticBlock`,
  `PartialMerkleTree`, `StateSyncInfo`. Derived values are checked against the
  oracle: block hash and inner hash for every header version, chunk hash per
  header version, approval and spice signing bytes, `merklize` roots and
  proofs, the block's chunk roots, block body hash, `check_validity`, the
  block-producer-set hash, receipt proof roots and the encoded chunk merkle
  root. The block producer signs the block hash, so there are no other signing
  bytes.
- **Covered (M1c).** Stateless validation: `ChunkEndorsement` (V2, tag 1),
  `ChunkStateWitness` (V2) with `ChunkStateTransition`, the partial encoded
  witnesses V1 and V2, `ChunkContractAccesses`, `ContractCodeRequest` and
  `Response` V1 and V2, `PartialEncodedContractDeploys`,
  `StoredChunkStateTransitionData`, the SPICE witness, partial data and
  contract messages, with their signing bytes (checked against real signatures
  by the oracle) and production keys. Epochs: `EpochInfo` V1 to V5 with
  `StakeWeightedIndex`, `ValidatorMandates` and `ShardLayout` V0 to V3,
  `BlockInfo` V1 to V5, `EpochSummary`, `EpochSyncProof`. Their pure functions
  are checked at 46 heights: `sample_block_producer`, `sample_chunk_producer`,
  `sample_chunk_validators` (a pure Lean `ChaCha20Rng` with the `rand` 0.8
  `gen_range` and `shuffle`), the alias tables, the mandate price and
  `ValidatorMandates::new`. State sync: `ShardStateSyncResponseHeader` V1, V2,
  `ShardStateSyncResponse` V1 to V4, `StatePart`, request keys and
  acknowledgements, plus `PeerId`, `AnnounceAccount` and `GenesisId`. The zstd
  frames (`EncodedChunkStateWitness`, `CompressedContractCode`,
  `CompressedEpochSyncProof`, `StatePartV1`) are opaque bytes until M2 needs a
  decoder.
- **Not covered.** Storage-layer types, which M4 brings with the trie and
  columns: `TrieKey`, `ValueRef`, `FlatStateValue`, the state change types,
  `ReceiptToTxInfo`, `ProcessedReceiptMetadata`, `ChunkApplyStats` (debug
  statistics), `PromiseYieldStatus`; the RPC-only `StoreKey`, `StoreValue` and
  `FunctionArgs`; and the serialize-only `SignableMessage` and
  `OptimisticBlockKeySource`.

**M1 complete.** Every Borsh type of `near-primitives` reachable from blocks,
chunks, the network, stateless validation, epochs and state sync round-trips
with the crates on every fixture, and every derived value in scope matches the
oracle.

### M2 crypto

`just crypto-tests` builds `near-lean/crypto` (`NearCrypto`) and runs `crypto-conformance` (every
oracle vector against both the `Spec` and the `Impl` of each primitive) and `crypto-differential`
(`Spec` against `Impl` on seeded random inputs). `just node-conformance-types` now also verifies
Ed25519 signatures in Lean.

- **Package.** `NearCrypto` requires nothing from this repository and no Mathlib, so contract builds
  are unaffected and `NearVM` can adopt it later without pulling the node in; `just node-isolation`
  enforces it. The VM keeps taking its digests and `ed25519Verify` as host parameters. The node
  requires it by path: `CryptoHash.hash` (so every block, chunk and outcome hash and the sampler
  seeds) is the `NearCrypto` SHA-256 `Impl`. Pure Lean throughout, no `@[extern]`.
- **Spec and Impl.** Each primitive has a `Spec`, simple and close to the standard (lists, `Nat`,
  constants derived from their definitions), and a fast `Impl`:

  | | `Spec` | `Impl` |
  |---|---|---|
  | SHA-256, SHA-512 | FIPS 180-4 over lists; `K` and `H0` from roots of primes | `ByteArray` in, block function unrolled onto `UInt32`/`UInt64` registers (`scripts/gen_sha.py`) |
  | Keccak-256/512 | FIPS 202 permutation on 25 lanes; offsets and round constants derived | unrolled round on 25 registers |
  | RIPEMD-160 | the two 80-step lines over lists | one loop on `UInt32` registers |
  | Ed25519 | `Nat` and projective points (`add-2008-bbjlp`), Fermat inversion | ten 25.5-bit limbs (`scripts/gen_fe.py`), extended coordinates, width-5 and width-7 NAF with Shamir's trick |

  Keccak is the original padding (`0x01`), not SHA-3's, as `sha3::Keccak256`/`Keccak512` in the VM.
  The `Spec`/`Impl` agreement is a differential test for now (every fixture, every length 0 to 300 for
  each hash, random keys, signatures and field elements including limb boundaries); equivalence
  theorems come later.
- **Ed25519 acceptance.** `near-crypto` 0.37.4 `Signature::verify` (`signature.rs`) calls
  `ed25519_dalek::VerifyingKey::from_bytes` and then the non-strict `Verifier::verify`
  (`ed25519-dalek` 2.2.0, `verifying.rs`; `curve25519-dalek` 4.1.3; the `legacy_compatibility` feature
  is off in the locked build). The Lean `verify` matches:
  1. The key is decoded by `CompressedEdwardsY::decompress` (`edwards.rs`): bit 255 is the sign, `y` is
     the other 255 bits **mod p with no canonical check** (`y ≥ p` is accepted), `x² = (y²-1)/(dy²+1)`
     must have a root, and `x = 0` with the sign bit set is accepted (ZIP 215). Small-order and
     mixed-order keys are accepted.
  2. `S` must be below `ℓ` (`check_scalar` in `signature.rs`, `Scalar::from_canonical_bytes`).
  3. `compress([S]B - [k]A)` must equal the 32 bytes of `R` as given (`RCompute::finish`): the check is
     cofactorless, and a non-canonical `R` can never match, so it is rejected.
  4. `k = SHA-512(R ‖ A ‖ M) mod ℓ` with `A` the key bytes as given.
  5. `near-crypto`'s Borsh decoder also rejects a signature whose last byte has any of its top three
     bits set (`BorshDeserialize for Signature`); that sits in the node's codec, not in `verify`.
  The 196 ZIP 215 vectors (14 small-order encodings as key and as `R`, `S = 0`) have 12 accepts and 184
  rejects in the oracle, and Lean reproduces each. Keys are the 64-byte `ED25519SecretKey` (seed, then
  public key); `sign` is RFC 8032 (SHA-512 of the seed, clamp, `a` reduced mod `ℓ`); a key pair whose
  public half is not the derived one, byte for byte, is `none` where `near-crypto` panics
  (`from_keypair_bytes`).
- **Not constant time.** Verification handles public data and the arithmetic is variable time (`Nat`
  scalars, NAF with branches on digits). `sign` is correct but neither constant time nor hardened:
  signing with the validator's secret key needs a constant-time implementation (secret-independent
  scalar multiplication and recoding) before the node signs on a hostile network. Open for M8.
- **Fixtures.** `tools/node-conformance` `crypto-fixtures` writes `near-lean/crypto/fixtures/`
  (reproducible; 0.7 MB): 405 hash vectors (the classic ones, 59 random lengths around every block and
  padding boundary up to 20000 bytes, all-zero and all-ones messages at the boundaries, one million
  `a`) and 831 Ed25519 lines: 28 key derivations (RFC 8032 and `near-crypto` seeds), 13 key-pair
  checks, 29 `near-crypto` signatures, 233 key decodings and 528 verifications (bit flips in `R`, `S`
  and `A`, `S + kℓ`, the `S` boundary, the ZIP 215 matrix, the identity key, small-order keys with an
  accepting `R` found by search, and mixed-order keys `A + T` that verify when `k ≡ 0 mod 8`).
  `tools/tests/test_crypto_fixtures.py` checks the files and cross-checks SHA-2 against `hashlib`.
- **Signatures in the M1 fixtures.** The Borsh fixtures do not hold the key of an approval, a header or
  an endorsement, and they stay byte for byte as they were, so the oracle writes
  `near-lean/node/fixtures/signatures.jsonl` beside them (the signatures and keys it made, per
  line). `node-conformance-types` verifies in Lean 3923 recorded signatures found in their lines and
  recomputes 1454 from the decoded values (transaction, delegate, block and chunk hashes, approvals,
  endorsements, partial witnesses, contract messages, spice data) under the key in the value, the
  recorded key or the line's signer. ML-DSA and secp256k1 are skipped.
- **Representation by benchmark.** The first `Impl` kept field elements as `Nat` below `p`: a product
  and one `%` cost 280 ns (the fold of the high half cost 900 ns), and Ed25519 verification 1.44 ms and
  signing 1.1 ms. Ten limbs of 25.5 bits on unboxed `UInt64` registers cost 53 ns a product and 30 ns a
  square, and verification fell to 0.2 ms. Scalars stay `Nat`: a few operations per signature.
- **Performance** (this development machine, 4 cores, release builds, mean time per call; the Lean
  column is `node-bench`, the native one `crypto-bench` in `tools/node-conformance` on the crates
  nearcore uses, `sha2` without SHA-NI here):

  | | Lean | native | Lean / native | old `Near.Sha256` |
  |---|---|---|---|---|
  | SHA-256 64 B | 1.16 µs | 0.65 µs | 1.8 | 11.0 µs |
  | SHA-256 1 KiB | 6.7 µs | 5.2 µs | 1.3 | 63 µs |
  | SHA-256 64 KiB | 386 µs | 304 µs | 1.3 | 3.9 ms |
  | SHA-512 64 B / 1 KiB / 64 KiB | 1.03 µs / 5.1 µs / 250 µs | 0.31 / 2.5 / 139 µs | 3.4 / 2.1 / 1.8 | |
  | Keccak-256 64 B / 1 KiB / 64 KiB | 1.35 µs / 7.0 µs / 393 µs | 0.44 / 3.3 / 201 µs | 3.1 / 2.1 / 2.0 | |
  | Keccak-512 64 B / 1 KiB / 64 KiB | 1.21 µs / 12.1 µs / 730 µs | 0.43 / 6.3 / 371 µs | 2.8 / 1.9 / 2.0 | |
  | RIPEMD-160 64 B / 1 KiB / 64 KiB | 2.1 µs / 15.1 µs / 893 µs | 0.48 / 3.8 / 228 µs | 4.4 / 3.9 / 3.9 | |
  | Ed25519 verify (100 B message) | 202 µs | 41 µs | 4.9 | |
  | Ed25519 sign, key pair decoded each time | 376 µs | 42 µs | 8.9 | |
  | Ed25519 sign, key prepared | 156 µs | 19.6 µs | 8.0 | |

  The new SHA-256 is 9.5 to 10 times faster than the list-based one the node used. The numbers vary by
  up to 20% between runs on this shared machine. The native SHA-256 is the portable software one; a
  CPU with SHA extensions makes the `sha2` crate several times faster, which pure Lean cannot match.
- **Proposed targets for M2** (from these measurements; the current code meets them): every hash within
  5x of the native crate at 1 KiB and 64 KiB (SHA-256 within 1.5x there, since every node hash goes
  through it), Ed25519 verification within 6x (at most 0.25 ms, about 5,000 per second per core), signing
  within 10x. A faster `Ed25519` is open work with known levers: avoid the carries of `add` and `sub`
  where the next product tolerates wide limbs, convert field elements to bytes without `Nat`, a
  fixed-base table for signing, and batch verification of the many signatures of a block, none of which
  changes the `Spec`. The matching targets for M4 (trie) and M10 remain open below.
- **Still to come.** M2b: secp256k1 (`ecrecover`, ECDSA verification) and the VRF of `near-crypto`'s
  `vrf.rs`. M2c: ML-DSA-65. The `Merkle` row of the layer table stays in the node (M1 already has
  `merklize`).

## Open points

- Numeric performance targets for M4 and M10, measured against nearcore (M2's are proposed above).
- Whether crypto host functions in `NearVM` slow contract verification. If they
  do, `NearVM` takes host crypto as a parameter and the node supplies it. Today the VM takes its
  digests and `ed25519Verify` as parameters; `NearCrypto` is a separate package it can import later.
