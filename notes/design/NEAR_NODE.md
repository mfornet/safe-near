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
  through it); only the node requires the node; the crypto package requires no
  repository package; no `@[extern]` /
  `@[implemented_by]` in our Lean and no native link settings in lakefiles;
  `NearNode.Protocol` matches `reference.json`.
- `just vm-dependencies`: the compiled NearVM import closure contains no
  `NearRuntime`, `NearChain`, `ChainReplay`, `NearNode`, `NodeBench` or (until the open point
  below is settled) `NearCrypto` module.
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
Ed25519 and secp256k1 signatures in Lean. M2a is the hashes and Ed25519, M2b secp256k1 (with the VM's
`ecrecover`), BLAKE2b, ristretto255 and the VRF; M2c (ML-DSA-65) is still to come.

- **Package.** `NearCrypto` requires nothing from this repository and no Mathlib, so contract builds
  are unaffected and `NearVM` can adopt it later without pulling the node in; `just node-isolation`
  enforces it. The VM keeps taking its digests, `ed25519Verify` and `ecrecover` as host parameters. The node
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
  | BLAKE2b-256/512, HMAC-SHA256 | RFC 7693 over lists; RFC 2104 over the `Spec` SHA-256 | the 12 rounds unrolled on 16 registers (`scripts/gen_blake2b.py`); HMAC over the `Impl` SHA-256 |
  | secp256k1 | `Nat`, Jacobian points, one shared double-and-add chain, Fermat inversion, the C library's formulas for ECDSA | ten 26-bit limbs (`scripts/gen_fp.py`), Jacobian points with lazy reduction (`scripts/gen_point_ops.py`), GLV endomorphism with four NAF streams, binary gcd inversion of scalars (`scripts/gen_modinv.py`) |
  | ristretto255, VRF | RFC 9496 over the Ed25519 `Spec`, the VRF of `vrf.rs` over `Nat` | the Ed25519 limbs and points; `Ext.doubleMul` for two arbitrary points |

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
- **secp256k1 acceptance.** `near-crypto` 0.37.4 reaches `libsecp256k1` (the C sources vendored in
  `secp256k1-sys` 0.8.2, `depend/secp256k1/src`) through `secp256k1` 0.27.0. The Lean `verify`
  (`Signature::verify`, `signature.rs:1086`), `recover` (`Secp256K1Signature::recover`, `signature.rs:979`)
  and `sign` (`SecretKey::sign`, `signature.rs:792`) match:
  1. **Keys** are the 64 bytes `x ‖ y`, given tag `04` and parsed by `secp256k1_eckey_pubkey_parse`
     (`eckey_impl.h:17`): `x, y < p` (`fe_set_b32` rejects `≥ p`) and on the curve. The parser also
     takes 33 bytes `02`/`03` (`ge_set_xo_var`: `x³ + 7` needs a root, the one of the stated parity)
     and 65 bytes `06`/`07` whose parity matches the tag; any other tag or length fails, and the
     origin is off the curve.
  2. **Signatures** are `r ‖ s ‖ v` (65 bytes). `v` must be 0 to 3 (`RecoveryId::from_i32`, `recovery.rs:39`)
     and `r, s < n` (`ecdsa_recoverable_signature_parse_compact`, `recovery/main_impl.h:38`); zeros
     parse and fail later. The message must be exactly 32 bytes (`Message::from_slice`) and is
     reduced modulo `n`, never rejected.
  3. **Verification** (`secp256k1_ecdsa_verify`, `secp256k1.c:381`; `ecdsa_sig_verify`, `ecdsa_impl.h:207`)
     rejects a **high `s`** (`s > (n-1)/2`) before anything else, needs `r, s ≠ 0`, and accepts when
     `x(s⁻¹ m G + s⁻¹ r Q) mod n = r`. The id `v` only has to be in range. `s' = n - s` with the
     other `v` does not verify, although it recovers the same key.
  4. **Recovery** (`ecdsa_sig_recover`, `recovery/main_impl.h:87`) needs `r, s ≠ 0`; for `v ≥ 2` it fails
     when `r ≥ p - n` and takes the abscissa `r + n`; the point has the parity `v & 1` (no root: fails);
     `Q = r⁻¹ (s R - m G)`; infinity fails. It does not reject high `s`. Of the oracle's recoveries,
     198, 194, 39 and 39 succeed for `v` = 0, 1, 2, 3.
  5. **Signing** is `sign_ecdsa_recoverable` with `secp256k1_nonce_function_rfc6979` and no extra data
     (`secp256k1.c:402`, the HMAC-SHA256 DRBG of `hash_impl.h:215`): the nonce of attempt `c` is the
     `(c + 1)`-st output seeded with `sk ‖ (m mod n)`; an invalid nonce, `r = 0` or `s = 0` goes to
     the next attempt; `s` is made low and `v = 2 [R.x ≥ n] + (R.y odd xor s was high)`
     (`ecdsa_impl.h:277`). The public key is `d G`, uncompressed, without the tag. `near-crypto`
     panics on a message that is not 32 bytes and on an invalid secret; Lean returns `none`.
  Lean reproduces every vector of the oracle (below), and the Spec was written from the C code before
  the Impl (the Python tests then recompute the oracle's keys, signatures and recoveries with plain
  integers).
- **`ecrecover`.** The VM host function (`near-vm-runner` 0.37.4, `logic.rs:1713`) traps unless
  `sig` is 64 bytes, `v < 4`, `hash` is 32 bytes and the flag is 0 or 1 (errors of the VM, kept there), then
  returns 0 unless `check_signature_values(flag != 0)` (`signature.rs:960`: `r < n` and `s < n`, or
  `s < n/2 + 1` with the flag) passes and `recover` succeeds, and otherwise writes the 64-byte key to the
  register and returns 1. `NearCrypto.ecrecover hash sig v malleability : Option ByteArray` is that last
  step for arguments the VM has checked; M3 maps it to `NearState.host.ecrecover`. The oracle calls the
  same two public `near-crypto` functions on the VM's well-formed arguments (it does not run the VM):
  1478 lines, 809 recovering, with both flags on every case that recovers, including the high-`s` ones
  that only the flag rejects.
- **VRF.** `near-crypto` `vrf.rs` over ristretto255 (`curve25519-dalek` 4.1.3 `ristretto.rs`); Lean follows
  it: `offset = H256(pk ‖ input)`, `x = sk + offset`, value `enc(B / x)` (`1 / 0 = 1`), `k = H512(x)`,
  `c = H256(pk ‖ value ‖ enc(k B) ‖ enc((k / x) B))`, proof `(k - c x) ‖ c`; verification needs the
  value to decode, `r` and `c` canonical (`< ℓ`, `Scalar::from_canonical_bytes`) and
  `H256(pk ‖ value ‖ enc((r + c offset) B + c pk) ‖ enc(r value + c B)) = c`. `H256` is
  `Blake2bVar::new(32)`, not a prefix of BLAKE2b-512. Ristretto decoding accepts only an even `s < p`
  (bit 255 rejects) whose `v (1 + s²)²` is a nonzero square and gives `t` even and `y ≠ 0`
  (RFC 9496 section 4.3.1, `decompress`); the encoder is `compress`; the Spec is the RFC and the Impl
  agrees on the 16 multiples of the base point of RFC 9496 appendix A. A block producer's VRF key is the
  ristretto form of its ed25519 key if that decodes as an Edwards point and is torsion free
  (`key_conversion.rs`, `convert_public_key`), its secret the clamped scalar of the seed reduced modulo `ℓ`
  (`convert_secret_key`). nearcore 2.13.4 checks each block with `verify_block_vrf`
  (`chain/chain/src/signature_verification.rs:12`: `convert_public_key(...).unwrap()` then
  `is_vrf_valid(prev.random_value, value, proof)`) and requires the header's `random_value` to be
  the SHA-256 of the value (`chain.rs`, `get_block_metadata` in `near-primitives` `utils.rs:481` computes it);
  Lean has `blockVrfValid` and `randomValue`. The M1 block fixtures hold random bytes in these fields
  (the oracle draws `vrf_value`, `vrf_proof` and `random_value` independently), so there is nothing to
  check on them; `vrf.jsonl` has ten `block` lines made by nearcore's own validator signer instead.
- **Not constant time.** Verification handles public data and the arithmetic is variable time (`Nat`
  scalars, NAF with branches on digits, `isZero` tests inside the additions). `sign` for Ed25519 and for
  secp256k1, and the VRF's `compute`, are correct but neither constant time nor hardened:
  signing with the validator's secret key needs a constant-time implementation (secret-independent
  scalar multiplication and recoding, nonce handling) before the node signs on a hostile network. Open
  for M8. Nothing in the node signs yet.
- **Fixtures.** `tools/node-conformance` `crypto-fixtures` writes `near-lean/crypto/fixtures/`
  (reproducible; 3.6 MB): 567 hash vectors (the classic ones, 59 random lengths around every block and
  padding boundary up to 20000 bytes, all-zero and all-ones messages at the boundaries, one million
  `a`; BLAKE2b at 32 and 64 bytes added), 831 Ed25519 lines: 28 key derivations (RFC 8032 and
  `near-crypto` seeds), 13 key-pair checks, 29 `near-crypto` signatures, 233 key decodings and 528
  verifications (bit flips in `R`, `S` and `A`, `S + kℓ`, the `S` boundary, the ZIP 215 matrix, the
  identity key, small-order keys with an accepting `R` found by search, and mixed-order keys `A + T`
  that verify when `k ≡ 0 mod 8`), 5964 secp256k1 lines and 1876 ristretto and VRF lines.
  secp256k1: 16 secret keys (0, `n`, `n ± 1`, ...), 45 key derivations (small and edge scalars, 5
  `near-crypto` seeds, random), 151 signatures (edge messages `0`, `n - 1`, `n`, `2²⁵⁶ - 1`, ...), 875 key
  parses (valid in all forms, wrong tags and lengths, `x ≥ p`, off-curve, bit flips), 1820 recoveries
  (all four ids on valid signatures and on small `r`, `r` and `s` over the 16 edge values, `r` around
  `p - n`, high `s`, wrong message, `v` 4, 5, 255 and -1), 1579 verifications (170 accepted: bit flips of
  `r`, `s`, the key and the message, other lengths, `v` 0 to 7 and 255, high `s`, `r + n`, `s + n`, edge `r` and
  `s`, keys off the curve) and 1478 `ecrecover` lines. Ristretto and VRF: 273 decodings (the multiples of the
  base point, `s = p + k`, odd `s`, random strings), 29 base multiples, 60 double products, 17 keys, 269
  ed25519 key conversions (identity, the eight torsion points, `y ≥ p`, mixed-order, random), 93
  value and proof computations, 847 verifications (24 accepted: wrong input, other key, bits of value and
  proof, `r + ℓ`, `c + ℓ`, swapped halves, zero proof, odd and non-decodable values) and 10 block lines.
  `tools/tests/test_crypto_fixtures.py` checks the files and cross-checks the SHA-2 and BLAKE2b digests
  with `hashlib`, the secp256k1 keys, signatures and recoveries and the RFC 9496 multiples with plain
  Python integers.
- **Signatures in the M1 fixtures.** The Borsh fixtures do not hold the key of an approval, a header or
  an endorsement, and they stay byte for byte as they were, so the oracle writes
  `near-lean/node/fixtures/signatures.jsonl` beside them (the signatures and keys it made, per
  line, 65-byte signatures and 64-byte keys for SECP256K1). `node-conformance-types` verifies in Lean 4229
  recorded signatures found in their lines (306 of them secp256k1) and recomputes 1577 from the decoded
  values (transaction, delegate, block and chunk hashes, approvals, endorsements, partial witnesses,
  contract messages, spice data; 123 secp256k1) under the key in the value, the recorded key or the
  line's signer. ML-DSA is skipped (M2c). A Python test verifies the recorded secp256k1 signatures
  independently.
- **Representation by benchmark.** The first `Impl` kept field elements as `Nat` below `p`: a product
  and one `%` cost 280 ns (the fold of the high half cost 900 ns), and Ed25519 verification 1.44 ms and
  signing 1.1 ms. Ten limbs of 25.5 bits on unboxed `UInt64` registers cost 53 ns a product and 30 ns a
  square, and verification fell to 0.2 ms. Scalars stay `Nat` for Ed25519: a few operations per signature.
  For secp256k1, ten 26-bit limbs cost 58 ns a product and 38 ns a square, an inversion 8.9 µs. Three
  measurements shaped the rest. The `Nat` extended Euclidean algorithm for scalars took 68 µs (30% of a
  verification, 614 ns per `Nat` product and `%`); the binary algorithm on four unboxed limbs takes 8 µs,
  is checked against the `Nat` algorithm on every call and serves the VRF scalars too. The endomorphism
  `λ (x, y) = (β x, y)` (the split of `secp256k1_scalar_split_lambda`) halves the doublings: verification
  fell from 293 to 148 µs and recovery from 296 to 173 µs. Combining the terms of each point formula
  before reducing (generated with checked bounds, `PointOps`) took a scalar multiplication from 120 to
  107 µs; carrying all limbs in two parallel passes was no faster and was not kept. BLAKE2b over an
  array took 6.6 µs for 64 bytes; unrolled on registers 0.9 µs.
- **Performance** (this development machine, 4 cores, release builds, mean time per call, best of
  three runs; the Lean column is `node-bench`, the native one `crypto-bench` in `tools/node-conformance`
  on the crates nearcore uses, `sha2` without SHA-NI here; the 64-byte hash rows include per-call setup):

  | | Lean | native | Lean / native | old `Near.Sha256` |
  |---|---|---|---|---|
  | SHA-256 64 B / 1 KiB / 64 KiB | 1.16 µs / 6.7 µs / 380 µs | 0.63 / 5.2 / 311 µs | 1.8 / 1.3 / 1.2 | 11.0 µs / 63 µs / 3.9 ms |
  | SHA-512 64 B / 1 KiB / 64 KiB | 1.02 µs / 5.1 µs / 250 µs | 0.30 / 2.5 / 138 µs | 3.4 / 2.0 / 1.8 | |
  | Keccak-256 64 B / 1 KiB / 64 KiB | 1.43 µs / 7.1 µs / 390 µs | 0.45 / 3.4 / 198 µs | 3.2 / 2.1 / 2.0 | |
  | Keccak-512 64 B / 1 KiB / 64 KiB | 1.23 µs / 11.7 µs / 687 µs | 0.44 / 6.2 / 370 µs | 2.8 / 1.9 / 1.9 | |
  | RIPEMD-160 64 B / 1 KiB / 64 KiB | 2.1 µs / 15.3 µs / 902 µs | 0.50 / 3.9 / 229 µs | 4.2 / 3.9 / 3.9 | |
  | BLAKE2b-256 64 B / 1 KiB / 64 KiB | 0.84 µs / 3.0 µs / 161 µs | 0.19 / 1.4 / 81 µs | 4.3 / 2.1 / 2.0 | |
  | BLAKE2b-512 64 B / 1 KiB / 64 KiB | 0.82 µs / 3.0 µs / 169 µs | 0.20 / 1.3 / 81 µs | 4.1 / 2.2 / 2.1 | |
  | Ed25519 verify (100 B message) | 201 µs | 40.6 µs | 5.0 | |
  | Ed25519 sign, key pair decoded each time | 300 µs | 42.5 µs | 7.1 | |
  | Ed25519 sign, key prepared | 144 µs | 20.3 µs | 7.1 | |
  | secp256k1 recover (32 B hash) | 164 µs | 44.7 µs | 3.7 | |
  | secp256k1 verify (32 B hash) | 151 µs | 36.1 µs | 4.2 | |
  | secp256k1 sign (32 B hash) | 111 µs | 34.2 µs | 3.3 | |
  | VRF compute with proof (32 B input) | 476 µs | 69.9 µs | 6.8 | |
  | VRF verify (32 B input) | 432 µs | 83.5 µs | 5.2 | |

  The new SHA-256 is 9.5 to 10 times faster than the list-based one the node used. The numbers vary by
  up to 20% (secp256k1 recovery by a factor of 1.9 between two runs) on this shared machine. The native
  SHA-256 is the portable software one; a CPU with SHA extensions makes the `sha2` crate several times
  faster, which pure Lean cannot match. The native secp256k1 and Ed25519 use 64-bit limbs with
  128-bit products and large precomputed tables; the Lean code cannot (no 128-bit product), which is
  part of the remaining factor.
- **Proposed targets for M2** (from these measurements; the current code meets them): every hash within
  5x of the native crate at 1 KiB and 64 KiB (SHA-256 within 1.5x there, since every node hash goes
  through it; BLAKE2b within 2.5x), Ed25519 verification within 6x (at most 0.25 ms, about 5,000 per
  second per core), signing within 10x; secp256k1 verification and recovery within 5x (at most 0.2 ms,
  about 5,000 per second per core, the rate an `ecrecover`-heavy contract needs), signing within 4x; the
  VRF within 7x (at most 0.5 ms; nodes verify one per block). Open work with known levers, none of
  which changes a `Spec`: for Ed25519 avoid the carries of `add` and `sub` where the next product
  tolerates wide limbs (done for secp256k1 in the point formulas), convert field elements to bytes
  without `Nat`, fixed-base comb tables for signing and the VRF; for secp256k1 a table of the variable
  point with a shared denominator (`ge_globalz_set_table_gej`) and a wider window for the base point; and
  batch verification of the many signatures of a block. The matching targets for M4 (trie) and M10 remain
  open below.
- **Still to come.** M2c: ML-DSA-65 (verification of the PQ keys and signatures that `near-crypto` accepts).
  The `Merkle` row of the layer table stays in the node (M1 already has `merklize`).

## Open points

- Numeric performance targets for M4 and M10, measured against nearcore (M2's are proposed above).
- Whether crypto host functions in `NearVM` slow contract verification. If they
  do, `NearVM` takes host crypto as a parameter and the node supplies it. Today the VM takes its
  digests, `ed25519Verify` and `ecrecover` as parameters; `NearCrypto` is a separate package it can import later.
