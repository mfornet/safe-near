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
| M4 | SAF-18 | Trie and storage | M1 | `just node-state-roots`, `just node-store-tests` |
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
(`Spec` against `Impl` on seeded random inputs). `just node-conformance-types` also verifies
Ed25519, secp256k1 and ML-DSA-65 signatures in Lean. M2a is the hashes and Ed25519, M2b secp256k1 (with the VM's
`ecrecover`), BLAKE2b, ristretto255 and the VRF, M2c SHAKE128/256, SHA3-256 and ML-DSA-65: M2 is complete
(acceptance at the end of this section).

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
  | SHAKE128/256, SHA3-256 | FIPS 202 over lists on the `Keccak.Spec` permutation, any output length | the unrolled round; a sponge that squeezes block by block (`Xof`), and the state lanes themselves for the samplers |
  | ML-DSA-65 | FIPS 204 over `Int` arrays: algorithms 41/42 for the NTT with zetas as powers of 1753, bit-list encodings, doubling SHAKE streams | flat `UInt32` arrays, Montgomery products, zetas in Montgomery form, rounding on residues, branch-free reductions, group packers |

  Keccak is the original padding (`0x01`), not SHA-3's, as `sha3::Keccak256`/`Keccak512` in the VM; SHAKE
  (`0x1f`) and SHA3-256 (`0x06`) are the FIPS 202 paddings on the same permutation.
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
- **ML-DSA-65 acceptance.** `near-crypto` 0.37.4 implements `MLDSA65` with `aws-lc-rs` 1.16.2 (feature
  `unstable`), which binds AWS-LC through `aws-lc-sys` 0.39.1; AWS-LC's ML-DSA is `mldsa-native`, FIPS 204
  final, not a draft (`aws-lc/crypto/fipsmodule/ml_dsa/`). The Lean code matches, with the calls it follows:
  1. **Verification** is `UnparsedPublicKey::new(&ML_DSA_65, pk).verify(msg, sig)` (`signature.rs:1126`), that
     is `EVP_DigestVerify` (`evp/p_pqdsa.c`, `pkey_pqdsa_verify_generic`, the raw mode) and `ml_dsa_65_verify`
     with an **empty context** (`ml_dsa.c:358`): pure ML-DSA, `M' = 0x00 ‖ 0x00 ‖ M`. A signature made in another
     mode is rejected: a non-empty context, HashML-DSA, no domain prefix, `ExternalMu` for another `μ` (the
     `ExternalMu` signature of the pure `μ` is accepted, being the same signature).
  2. `mld_sign_verify_internal` (`mldsa/sign.c:976`) rejects, in effect: a signature that is not 3309 bytes;
     a malformed hint (`mld_unpack_hints`, `mldsa/packing.c:192`: a cumulative count that decreases or
     exceeds `ω = 55`, indices within a polynomial not strictly increasing, a nonzero byte after the last
     index); `‖z‖∞ ≥ γ1 - β = 524092`; and `c~ ≠ H(μ ‖ w1Encode(UseHint(h, Az - c t1 2^d)), 48)` with
     `μ = H(H(pk, 64) ‖ M', 64)`. The public key is only unpacked, so any 1952 bytes are a key (every 10-bit
     `t1` is valid); `UnparsedPublicKey` rejects other key lengths. `near-crypto`'s own types fix the lengths
     (1952, 3309) and Borsh enforces them, so a verify of other lengths cannot occur in the node; Lean returns
     `false` for them, as `aws-lc-rs` does.
  3. **Keys.** `SecretKey::from_str` (`signature.rs:917`) and `SecretKey::sign`/`public_key` (`:805`, `:828`)
     call `PqdsaKeyPair::from_raw_private_key` on the 4032 bytes `ρ ‖ K ‖ tr ‖ s1 ‖ s2 ‖ t0`
     (`PQDSA_KEY_set_raw_private_key`, `pqdsa/pqdsa.c:137`, then `mld_sign_pk_from_sk`, `sign.c:1423`), which
     accepts only if every `s1`, `s2` coefficient is within `[-4, 4]` (nibbles 0 to 8; 9 to 15 are rejected) and
     `t0` and `tr` equal the ones recomputed from `ρ`, `s1`, `s2`; `K` is not checked (a changed `K` gives
     another valid key with the same public key). `NearCrypto.mlDsa65PublicKey` returns that public key or
     `none`. The seed constructor `ml_dsa_65_from_seed` is private to `near-crypto`; it is
     `PqdsaKeyPair::from_seed` (`ML-DSA.KeyGen_internal` with the 32-byte `ξ`, `ρ ‖ ρ' ‖ K = H(ξ ‖ 6 ‖ 5)`) and
     the raw export, and `mlDsa65KeyGen` is that.
  4. **Signing** is `PqdsaKeyPair::sign` (`signature.rs:808`): `EVP_DigestSign`, pure mode, empty context, with
     32 fresh random bytes `rnd` (hedged, `ml_dsa_65_sign`, `ml_dsa.c:289`). No public API takes `rnd`, so a
     signature is never reproducible; the oracle calls the function under it, `ml_dsa_65_sign_internal`
     (`ml_dsa.c:330`, which takes the prefix `0x00 0x00` and `rnd`), declared by hand in the oracle, and
     checks with `near-crypto` that each signature verifies. Lean's `sign sk msg rnd` equals it byte for byte
     (all 54 fixtures, `rnd` zero for the deterministic variant of FIPS 204 and random otherwise). The loop is
     algorithm 7 with `ρ'' = H(K ‖ rnd ‖ μ)`, the nonce `κ` stepping by `ℓ = 5`, and at most 13106 attempts
     (`MLD_NONCE_UB`) before `mldsa-native` fails; the Lean code returns `none` there (never reached).
  5. **Encodings** are FIPS 204's: `pk = ρ ‖ SimpleBitPack(t1, 10 bits)`, `z` 20 bits per coefficient
     (`γ1 - z`), `w1` 4 bits, the hint as 55 index bytes then 6 cumulative counts.
  6. `MlDsa65PublicKey::to_public_key_handle` (`signature.rs:166`), the trie's name for an ML-DSA access key, is
     `SHA3-256("near:ml-dsa-65-pubkey-hash:v1" ‖ pk)`: `NearCrypto.mlDsa65PublicKeyHandle`.
  Three implementations agree on every vector: AWS-LC (the oracle), Lean (`Spec` and `Impl`), and
  `tools/tests/mldsa_reference.py`, FIPS 204 in plain Python integers, which recomputes all keys, signatures
  and 282 verdicts.
- **Not constant time.** Verification handles public data and the arithmetic is variable time (`Nat`
  scalars, NAF with branches on digits, `isZero` tests inside the additions). `sign` for Ed25519 and for
  secp256k1, and the VRF's `compute`, are correct but neither constant time nor hardened:
  signing with the validator's secret key needs a constant-time implementation (secret-independent
  scalar multiplication and recoding, nonce handling) before the node signs on a hostile network. Open
  for M8. Nothing in the node signs yet. The same holds for ML-DSA `keyGen` and `sign` (branches on secret
  data in the samplers, rejection checks and array indexing); `verify` handles public data only. A validator
  signs with Ed25519, so ML-DSA signing matters to wallets, not to the node.
- **Fixtures.** `tools/node-conformance` `crypto-fixtures` writes `near-lean/crypto/fixtures/`
  (reproducible; 6.9 MB, of which M2c is 3.4 MB and the files of M2a and M2b are unchanged): 567 hash vectors (the classic ones, 59 random lengths around every block and
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
  M2c: 364 SHAKE and SHA3 vectors (SHAKE128 177, SHAKE256 164, SHA3-256 23: messages of 0 to 4096 bytes with
  the lengths `rate - 2` to `rate + 2` and multiples of the rate, outputs from 1 byte to 5000 around one and
  several blocks, one million `a`) and 401 ML-DSA-65 lines: 12 keys from seeds (zeros, ones, counting, 9
  random), 39 raw secret keys (4 accepted: as generated and a changed `K`; 35 rejected: bits of `ρ`, `tr`,
  `t0`, nibbles 9 and 15 in `s1` and `s2`, an in-range changed coefficient, zeros, ones, other lengths), 54
  signatures with chosen randomness (messages of 0, 3, 32, 100, 1000, 4096 and 100000 bytes; `rnd` zero or
  random; two found by search for the most hints), 14 public key handles and 282 verifications (13 accepted:
  the 10 base signatures, one of them with the key given literally, the pure empty-context signature of
  the mode tests and the `ExternalMu` signature of the pure `μ`; 269 rejected: another message
  (flipped, extended, truncated) or key, bits of `c~`, `z` and the hint, `z` coefficients at, inside and
  beyond `±(γ1 - β)`, 16 malformed or odd hints on each of two real prefixes (unsorted, duplicate, decreasing counts,
  counts 56 and 255, nonzero padding, 55 indices), signature lengths 0, 3308, 3310 and 6618, key lengths
  0, 1951 and 1953, a key of zeros and of ones, garbage signatures, and signatures of the other FIPS 204
  modes: contexts of 1, 3 and 255 bytes, no domain prefix, HashML-DSA-SHA-256, `ExternalMu` as a message).
  `tools/tests/test_crypto_fixtures.py` checks the files and cross-checks the SHA-2, BLAKE2b, SHAKE and
  SHA3 digests and the public key handles with `hashlib`, the secp256k1 keys, signatures and recoveries and
  the RFC 9496 multiples with plain Python integers, and every ML-DSA key, signature and verdict with
  `mldsa_reference.py`. `manifest.json` also names `aws-lc-rs`; the oracle depends on it, and on `bs58`, to
  build the ML-DSA keys the way `near-crypto` does.
- **Signatures in the M1 fixtures.** The Borsh fixtures do not hold the key of an approval, a header or
  an endorsement, and they stay byte for byte as they were, so the oracle writes
  `near-lean/node/fixtures/signatures.jsonl` beside them (the signatures and keys it made, per
  line, 65-byte signatures and 64-byte keys for SECP256K1). `node-conformance-types` verifies in Lean 4239
  recorded signatures found in their lines (306 of them secp256k1) and recomputes 1580 from the decoded
  values (transaction, delegate, block and chunk hashes, approvals, endorsements, partial witnesses,
  contract messages, spice data; 123 secp256k1) under the key in the value, the recorded key or the
  line's signer. A Python test verifies the recorded secp256k1 signatures independently.
  **ML-DSA in the M1 fixtures.** ML-DSA signing is randomised, so the oracle's ML-DSA \"signatures\" there are
  seeded random bytes of the right length and none is valid; the Borsh fixtures stay as they were, and the
  oracle now records each one (13 checks: 10 found in their lines, 3 recomputed from the value) in
  `signatures.jsonl` with its 1952-byte key, its message and `valid`, the verdict of `near-crypto` (`false`).
  Lean verifies each with `NearCrypto.mlDsa65Verify` and must reach that verdict. Real ML-DSA signatures with
  verdicts are only in the crypto fixtures (`mldsa.jsonl`), made with chosen randomness.
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
  array took 6.6 µs for 64 bytes; unrolled on registers 0.9 µs. For ML-DSA-65 the first `Impl` verified in
  0.78 ms and generated a key in 0.88 ms, and a signature took 0.9 s: the compiler had moved the
  computation of an array that only a closure used (`c t0` in the hint loop) into the closure, so it ran 1536
  times. Handing the arrays to functions of their own (`makeHints`, `useHints`, `@[noinline]`) made a
  signature five attempts of 0.8 ms. The profile of a verification is then ExpandA 277 µs of 700
  (thirty polynomials at five SHAKE128 blocks each, 0.9 µs a permutation, plus the sampler), eighteen NTTs at
  11 µs, and packing and hashing for the rest. Sampling from the Keccak lanes (eight 3-byte candidates in
  three lanes) instead of a 168-byte block took ExpandA to 185 µs, packing `w1` in groups instead of with a
  generic bit accumulator took 45 µs to 5 µs, and verification fell to 0.53 ms. Branch-free reductions and
  literal constants changed nothing measurable: an NTT is 11 µs, 11 ns a butterfly, which is the cost of the
  array loads and stores (bounds checks, boxing) in the loop, and a radix-4 transform that halves them is the
  next lever.
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
  | SHAKE256, 1 KiB in, 32 B out | 7.5 µs | 3.75 µs | 2.0 | |
  | ML-DSA-65 key generation from a seed | 728 µs | 137 µs | 5.3 | |
  | ML-DSA-65 sign (100 B), key decoded and checked each time | 3.87 ms | 0.62 ms | 6.2 | |
  | ML-DSA-65 sign (100 B), key prepared | 3.05 ms | 0.50 ms | 6.1 | |
  | ML-DSA-65 verify (100 B) | 533 µs | 124 µs | 4.3 | |

  The new SHA-256 is 9.5 to 10 times faster than the list-based one the node used. The numbers vary by
  up to 20% (secp256k1 recovery by a factor of 1.9 between two runs) on this shared machine. The native
  SHA-256 is the portable software one; a CPU with SHA extensions makes the `sha2` crate several times
  faster, which pure Lean cannot match. The native secp256k1 and Ed25519 use 64-bit limbs with
  128-bit products and large precomputed tables; the Lean code cannot (no 128-bit product), which is
  part of the remaining factor. The ML-DSA rows compare with AWS-LC as `aws-lc-sys` builds it here (its
  own Keccak, `near-crypto`'s `SecretKey::sign` and `Signature::verify` for the "decoded each time" and
  verify rows, `PqdsaKeyPair::sign` for the prepared key); native signing draws fresh randomness and Lean
  signs 100-byte messages that differ in the first byte with fixed `rnd`, so a signing row is a mean over
  about five attempts of the rejection loop and varies by 20% between runs. SHAKE256 is the `sha3` crate.
- **Proposed targets for M2** (from these measurements; the current code meets them): every hash within
  5x of the native crate at 1 KiB and 64 KiB (SHA-256 within 1.5x there, since every node hash goes
  through it; BLAKE2b within 2.5x), Ed25519 verification within 6x (at most 0.25 ms, about 5,000 per
  second per core), signing within 10x; secp256k1 verification and recovery within 5x (at most 0.2 ms,
  about 5,000 per second per core, the rate an `ecrecover`-heavy contract needs), signing within 4x; the
  VRF within 7x (at most 0.5 ms; nodes verify one per block); SHAKE256 within 2.5x at 1 KiB; ML-DSA-65
  verification within 6x (at most 0.8 ms, about 1,250 per second per core; a transaction with an ML-DSA key
  carries 5.3 KB of key and signature, so bandwidth limits the rate first), key generation within 7x and
  signing within 8x (at most 5 ms; wallets sign, validators do not). Open work with known levers, none of
  which changes a `Spec`: for Ed25519 avoid the carries of `add` and `sub` where the next product
  tolerates wide limbs (done for secp256k1 in the point formulas), convert field elements to bytes
  without `Nat`, fixed-base comb tables for signing and the VRF; for secp256k1 a table of the variable
  point with a shared denominator (`ge_globalz_set_table_gej`) and a wider window for the base point; and
  batch verification of the many signatures of a block. For ML-DSA-65: a radix-4 NTT (half the array
  traffic), the NTT of `t1` kept per key by a node that sees one key often, and a 4-way Keccak is out of
  reach without SIMD. The matching targets for M4 (trie) and M10 remain open below.
- **M2 complete: `just crypto-tests`.** It builds `near-lean/crypto` with `--wfail`, runs `crypto-conformance`
  (10003 vectors, `Spec` and `Impl` each) and `crypto-differential` (130663 seeded comparisons), both
  with 0 failures; `just node-conformance-types` verifies the fixtures' signatures; the axiom audit of
  `near-lean/crypto` has 0 violations (no `sorry`, no axioms beyond the core ones). What the node and the
  runtime need from crypto, and where it is:

  | Primitive | Needed by | In `NearCrypto` |
  |---|---|---|
  | SHA-256 | `CryptoHash` (block, chunk, transaction, receipt, outcome hashes, Merkle trees, trie nodes), VM `sha256` | yes: the node's `CryptoHash.hash` is the `Impl`; the VM still passes its own digest |
  | Keccak-256, Keccak-512 | VM `keccak256`, `keccak512` | yes |
  | RIPEMD-160 | VM `ripemd160` | yes |
  | Ed25519 verify, sign | transactions, delegate actions, block headers and approvals, chunk headers, endorsements, state witnesses, contract messages, network handshake and announcements, VM `ed25519_verify` | yes; `sign` is not constant time (M8) |
  | secp256k1 verify, recover, sign | transactions with SECP256K1 keys, VM `ecrecover` | yes; `sign` is not constant time (M8) |
  | ML-DSA-65 verify | transactions with ML-DSA keys | yes |
  | ML-DSA-65 key generation, sign, secret-key check | wallets and tools, `SecretKey::from_str` | yes; not constant time |
  | SHA3-256 (public key handle) | the trie's name for an ML-DSA access key | yes (`mlDsa65PublicKeyHandle`) |
  | SHAKE128, SHAKE256 | inside ML-DSA | yes |
  | ristretto255, BLAKE2b-256/512, VRF compute and verify, key conversion | block production randomness (`verify_block_vrf`, `random_value`) | yes |
  | HMAC-SHA256, SHA-512 | RFC 6979 nonces, Ed25519 | yes |
  | `Merkle` (`merklize`, paths) | chunk, block and outcome roots | not crypto: the node (M1) |

  **Not in this package:** the VM keeps taking its digests, `ed25519Verify` and `ecrecover` as parameters until M3
  chooses to import `NearCrypto`. Reed-Solomon erasure coding (chunk parts) is not cryptography and is not here
  either; M6 confirms the network handshake needs nothing more than Ed25519. The pairing-friendly curves and P-256
  of the VM's host functions are M2d, below.

- **M2d: pairing-friendly curves and P-256.** `NearCrypto.Bn254` (`alt_bn128_g1_multiexp`, `alt_bn128_g1_sum`,
  `alt_bn128_pairing_check`), `NearCrypto.Bls12381` (the nine `bls12381_*` functions) and `NearCrypto.P256`
  (`p256_verify`), each a function from the host's input bytes to what the host writes or returns (`Except` for
  its traps, `none` for the BLS functions' return value 1), with a `Spec` and an `Impl`. The oracle is
  `near-vm-runner` 0.37.4's own `VMLogic` (`crypto_vm.rs`: a flat memory, the free configuration), not a
  reimplementation of its wrapping; `zeropool-bn` 0.5.11, `blst` 0.3.11 and `p256` 0.13.2 only build the inputs.
  The sources matched: `logic/alt_bn128.rs` (little-endian words; `Fq` below `q`, `Fr` below `r`; `G1` on the
  curve, `(0, 0)` infinity; `G2` on the twist **and** `[r] Q = O`), `logic/bls12381.rs` (ZCash flags; the flag `0x80`
  rejected on uncompressed input; sums need only curve points, multiexp and pairing the prime-order group;
  returns 0, 1 or 2), `blst` `e1.c`/`e2.c`/`map_to_g1.c`/`map_to_g2.c`/`pairing.c`, and `logic/logic.rs:1900`
  (`p256_verify`) with `ecdsa` 0.16.9 `verify_prehash` (the message is the digest: under 16 bytes false, cut to 32;
  no low-`s` rule; a signature outside `[1, n-1]` answers false **before** the key length can trap).
  - **Structure.** `Pairing.Group` is one Jacobian implementation over a record of field operations (`Fp`, `Fp2`,
    any `a`); `Pairing.Spec` is the optimal ate pairing for both families as an `Fp12` of twelve coefficients, a
    Miller loop on the twist in affine coordinates with each line untwisted and multiplied as an ordinary element,
    and the final exponentiation as one power; `Pairing.Tower`/`Pairing.Impl` are the Karatsuba tower, one Miller
    loop for all pairs with Jacobian steps and thirteen-product sparse lines (D- and M-type twists), cyclotomic
    squaring, and the hard part from its expansion in `x` (BN: `λ₀ + λ₁p + λ₂p² + p³`; BLS:
    `((x-1)²/3)(x+p)(x²+p²-1) + 1`). The fast pairing equals the reference exactly, so the differential test
    compares reduced values, not only verdicts. Field elements stay `Nat`: a 381-bit product and `%` costs 0.4 µs, a
    Montgomery product on 26-bit limbs would cost about as much (225 + 225 limb products), and inversion is the
    extended Euclidean algorithm (4 µs; Fermat's 250 µs).
  - **Subgroup tests.** `G2` of BN254 by `ψ(Q) = [6x²] Q`: `deg([6x²] - ψ) = 36x⁴ + p - 6x²t = r`, so the kernel is
    exactly `G2` (the check the crate makes is `[r] Q = O`, which the reference does). BLS12-381 uses `blst`'s own
    tests (`σ²(P) = -[z²] P`, whose endomorphism has degree `r`, and `ψ(P) = [z] P` of Scott 2021) and the reference
    `[r] P = O`; the differential tests compare them on members, non-members and sums of both. `ψ`-based clearing of the
    `G2` cofactor, as `blst` does, equals `[h_eff]` on random curve points (also a differential test).
  - **NEP-488.** With `bls12381_not_in_group_fix` off (protocol 86) `p1_sum` and `p1_decompress` reject the order-3
    points `(0, ±2)`; on (protocol 155) they accept them. Both are fixtures (`v0`, `v1`) and a `version` argument.
  - **Hash to curve.** The isogeny constants are read out of `blst`'s sources by `scripts/gen_bls_isogeny.py`
    (`tools/tests/test_crypto_generated.py` regenerates them when the sources are in the cargo registry;
    `test_bls_isogeny.py` checks they define isogenies). The fast `G1` map takes one exponentiation
    (`sqrt(-g)` for the non-square case) and one inversion.
  - **Fixtures** (`bn254.jsonl` 336 lines: 110 multiexp, 91 sum, 135 pairing; `bls12381.jsonl` 883: 112 + 120
    multiexp, 109 + 113 sum, 88 + 88 decompress, 50 + 99 map, 104 pairing; `p256.jsonl` 215; 1.3 MB, the older
    files unchanged). Valid and invalid: wrong lengths, non-canonical and over-range field elements and scalars,
    off-curve points, points outside the groups, infinities, flags, opposite and repeated points, up to 64 points,
    pairings that hold and fail, the exceptional SSWU input, every `p256_verify` edge. `crypto-conformance` runs
    all of them on `Impl` and, within a size bound (and on one version unless the two differ), on `Spec`;
    `tools/tests/test_pairing_fixtures.py` recomputes a sample of every function in plain Python integers with
    `pairing_reference.py` and an RFC 9380 SSWU written again.
  - **Performance** (same machine as above, best of three; the native column is `crypto-bench curves`, the host
    functions themselves with `blst` built `portable` as `near-vm-runner` builds it; 2 pairs, 8 points):

    | | Lean | native | Lean / native |
    |---|---|---|---|
    | BN254 pairing check, 1 / 2 pairs | 19.2 / 28.1 ms | 2.95 / 4.24 ms | 6.5 / 6.6 |
    | BN254 `g1_multiexp` 1 / 8 points | 1.65 / 4.93 ms | 195 / 774 µs | 8.5 / 6.4 |
    | BN254 `g1_sum` 8 points | 145 µs | 13 µs | 11 |
    | BLS12-381 pairing check, 1 / 2 pairs | 17.0 / 22.2 ms | 0.89 / 1.32 ms | 19 / 17 |
    | BLS12-381 `p1_sum` / `p2_sum`, 8 points | 218 / 353 µs | 16 / 31 µs | 13 / 11 |
    | BLS12-381 `g1_multiexp` 1 / 8 points | 2.5 / 12.4 ms | 203 µs / 1.40 ms | 12 / 8.9 |
    | BLS12-381 `g2_multiexp` 1 / 8 points | 6.5 / 30.2 ms | 279 µs / 3.16 ms | 23 / 9.5 |
    | BLS12-381 `map_fp_to_g1` / `map_fp2_to_g2` | 1.40 / 3.64 ms | 61 / 185 µs | 23 / 20 |
    | BLS12-381 `p1_decompress` / `p2_decompress` | 258 / 656 µs | 21 / 39 µs | 12 / 17 |
    | P-256 `p256_verify` (32-byte digest) | 2.94 ms | 319 µs | 9.2 |

    The native BN254 crate is slow (`zeropool-bn`), so BN254 is the closest. Proposed targets (the code meets
    them): BN254 pairing checks within 8x, BLS12-381 pairing checks within 20x (about 25 ms for two pairs), sums,
    multiexp, decompression and `p256_verify` within 25x, the maps within 25x. Levers, none changing a `Spec`: the
    subgroup tests dominate multiexp (an eighth of a `G2` multiexp is its tests), a GLV/GLS split of the
    scalars, mixed additions from affine tables, lazy reduction in the tower, and an unboxed limb field once
    there is a 128-bit product.
  - **Open.** Nothing here is constant time (all inputs are public). The host functions' gas is the VM's
    (M3). `p256_verify` and the BLS functions take the arguments after the VM's own length and memory checks.

### M3 runtime

Acceptance is `just chain-replay-corpus`: the Lean runtime replays real protocol-86 chunks and matches what nearcore
2.13.4 produced, byte for byte. M3a builds the corpus and the harness; later stages close the gaps the harness
reports. Rebuild steps and formats: [`tools/localnet/CORPUS.md`](../../tools/localnet/CORPUS.md).

- **Why a localnet, why the full state.** Gas depends on the trie nodes a chunk touches, so replay needs the real trie
  shape; public RPC cannot give trie nodes. A Merkle-Patricia trie is a function of its key/value set, so the complete
  raw state of a shard before a chunk rebuilds the original trie (the oracle checks the root). A neard built from the
  pinned revision (`tools/localnet/build.py`: release, the revision's toolchain, `--locked`, metadata recorded) runs a
  1-validator/1-shard and a 2-validator/4-shard localnet at protocol 86, driven by a seeded workload (transfers,
  named, NEAR- and ETH-implicit accounts, keys, contracts and host functions, promises, yield, stake, deletion,
  delegation, global contracts, gas keys, delayed receipts, epoch boundaries).
- **Bundle.** Per new chunk: all pre-state entries of its shard, transactions and incoming receipts in apply order,
  the `ApplyState`-level context (validators, congestion info and bandwidth requests of all shards), and what neard
  recorded (post-state root, every outcome, outgoing receipts, gas, balance burnt, proposals, congestion), plus state
  changes from the same `Runtime::apply` call. The corpus: 436 chunks (148 single-shard, 288 four-shard), 7.7 MB, in
  `near-lean/chain/corpus`.
- **Gates.** The exporter aborts unless `Runtime::apply` on the database reproduces the record. `just
  corpus-selfcheck` re-applies each bundle from its own data: 436 of 436 reproduce bit for bit (2520 of 2520 before
  selection). `just chain-replay-corpus` converts each bundle for `registered-replay`, requires Lean to rebuild the
  pre-state entries byte for byte, runs the chunk and compares outcomes, outgoing receipt bytes, burnt totals and the
  complete post-state with the record, never the reverse. Result per chunk: `pass`, `fail: <first field>` or
  `unsupported: <reason>`. The recipe exits 0 only if all pass; `just chain-replay-corpus-report` prints the table
  and always exits 0. Python tests check codec, format, manifest and converter in CI without neard.
- **Current report: 436 pass, 0 fail, 0 unsupported of 436: M3 is accepted** (`just chain-replay-corpus` exits 0).
  Earlier: M3d 426, 10, 0; M3c 405, 14, 17; M3b 129, 6, 301; M3a 70, 18, 348. The last two chunks (`h205`) needed
  the crypto (M3e) and validator (M3d) hosts together, code a contract deploys from its own memory (decoded by the
  replay like catalogue code), and nearcore's UTF-8/UTF-16 log decoding (`NearVM/LogRead.lean`).

  M3d closed the 25 staking and epoch chunks. `Stake`/`Unstake` follow `action_stake` (`TriesToStake`,
  `TriesToUnstake`, `InsufficientStake` against the epoch's minimum stake, the locked balance, and a validator
  proposal per accepted action; a failed receipt keeps none). The epoch is an input, not computed:
  `ApplyState.epochInfo` carries what `EpochInfoProvider` answers (minimum stake, each validator's stake, the total),
  which `validator_stake` and `validator_total_stake` read in the VM (`VMContext.validatorStake`; gas in
  `near-vm-runner` order: base, account id read and decoding, `validator_stake_base`, the 16-byte write).
  Proposals travel in each `ExecutionOutcome` and in `ApplyResult.proposals`; `uniqueProposals` is the chunk's dedup
  (`Runtime::apply` walks them backwards, last proposal of an account wins), and `registered-replay` reports them as
  Borsh `Vec<ValidatorStake>` for the harness to compare with `validatorProposals`. At an epoch's first chunk the
  harness passes the `ValidatorAccountsUpdate` and `NearRuntime.Epoch` applies `update_validator_accounts` (rewards
  added to the locked balance, the staking invariant checked, everything above `max(max_of_stakes, last_proposal)`
  returned to the liquid balance, the treasury paid unless it is a validator) before anything else runs, so the
  chunk trie already holds the updated accounts. The update is outside the proved `apply`.

  M3c closed the 288 four-shard chunks and the 8 converter chunks: the `ShardLayout` (V2, ids 3, 1, 0, 2 over the
  boundaries `test1`..`test3`; routing as `account_id_to_shard_id`, shard order as `shard_ids()`), the bandwidth
  scheduler for any layout (`Bandwidth.lean`: parameters, request bitmaps, the persistent link allowances and sanity
  hash, tie breaks by `rand_chacha 0.3.1`/`rand 0.8.5` shuffling seeded with the previous block hash, the
  remaining-bandwidth distribution), congestion control (`Congestion.lean`: levels in IEEE doubles, outgoing gas
  limits, the allowed shard, `shardAcceptsTransactions` for chunk producers) and the receipt sink (`ShardSink.lean`:
  per-target limits from congestion and granted bandwidth, forwarding from the outgoing buffers, buffering with
  `StateStoredReceipt` metadata, receipt groups, bandwidth requests). `ChainReplay/ShardChunk.lean` runs them around
  `Near.apply` in the order of `Runtime::apply` and reports the outgoing receipts, own `CongestionInfo`, bandwidth
  requests and scheduler hash; the harness compares all of them and the `buffered-receipt*` columns of the
  post-state (bundles with a buffered receipt: 10 chunks, 2 of which change the buffers). No existing runtime
  theorem or definition changed; the proved `apply` still returns every outgoing receipt and the layer around it
  is new. The converter now decodes pre-state postponed receipts, pending counts, received data and delayed
  receipts (with their stored gas and size). Not exercised by the workload: bandwidth requests (every request in
  the corpus is empty, so the tie-break shuffle and request grants are checked by unit tests against the Rust
  crates, not by chunks), a fully congested shard, missing chunks, resharding. A full replay takes about 15
  minutes on four cores (`replay_corpus.py --jobs`): the burst chunks `single-h214`, `sharded-h214` and `single-h215`
  each spend 14 minutes executing 300 Tgas of contract code in the Lean interpreter.

  **M3e (crypto host functions).** The 19 cryptographic host functions of protocol 86 (`sha256`, `keccak256`,
  `keccak512`, `ripemd160`, `ecrecover`, `ed25519_verify`, `p256_verify`, `alt_bn128_g1_multiexp`/`g1_sum`/
  `pairing_check`, the nine `bls12381_*`) now run in the metered VM. `vm/NearVM/CryptoHost.lean` follows
  `near-vm-runner` 0.37.4 `logic.rs` call by call: arguments from memory or a register (a failed read keeps its
  read charges), the function's own base cost (none of them pays the generic `base`), per-byte, per-block
  (`ripemd160`) or per-element costs where `logic.rs` pays them, `IntegerOverflow` before any burn when
  `cost * count` overflows `u64` (the `bls12381_*` element count comes from the declared length, so a register input
  overflows), the `ecrecover` order (signature, then `v`, then hash, then flag, with the `ECRecoverError` texts),
  `ed25519_verify`/`p256_verify` early exits (a signature with its top three bits set, or a `p256` signature outside
  `[1, n-1]`, returns 0 before the message is read or paid), the length errors (`Ed25519VerifyInvalidInput`,
  `P256VerifyInvalidInput`, `AltBn128InvalidInput`, `BLS12381InvalidInput` with nearcore's messages), the register
  write and its gas only when the call writes one, and the protocol-86 `bls12381_not_in_group_fix = false` (version 0).
  The primitives are `HostCrypto` (`interface/NearInterface/HostCrypto.lean`), carried by `RuntimeConfig.hostCrypto`;
  `chain/ChainReplay/HostCrypto.lean` builds it from `NearCrypto` (`Impl`) for the replay executables, and the VM
  never imports `NearCrypto` (`check_vm_dependencies.py`). Without one the functions stay `unsupportedHost`.
  `ecrecover` is declared with its seven arguments (the old table had six), and `p256_verify` is a new import.
  `vm-tests` runs every function on a recording stub. The proofs over the metered registry gained one generic lemma
  per invariant for `cryptoHostFn` (13 files, none of them restated); `applyCharge` and the other proved definitions
  are unchanged. The six chunks pass: `sharded-h48-s1`, `sharded-h193-s2/s3`, `sharded-h199-s3`, `single-h193-s0`,
  `single-h199-s0`. Full replay after M3e: 411 pass, 8 fail (`Stake`/`Unstake`), 17 unsupported (epoch boundary, `validator_stake`,
  `validator_total_stake`): all remaining ones are M3d.

### M4 trie and storage

Acceptance: the state roots of the M3 corpus and a restart test. `just node-state-roots` and `just node-store-tests`
(sources: `near-lean/node/NearNode/{Trie,Store}`, `Primitives/{Storage,TrieNode,Flat}.lean`).

- **Types.** `TrieKey` (24 variants, Borsh tag = column except `DelayedReceipt` 8 and `GasKeyNonce` 21; `toVec?` is
  `TrieKey::to_vec`, `parse?` its inverse, checked against the oracle's bytes), `PublicKeyHandle`, `ValueRef`,
  `FlatStateValue`, `StateChangeCause`, `RawStateChange(sWithTrieKey)`, `StateChangesForShard/Block/BlockRange`,
  `RawTrieNode(WithSize)` and the flat storage types. Fixtures come from `tools/node-conformance` (`storage_fam.rs`);
  `near-store` is not linked there, so `RawTrieNode*` and the flat types are copies of `raw_node.rs`, `flat/types.rs`
  and `flat/delta.rs` at the pin (node hashes are additionally checked against 436 real roots). `FlatStorageStatus`
  has `Disabled`, `Empty`, `Ready`; `Creation` (deprecated) and `Resharding` are rejected. `node-conformance-types`:
  256 types, 0 failures; the existing fixtures are unchanged.
- **Trie, Impl.** `Trie/Update.lean` ports `Trie::update` (`trie_storage_update.rs`, `ops/insert_delete.rs`,
  `ops/squash.rs`) over `ByteArray` and the `NearCrypto` SHA-256: a working trie of updated nodes with `old h` for
  subtrees not loaded, batched insert/delete in order, squash after deletion, then bottom-up serialization and
  hashing. It returns `TrieChanges` (insertions with data and count, deletions, sorted by hash) exactly as
  `TrieRefcountDeltaMap` does: a node read is a reference removed (`move_node_to_mutable`), a node of the new trie
  that was read or created is a reference added, values likewise. Memory usage is `direct + children`, kept as a
  delta along the path (`TRIE_COSTS` 50/2/1). `Trie/Lookup.lean`: `get`, `contains`, in-order iteration from a lower
  bound, and the recorder (`Recorder.partialState` is `PartialStorage`: every node read plus the value a `get`
  fetches; an `update` records the nodes it loads). `Trie/Mem.lean`: a refcounted in-memory node store.
  The functions are `partial` (fuel-free recursion on the key); proofs are future work.
- **Trie, Spec.** `NearInterface.TrieConstruction.build` on the whole entry set. `node-trie-tests` (3000 cases
  checked, 800k checks): root and memory usage equal after random batches; the node store after any number of
  updates equals the store of the final entry set built from scratch, hash by hash with its refcount (so the deltas
  are exact); lookups and iteration (every lower bound) equal a sorted list; an update run on the recorded nodes
  alone gives identical changes. A deliberately broken `squash` fails it.
- **Corpus.** For each of the 436 chunks: the trie built from the raw pre-state has the bundle's pre-state root;
  `update` with the recorded `stateDiff` gives `postStateRoot`, and the resulting store equals the post-state built
  from scratch (every refcount); Lean's own replayed post-state (`registered-replay`, M3) built from scratch and
  applied as a diff through `update` gives the same root; on the 204 chunks small enough for the list-based Spec
  SHA-256, the Spec's roots agree too. Result: **436/436 pre, 436/436 post (diff), 436/436 refcounts,
  436/436 + 436/436 for the Lean replay, 204/204 Spec**. This is the end-to-end state-root check of the M3 runtime.
  The replay takes about 15 minutes (`--no-replay` skips it and checks the diff only, 8 s).
- **Store.** `Store/Db.lean`: columns after `DBCol` (`State` refcounted, `FlatState`, `FlatStateChanges`,
  `FlatStateDeltaMetadata`, `FlatStorageStatus`, `BlockMisc`, `ChunkExtra`) held in memory, made durable by an
  append-only log (one `NRCD` record per commit: length, CRC-32, sequence number, operations `set`/`delete`/`rcAdd`)
  and snapshots (`snapshot-G.bin` with a checksum footer, written as `.tmp` and renamed). Recovery takes the highest
  complete generation, replays its log while checksum and sequence hold, truncates the first bad record and all after
  it, deletes `.tmp` and older generations. *Crash safety:* a commit is applied entirely or not at all (one checksummed
  record); a crash while writing leaves a prefix that recovery drops; a crash during compaction leaves the old
  generation whole or the new snapshot whole (it is written from memory after the old log was applied); a failed
  write poisons the handle. *Limit:* Lean's `IO.FS` has no `fsync`, `seek` or `pread`: `commit` is `write` +
  `flush`, which survives a process kill but not power loss (`Options.sync` runs the system `sync -f` after each
  commit), and values stay in memory (no disk-resident tier); both are deferred. Tests (`node-store-tests`): a log cut
  at every byte and a flipped byte in every record, a crash after each compaction step, a cut snapshot falling back;
  on the corpus, the 148 single-shard chunks (444 commits, 43 MiB of log): pre-state and update written as commits with a head pointer, restart, 29 random and
  boundary cut points of the log (recovered commits are exactly the complete ones, head pointer, node count and the
  root of every post-state rebuilt from the store), garbage collection of replaced nodes leaves exactly the references
  of the post-state tries, and a run with a small log limit that compacts several times. Replaced nodes are released
  in a separate commit (`trieDeleteOps`), as nearcore does at garbage collection, so older roots stay readable until then.
- **Flat storage.** `Store/Flat.lean` follows `FlatStorage`: `get_value`/`contains_key` at a block through
  `get_blocks_to_head` (with `prev_block_with_changes`), a changed key answers as a `ValueRef`, otherwise the
  `FlatState` column; `add_delta`, `get_new_flat_head`, `update_flat_head` (applies deltas to the column, sets the
  status, drops deltas at or below the new head). Functions return store operations to commit atomically. Tested
  against a model of forked chains (head moves, restart) and on the corpus (flat state of the pre-state, the delta of
  the `stateDiff`, the moved head equal to the post-state, values above 4000 bytes by reference).
- **Measured** (100 000 entries, batches of 1 000 writes, one core, `node-bench --filter trie/`; native is
  `just node-trie-native-bench`, `near-store` at the pin over an in-memory `TestDB`, no memtrie, no RocksDB):

  | per key | Lean | native |
  |---|---|---|
  | build the trie from scratch | 11 us | 6.8 us |
  | update (70% overwrite, 20% insert, 10% delete) | 46 us | 24 us |
  | get | 8.1 us | 6.3 us |
  | get with recording | 10.7 us | |
  | iterate | 0.13 us | |
  | store commit of the changes (1.3 KB per write) | 22 us | |
  | store open: replay 28 MiB / snapshot write (per node) | 2.6 / 1.2 us | |

  The native memtrie update is 38 us per key in the same harness, which includes its flat-storage bookkeeping.
  **Proposed M4 target:** trie `update` and `build` within 2.5x of native `near-store` per key and at least 20 000 keys/s
  on one core, `get` within 2x (all met: 1.9x, 1.6x, 1.3x); store commit at least 20 000 writes/s. The time is
  SHA-256 (about 165 MB/s, M2) and allocation; M10 revisits.
- **Doubts and deferred.** The recorded set of an update follows the source but is not compared with a
  nearcore-produced witness (the corpus has none); memtrie, trie caches and prefetching, state parts and sync (M7),
  resharding (`split.rs`, flat `Resharding` status), `delete_range`, the disk-resident store and `fsync`.

### M5 chain

M5a (header and block validation) and M5b (the epoch manager's computation, chunk application in the chain, the chain
store) are done. Acceptance of M5a: `just chain-validate-corpus` (sources: `near-lean/node/NearNode/Chain/`,
`NodeConformance/ChainValidate.lean`, `tools/localnet/{chain_exporter.rs,chain_corpus.py,chain_validate.py}`).
Acceptance of M5b: `just chain-apply-corpus` (sources: `NearNode/Epoch/`, `NearNode/Chain/{Model,StateDecode,
ApplyChunk,Apply,Genesis,Persist}.lean`, `NodeConformance/ChainApply.lean`, `tools/localnet/chain_apply.py`); its
results are in the M5b bullets after the M5a ones.

- **Corpus** (`near-lean/node/corpus/blocks/{single,sharded}`, 1.9 MB of gzip, budget 20 MB). The pinned `neard`
  databases of the M3 localnets read by `safe-near-chain-export` (an overlay on `state-viewer`, like the chunk exporter;
  `build.py --only safe-near-chain-export`; all 436 M3 chunks belong to these blocks). Per chain: `meta.json` (genesis,
  economics, static shard layout), `epochs.jsonl` (`EpochInfo` and shard layout of every epoch, 19 each),
  `blocks.jsonl` (every block from genesis to the head, 514 and 512, as Borsh `Block`, with what nearcore derived:
  `BlockInfo`, block merkle tree and root, block producer, the approvers `EpochManager` ordered with both stakes,
  chunk producers, chunk validator assignments, `ChunkExtra` per shard, whether the next block starts an epoch) and
  `variants.jsonl`. Not exported in M5a: chunk bodies and parts (nothing validated here reads them). The
  localnets have no skipped heights, and every chunk is present except the chunk of shard 0 of the sharded chain in
  heights 181 to 210 (found in M5b); 34 blocks per chain need approvals of the next epoch, and the
  sharded chain alternates two block producers.
- **Invalid variants** (931 and 937, 39 kinds on 24 base blocks per chain: the first two blocks, epoch boundaries, and
  seeded picks). Each is built from a valid block, re-derived and **re-signed by the producer's key** (`validator_key.json`)
  so that exactly one check fails: tampered signature, body and approvals, a signer that is not the producer, wrong
  prev hash (existing and unknown), height, timestamp, epoch ids, `next_bp_hash`, finality fields, merkle root,
  ordinal, epoch sync hash, gas price, total supply, random value, VRF proof and value, chunk mask and bitmap, chunk
  headers root and every other root, a chunk's signature and `prev_block_hash`, validator proposals, protocol version,
  chunk endorsement signatures and counts. The verdict is the error of the pinned
  `Chain::start_process_block_async` (the entry that runs `verify_block_hash_and_signature`, `preprocess_block`,
  `validate_header` and `validate_block`) on the real database, on a copy because even a rejection writes
  bookkeeping; the exporter aborts if nearcore accepts a variant. The comparison is by `Error` variant (26 kinds).
- **Validated** (`Chain/Validate.lean`, in nearcore's order; `chain.rs` unless noted): `verify_block_hash_and_signature`
  (body hash, producer signature via `sample_block_producer`); `preprocess_block` (epoch known, chunk header count,
  known block, height bound, orphan with `partial_verify_orphan_header_signature`); `validate_header` with
  `Provenance::NONE` (challenges, signature, `epoch_id` and `next_epoch_id` from the previous block, protocol version,
  `next_bp_hash`, chunk mask length, `prev_height`, timestamp, `verify_approval_with_approvers_info`
  (`approval_verification.rs`) over `get_all_block_approvers_ordered` (`epoch-manager/lib.rs`: next-epoch approvers
  when `next_block_need_approvals_from_next_epoch`), `Doomslug::can_approved_block_be_produced` (`doomslug.rs`),
  `last_ds_final_block`, `last_final_block`, `block_merkle_root`, `block_ordinal`, `epoch_sync_data_hash`
  (`compute_epoch_sync_data_hash`), `validate_chunk_endorsements_in_header`); the VRF (`signature_verification.rs`) and
  `random_value`; `validate_block_impl` (genesis chunks, shard, `prev_block_hash`, chunk signature by the producer at
  height `prev + 1` (`get_chunk_producer_info_db` without `EarlyKickout`), `Block::check_validity`);
  `validate_block_shard_split` (static layout: no split); `verify_gas_price_checked`, `verify_total_supply_checked`
  (`block.rs`); `validate_chunk_headers` and `validate_block_proposals`; `validate_chunk_endorsements_in_block`
  (`stateless_validation/chunk_endorsement.rs`: `sample_chunk_validators`, signatures, the 2/3 stake rule, the bitmap).
  The chain state derives the `BlockInfo` (`BlockInfo::from_header`, `record_block_info_impl`: epoch id, first block,
  last finalized height) and the block merkle tree of each accepted block; the harness compares both with the stored
  ones. Header V4 to V6 and block V4 with body V2 (what protocol 86 produces); other versions and SPICE are rejected.
- **Result.** `just chain-validate-corpus`: 1024/1024 blocks accepted, 1024/1024 with all derived values equal
  (`BlockInfo`, tree, root, epoch ids, producers, approvers, chunk producers and validators), 1868/1868 variants
  rejected with nearcore's error variant, about 6 s. Python tests (`tools/tests/test_chain_corpus.py`) check the corpus
  files and that the harness fails on a changed verdict, derived value or block.
- **Not checked, with the reason.** The clock (`InvalidBlockFutureTime`); `ping_missing_chunks` and
  `collect_incoming_receipts_from_chunks` (chunk bodies); `check_if_finalizable`, `get_gc_stop_height`, catch-up and
  state-sync state (they depend on the node's final head, tracking and garbage collection, not on the block); the head
  is the accepted block of largest height; the `InvalidBlockHeight` bound uses it; `EarlyKickout` and dynamic
  resharding (nightly); resharding of `get_prev_chunk_headers`.
- **M5b, epoch manager** (`NearNode/Epoch/{Config,Selection,Manager,Process}.lean`, `chain/epoch-manager` at the pin).
  `EpochConfig` is `EpochConfig::genesis_test` filled with the genesis facts, which is what `EpochManager::new_arc_handle`
  builds on a chain with no `epoch_configs` directory (the localnets; note `max_inflation_rate` is 1/40 there, not the
  1/20 of `genesis.json`), `RewardParams` is `RewardCalculator::new`. `Aggregator.updateTail` is
  `EpochInfoAggregator::update_tail` (block production including missed heights, chunk production, endorsement bits,
  latest protocol version per producer, latest proposal per account); nearcore keeps the aggregator incrementally up to
  the last final block and merges the rest at the epoch end, here it is the aggregate over the epoch's blocks at its last
  block, the same on one chain. `collectBlocksInfo` (version vote and its threshold, `Unstaked`, the online ratio,
  `compute_validators_to_reward_and_kickout`), `calculateReward` (U256/U512 as `Nat`), `proposalsToEpochInfo`
  (`apply_epoch_update_to_proposals`, `select_validators` for chunk producers, block producers and chunk validators with the
  stake threshold, `NotEnoughStake` kickouts, `assign_to_satisfy_shards`, `assign_to_balance_shards` with the
  shard-assignment RNG, mandates, samplers, `EpochInfo::V5`), `finalizeEpoch`, `genesisEpochInfo`,
  `computeStakeReturnInfo` and `validatorAccountsUpdate` (`NightshadeRuntime::process_state_update`). `processBlock` is
  `acceptBlock` plus `finalizeEpoch` when the block ends its epoch, so the epochs of a chain are computed, not given.
  Result: **19/19 `EpochInfo` on both chains equal to nearcore's, byte for byte** (rewards, minted amount, kickouts,
  samplers, mandates; a changed inflation rate fails 3 of 19), the genesis epochs from the genesis validators, and the
  `ValidatorAccountsUpdate` equal on every chunk row (148 and 288, the 12 epoch-start ones non-empty).
- **M5b, chain apply** (`NearNode/Chain/{Model,StateDecode,ApplyChunk,Apply,Genesis}.lean`). `StateDecode` turns a shard's
  trie entries into the runtime's model state and the `QueueEncoding.Context` (the inverse of `QueueEncoding.encode`, the
  Lean twin of `lean_input.py`; every chunk's pre-state is re-encoded and must equal the trie's entries), `Model` converts
  transactions, actions and receipts, `ApplyChunk` is `ChainReplay.Registered.run` for one block returning typed results,
  `Apply.applyBlock` is what `postprocess_block` does: for each shard the incoming receipts (each new chunk's previous
  chunk's outgoing receipts grouped by `receiver_shard_id` (global contract distributions by target shard), one proof per
  new source chunk, shuffled with ChaCha20 seeded by the previous block hash, then the receipts delivered since the
  shard's last chunk, newest block first), the `ApplyChunkBlockContext` from the block and its chunk headers (gas price of
  the previous block, congestion info and bandwidth requests of the headers, `missed_chunks`), the epoch provider, the
  update, the runtime, the trie update (`Trie.update` on the diff of entries) and the `ChunkExtra` V5 (outcome root from
  `ExecutionOutcomeWithId::to_hashes`, whose partial status carries no failure details; balance burnt minus subsidized).
  A chunk that is not new gets `apply_old_chunk`: the accounts update and the bandwidth scheduler, previous extra with
  the new root. Checks per chunk: header `prev_state_root`, `prev_outgoing_receipts_root` of the previous chunk's
  receipts, `tx_root` of the transactions, the incoming and outgoing receipts against nearcore's recorded ones, and the
  `ChunkExtra` against the corpus. The genesis state is built from `genesis.json` (`GenesisStateApplier`, storage usage
  recomputed) and its roots equal the genesis chunk headers'. Inputs the corpus lacks are taken from the M3 bundles
  (`chunks.jsonl.gz`, see CORPUS.md section 12): the transactions of a chunk are the bundle's, a chunk without a bundle is
  empty (the `tx_root` check proves it), and code a contract deploys from its own memory is found in the receipts the bundle
  records as sent. No exporter change was needed.
  **Found on the way:** the sharded chain does miss chunks (shard 0 in heights 181 to 210), contrary to the M5a note; the
  node handles them, and the shuffle of receipt proofs only matched once old chunks were left out of it. No runtime bug
  was found; `near-lean/{vm,runtime,interface}` are unchanged.
- **M5b, chain store and restart** (`Chain/Persist.lean`, columns added to `Store/Format.lean`). One commit per block holds
  the block, its header, `BlockInfo`, merkle tree, the `EpochInfo` of a finalized epoch, the trie nodes of every shard,
  `ChunkExtra`, outgoing and incoming receipts and `HEAD`, `HEADER_HEAD`, `FINAL_HEAD`, `GENESIS_HASH`. `load` rebuilds the
  chain state and progress; `chain-apply-corpus` runs every chain in two processes, the second continuing from what the first
  stored at half the chain.
- **M5b, result** (`just chain-apply-corpus`): both chains, from genesis to the head, **all agree**. Sharded: 19/19 epochs, 288/288 validator accounts updates, 2044/2044 `ChunkExtra` (511 blocks, four shards), 2044/2044 pre-state round trips, 288/288 incoming and 288/288 outgoing receipt lists. Single: 19/19, 148/148, 513/513, 513/513, 148/148, 148/148 (513 blocks). Each chain was applied in two processes with the store between them (stopped at height 256 and 255). Timing on one core: 54 min for the single-shard chain and 58 min for the sharded one, almost all in the burst blocks 214 to 217 (13 to 27 minutes each: 300 to 1200 Tgas of contract code in the Lean interpreter); the other blocks take about 0.5 s per chunk. The catalogue handed to the encoders must hold only the code a chunk uses (a catalogue of everything seen made block 218 take over 20 minutes).
- **M5b, deferred and doubts.** A change of shard layout (`StickyResharding`, dynamic resharding, `EarlyKickout`, SPICE) is
  rejected, not represented; the epoch config is the generated one, real networks load `epoch_configs`; `max_by_key` ties
  of the version vote are not reproduced; only accounts and full access keys in the genesis; the incremental aggregator is
  not kept; trie nodes are never garbage collected and flat storage is not updated by the node (M4's tests cover it);
  chunk production, state witnesses and validation of the chunk body beyond its roots; forks and reorgs (one chain, no
  rollback); the chain is run chunk by chunk with the shard state converted from the trie each time (about 0.5 s a block,
  minutes for the burst chunks), performance is M10. `just chain-replay-test` has a failing test, 
  `test_emitted_deployment_uses_the_catalogue_or_rejects_atomically`, at the base commit already: M3e made the replay decode
  code a contract deploys from its own memory, and the test still expects an execution issue.

### M6 network

Acceptance: `just localnet-peer` (sources: `near-lean/node/NearNode/{Proto,Net,Network}/`, `NearNode/Chain/Bootstrap.lean`,
`tools/localnet/{network_oracle.rs,peer_accept.py}`); the conformance gate is `just node-conformance-network`.

- **Protobuf** (`Proto/Wire.lean`). A generic proto3 codec: varints (ten bytes, the tenth 0 or 1; a `uint32` has at most
  five), tags, zigzag, fixed32/64, length-delimited, packed and unpacked repeated fields, groups (skipped as
  `protobuf` 3.0.2 does), unknown fields (framing checked, content ignored), and `Schema`s that say which fields are
  messages so the parser reads them as nearcore's does. Two quirks of the pinned parser are reproduced because the
  oracle found them: a singular message or oneof member is *replaced* by a later occurrence (every occurrence is still
  checked), and a nested message that claims more bytes than the input holds is read as far as the input goes
  (the top-level stream has limit `u64::MAX`), so a message cut inside a nested message at a field boundary is
  accepted. nearcore writes repeated `uint64` unpacked, fields in declaration order.
- **Messages** (`Network/{Types,Message}.lean`). `PeerMessage` with all 25 variants of `network.proto`'s oneof
  (`UpdateNonceResponse` decodes as a routing update), `Handshake` with `OwnedAccount`, `HandshakeFailure`,
  `RoutingTableUpdate`, `SyncAccountsData`, `PeersRequest/Response`, headers and blocks, `Transaction`, the routed
  message in both wire forms (`Routed` with the Borsh `RoutedMessageV1`, `RoutedV3` with a `TieredMessageBody`), the
  routed bodies (every `RoutedMessageBody` variant, with the T1/T2 tags), state sync requests and responses, epoch
  sync, snapshot hosts, optimistic blocks. Sources: `network_protocol/{network.proto,mod.rs,edge.rs,peer.rs,
  proto_conv/*}`. `Edge` hash, `verify` and nonce rules, `PeerMessage::max_size` are checked too. Not modelled:
  `TxStatusResponse` (an RPC view type, `FinalExecutionOutcomeView`); a message with that body does not decode.
- **Oracle** (`tools/localnet/network_oracle.rs`). `near-network` keeps its types private, so `build.py` adds this file
  to the crate as a module (plus one `pub mod` line in `src/lib.rs`, restored after the build) and a one-line binary
  `safe-near-network-oracle`. It builds each variant around the M1 Borsh fixtures, writes nearcore's own
  serialization and its `PeerMessage::deserialize` verdict on byte and field level mutations (extra and duplicated
  fields, re-typed fields, groups, long varints, truncation). Fixtures: `near-lean/node/fixtures/network`, 15 files,
  4373 inputs (1899 accepted, 2474 rejected; 3273 of them `PeerMessage`). Result: **`node-conformance-network`, 0
  failures**; 180 000 further mutations (other seeds, not committed) also 0. `tools/tests/test_network_fixtures.py`.
- **Net** (`Net.lean`, `Net/{Uv,Mem}.lean`). `Stream`, `Listener` and `Net` are all the node uses; `Framed` is
  `stream.rs` (u32 LE length, 512 MiB, partial frames kept across timeouts). `Net/Uv.lean` is the only module that
  imports `Std.Internal.UV.TCP` (Lean's libuv binding) and has no `@[extern]`: a reader task per connection and polling
  with timeouts, because `cancelRecv` is documented as dangerous. `Net/Mem.lean` is the in-process network for tests.
  `node-net-tests` runs the same checks on both. `tools/check_node_isolation.py` needed no change.
- **Peer protocol.** `Network/Handshake.lean` is `process_handshake` and `handle_msg_connecting` as pure functions
  (version range 83..86, genesis, target, nonce window of 20 minutes, owned account and 30 minute skew, the edge both
  sign, `LastEdge` and `HandshakeFailure` answers and retries); `Peer.lean` runs them over a stream with the 20 s
  handshake timeout; `Node.lean` is the loop of a ready `PeerActor`: routing table, snapshot hosts and accounts sync on
  connect, `PeersRequest` and the latest block every minute (`READ_TIMEOUT` is two minutes), nonce refresh every ten
  minutes, replies to `PeersRequest`, `SyncAccountsData`, `RequestUpdateNonce`, `BlockHeadersRequest`, `BlockRequest`
  and `Ping`, edges and routed signatures verified with the M2 Ed25519 (invalid: close). `node-handshake-tests`: both
  sides against each other in memory (valid, other genesis, bad signature, versions, stale nonce, wrong target,
  `LastEdge`, owned accounts), 27 checks. **Found against neard:** an inbound connection without a
  `sender_listen_port` is dropped (`validate_new_connection`: `peer_info.addr` is none), so the node announces one and
  listens; `BlockRequest` is limited to 10 a second (`rate_limits/messages_limits.rs`), the driver sends 8.
- **Sync** (`Network/{Driver,Apply,Run}.lean`). Headers after a locator, blocks by hash, each validated in order by
  `Epoch.processBlock` (M5a), chunk bodies by routed `PartialEncodedChunkRequest` for all parts: the data parts are the
  Borsh `TransactionReceipt` of the chunk (merkle paths checked against `encoded_merkle_root`, `tx_root` against the
  transactions, no Reed-Solomon decoding needed because the peer has every part). A block is applied (M5b) when its own
  bodies and its child's are in: the child's `prev_outgoing_receipts` are the receipts this chunk sent, which supply
  the code a contract deploys from its own memory and are compared with what the Lean runtime produced; the child's
  chunk headers carry the previous `ChunkExtra` (state root, outcome root, gas used, balance burnt, proposals,
  congestion info, bandwidth requests) and are compared field by field. Validation runs on the connection thread,
  application on its own thread with the store (`Chain/Persist`), so a heavy block delays application, not following.
  The chain starts from `Chain/Bootstrap.lean` (extracted from `node-chain-apply`, which uses it): the genesis files of
  the M5 corpus, whose genesis block and `BlockInfo` nearcore derived; deriving them from `genesis.json` is M7.
- **Acceptance.** `just localnet-peer` starts the single-node localnet and its workload (without the `hostcalls`,
  `burst` and `wait` scenarios: the Lean interpreter needs minutes per block of heavy calls; `--full-workload` runs
  them), then the node with its own key, listening, dialing `neard`. Run of 614 s: one handshake, no disconnect,
  `neard`'s `network_info` lists the node, 2 edges received and verified, 599 blocks validated (the node was never more
  than 3 blocks behind the head during validation), 598 blocks / 598 chunks applied, 597 `ChunkExtra` equal to the next
  chunk header's, 595 outgoing-receipt sets equal to the next chunk bodies', 597 state roots equal to `neard`'s over
  RPC. Application (about one block a second in the interpreter) is slower than the localnet's block rate under
  load, so the applied height trails the validated one; the harness reports the lag against `neard`'s head after the
  drain (423 blocks at the end, because `neard` kept producing while the node drained).
- **Deferred.** Tier 1 (account data is accepted, not verified or kept), routing beyond one peer (no forwarding,
  no route-back cache, no peer store or connection pool), `TxStatusResponse`, fork choice and reorgs, header
  validation before the block, Reed-Solomon reconstruction of chunks with missing parts, (state sync and the
  genesis block: done in M7), IPv6 in `Net/Uv`, production of anything (M8).

### M7 sync

Acceptance: `just localnet-follow` (sources: `near-lean/node/NearNode/{Chain/{StateSync,Header,Profile},Trie/{StateParts,Witness},
Zstd,Network/{Driver,Run}}.lean`, `tools/localnet/follow_accept.py`); the gates are `just node-conformance-sync`
(zstd and state parts against nearcore's own code), `just node-sync-tests` (header sync and body attach on the
in-memory `Net`) and the existing ones.

- **Profile of the application.** `Chain.Prof` times the stages of `applyBlock`/`runChunk` (`node-chain-apply
  --profile`, `near-lean-node --profile`). On the single-shard corpus (heights 1..213) the time went to the list-based
  `Sha256.hash` that the runtime's encoders use (the shard was re-encoded four or five times a chunk), the storage-accounting
  trie that was rebuilt from the entries on every chunk (`TrieOverlay.start`, quadratic), the pre-flight encode of
  `TransactionRegistry.observe`, and the interpreter (about 5M instructions a second). Fixes, all node side: contract code
  and the encoders hash with `NearCrypto`'s SHA-256 (`Model.digest`), the runtime gets the trie the node stores
  (`Trie.objects`) instead of rebuilding one, the dead and duplicate encodes are gone, and the round trip of the
  pre-state is a flag. **Runtime change:** only defaulted parameters `digest` (default `Sha256.hash`) and `preflight`
  (default `true`) on `StateEncoding`, `QueueEncoding` and `TransactionRegistry`; no theorem statement changed, no
  `sorry` or axiom, the contract proofs build. **Effect:** 120 blocks took 75 s before (0.62 s a block), 213 blocks 23 s
  after (0.11 s a block, six times faster); every `ChunkExtra`, receipt set and epoch is still equal to nearcore's.
  Steady-state shares on the live sharded run (4 shards, 484 chunks, 31.8 s): `trie-witness` 29 %, `encode-state`
  21 %, `results` 14 %, `observe-queues` 12 %, shard start 8 %, decode 5 %, interpreter 5 %. What remains is
  the interpreter on heavy contracts: block 214 of the full-workload corpus (the 300 Tgas calls) takes 853 s, 98 % in
  `Near.step`/`runMetered`. It was not made faster; the VM is the specification, and a faster interpreter is a task for M10.
  `just chain-replay-corpus` after the change: 436 of 436 chunks pass, 31 min wall (89 min CPU; the heavy-call chunks dominate);
  the runtime change is defaulted parameters, so no timing change is expected there and no earlier timing exists for the full corpus.
- **Header sync** (`Network/Driver.lean`, `Chain/Header.lean`, `Epoch.processHeader`): `GetBlockHeaders` from the
  locator; an answered header gets `Chain::sync_block_headers`'s checks (`acceptHeader`: `validate_header`, then the
  epoch manager's `BlockInfo::from_header`, no chunk needed), and epochs are finalised from headers alone, so the node
  knows the epoch while the bodies are behind. Header-only `BlockRec`s are upgraded by `attachBody` when the body arrives; the driver's
  `cursor` is where the attach resumes. The flow follows `chain/client/src/sync/header.rs`.
- **State sync** (`Chain/StateSync.lean`, `Trie/StateParts.lean`, `Zstd.lean`; nearcore `chain/client/src/sync/state/`,
  `chain/chain/src/state_sync/{utils,adapter}.rs`, `core/store/src/trie/state_parts.rs`).
  - The sync hash is nearcore's (`get_sync_hash` in `state_sync/utils.rs`): the child of the first block of the
    epoch in which every shard has at least two new chunks, once that block is final; the extra blocks are those from its
    previous block down to the lowest `height_included` of the chunks of that block (`get_extra_sync_block_hashes`).
    `node-sync-tests` checks both as properties on the corpus chains.
  - `StateRequestHeader` and `StateRequestPart` are routed T2 messages that carry the requester's address. The host answers
    with a `StateRequestAck` on T2 and the `VersionedStateResponse` on a Tier-3 connection it opens to the requester's
    listener, so the node listens (`Network/Run.lean`). A refused or unanswered request is sent again after 5 s
    (`stateRetryMs`); no external storage is used (the localnet has none).
  - The header (`ShardStateSyncResponseHeader` V2) is checked as `set_state_header` does: chunk hash, transaction root and
    receipts root of the chunk, merkle paths of the chunk and its predecessor against `chunk_headers_root` of the
    blocks, the incoming receipts block by block from the sync block back to the previous chunk (merkle path of each
    receipt group to the sending chunk's outgoing receipts root and from there to the block's
    `prev_chunk_outgoing_receipts_root`, one proof per chunk the block included, from the chunk mask), and the state root node
    against the state root (hash and memory usage). The state is the one at the `prev_state_root` of the chunk in the
    block before the sync block, so the node starts applying chunks at that chunk's height (`ShardStart`), with the
    receipts delivered so far from the header. The first block applied cross-checks the header's receipts for that block
    against the ones derived from the bodies.
  - A part is zstd-decompressed (`Zstd.decompress`, pure Lean: frames, FSE and Huffman tables, sequences, repeat
    offsets, xxh64 checksum, skippable frames) into a `PartialState`, and validated as `Trie::validate_state_part`
    does: the interval of the part is re-walked with the part as the only storage (`find_state_part_boundary`,
    `visit_nodes_interval`) and the set of nodes visited must be the set of nodes given. A missing or an extra
    node, a changed node, and a part of another index or count fail. `applyPart` gives the nodes with their reference counts
    for the store. The conformance gate `node-conformance-sync` compares with the verdicts of nearcore's own
    `zstd` and `near-store` over tries of many shapes (good parts, a node removed, repeated, changed or added, other
    index, other count, empty) and with frames of the `zstd` crate in many shapes (levels, with checksum, several frames, skippable,
    cut or flipped).
  - The apply worker gets the synced tries through `Shared.install`; shards the node does not track are not started and
    their chunks are neither fetched nor applied (`--track-shards 0,2`).
  - Sync flow: headers first, then the state of the sync epoch, then blocks from the sync point, as the `EpochSync -> HeaderSync ->
    StateSync -> BlockSync` of nearcore minus epoch sync, which the localnet does not need (the node starts from the genesis
    files and the first blocks, as in M6, and takes the headers from there).
- **Acceptance** (`follow_accept.py`: the pinned `neard` localnet runs the workload with `--full-workload`, then the node starts
  fresh; a 1 Hz RPC sampler gives `neard`'s head and the node's lag log (JSONL per second) gives its applied
  height; the lag is the difference; every applied chunk's `ChunkExtra` is compared with the next chunk header's, its outgoing receipts
  with the next chunk body's, and the state root with `neard`'s over RPC). Results, 600 s followed after reaching the head:

  | topology | state sync point (shards at height) | reached head | max / median lag | state roots over RPC | disconnects |
  |---|---|---|---|---|---|
  | single | height 543, 1 shard, 1 part, 141 KB | 2.2 s | 2 / 0 blocks | 996 of 996 equal | 0 |
  | sharded (4) | height 543, 4 shards, 1 part each, 316 KB | 7.3 s | 9 / 1 blocks | 4003 of 4003 equal | 0 |

  With `--track-shards 0,2` on the sharded localnet: 158 of 158 roots equal over 40 s, max lag 10, median 1.
  The node was within 10 blocks of the head for the whole window in all three runs. The profile of the sharded
  run: 4004 chunks in 313 s of CPU over 598 s, so the node has 1.9x headroom at the localnet's block rate with four shards.
- **Bursts (honest result).** With `--lightburst` (heavy calls sent 70 s after the node reached the head) the node
  falls behind, because each heavy chunk is interpreter bound and about 10 to 100 times slower than a normal chunk:
  162 s of interpreter time for the burst's 1003-chunk window against 126 s for everything else. Single shard, followed 600 s: lag
  peaked at 253 blocks 155 s after the burst was sent, the node was back within 10 blocks 192 s after it, and the median
  lag over the window was 1; all 1003 state roots equal, no disconnect. With 240 s followed (single and sharded) the
  node was still draining at the end (peak 262 and 272 blocks, not caught up inside the window), which is why the
  catch-up limit of the harness, 240 s, only holds with a window of at least 600 s. The remaining bottleneck is the
  interpreter at about 5M instructions a second, not the node: a burst of N Tgas of contract code costs about
  so the node keeps up with traffic that fits its 0.11 s a block and falls behind by the burst's extra CPU time
  while it lasts.
- **Deferred.** Epoch sync proofs (not needed: the localnet nodes start at genesis headers), state sync from external
  storage, a state sync that spans an epoch change while running, retrying a sync hash that moved on, a synthetic unit
  test of `validateStateHeader` (it is exercised by every live run and by the tamper tests of the parts, but no
  tampered header is tried: left for M8, which needs the same checks for stateless validation), a faster interpreter for the heavy-call blocks (M10), and
  the pool of parallel part downloads for shards with many parts (the localnet state is one part a shard).

## Open points

- Numeric performance target for M10, measured against nearcore (M2's and M4's are proposed above).
- Whether crypto host functions in `NearVM` slow contract verification. If they
  do, `NearVM` takes host crypto as a parameter and the node supplies it. Today the VM takes its
  digests, `ed25519Verify` and `ecrecover` as parameters; `NearCrypto` is a separate package it can import later.
  Resolved in M3e: the VM takes a `HostCrypto` through the runtime configuration and the chain package supplies it.
