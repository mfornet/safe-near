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

### M8 validator

Acceptance: `just localnet-validator` (to come in M8d). Sources of the reference, all at the pin
(`tools/localnet/.nearcore/<revision>`): `chain/chain/src/doomslug.rs`, `chain/client/src/{client,client_actor,
chunk_producer,chunk_inclusion_tracker,chunk_endorsement_handler}.rs`, `chain/client/src/stateless_validation/**`,
`chain/chain/src/stateless_validation/{state_witness,chunk_validation,chunk_endorsement}.rs`, `chain/chunks/src/*`,
`core/primitives/src/{block,sharding,reed_solomon}.rs`, `chain/network/src/peer_manager/network_state/mod.rs`.

#### M8a, inventory (what a validator does at protocol 86)

1. **Doomslug** (`doomslug.rs`, `client.rs`, `client_actor.rs`).
   - On every new head `set_tip(hash, height, last_final_height)`: the timer restarts at `height + 1` and an
     endorsement is pending.
   - Every `doomslug_step_period` (10 ms) `process_timer` (up to 20 iterations):
     - `endorsement_pending` and `now >= last_endorsement_sent + endorsement_delay` and `tip.height >= largest_target_height`:
       approval `Endorsement(tip.hash)` for `tip.height + 1`, and `largest_target_height = tip.height + 1`.
       `Doomslug::new` is called with `min_block_production_delay` as the endorsement delay, `max_block_production_delay`
       as the base `min_delay` of `T` and `max_block_wait_delay` as its cap; the localnets run 600 ms, 2 s and 6 s.
     - `now >= timer.started + T(timer.height - last_final_height)` with
       `T(n) = min(cap, base + (base / 10) * max(n - 2, 0))` (`base` 2 s, `cap` 6 s): a `Skip(tip.height)` approval for
       `timer.height + 1`, `timer.started += T`, `timer.height += 1`.
   - The largest target height is persisted before any approval is sent (`save_largest_target_height`): never
     approve two blocks at one height (slashing-style safety); the node needs the same column.
   - Approvals go to `get_block_producer(epoch, target_height)` (to the previous epoch's producer too when the
     final head is still in the previous epoch, for skips); to itself they are collected locally.
   - Receiving: `collect_block_approval` verifies the signature against the validator of the next block's epoch (or
     the one after it), keeps only approvals for heights where it is the producer, resolves `Skip` to the parent
     it knows, parks approvals whose parent it lacks (`pending_approvals`), and `Doomslug::on_approval_message`
     accumulates stake per `(prev_hash, parent_height, target_height)` tracker; one approval per account per
     target height (a newer one withdraws the older).
   - Readiness (`ready_to_produce_block`): approved stake `> 2/3` of this epoch's total and of next epoch's (or the
     latter is zero) for the tracker of the head; then either all shards have an endorsed chunk
     (`ChunksReadiness::Ready`) or `now > ready_since + T(...) * chunk_wait_mult` (1/3).
2. **Block production** (`Client::produce_block_on`, `Block::produce`). When the node is `get_block_producer(epoch, h)`
   for the next height, nothing in `latest_known` at that height, and doomslug is ready: approvals ordered as
   `get_epoch_block_approvers_ordered(prev)` with signatures of the tracker's witness, new chunk headers (only
   chunks with enough endorsements, `height_included = h`, the others are the previous block's), endorsement
   signatures per chunk, `next_bp_hash`, `epoch_sync_data_hash`, `block_merkle_root` of the tree extended by the
   parent, `block_ordinal`, `minted_amount` at an epoch start, gas price and total supply from the included
   chunks, timestamp `max(now, prev + 1ns)` and VRF `(value, proof)` of `prev.random_value`
   (`get_block_metadata`), header V6 and body V2, signed by the node key, `latest_known` saved, then broadcast
   (`PeerMessage::Block`) and processed like a received block. Exactly the checks the node already runs on a
   received block (`Chain/Validate`) hold of the produced one, so the validator is its own oracle.
3. **Chunk production** (`Client::produce_chunks`, `ChunkProducer::produce_chunk_internal`). When a block is
   accepted (not syncing), for each shard the node is chunk producer of at `height + 1`
   (`get_chunk_producer_info_db`): the previous block's `ChunkExtra` gives state root, outcome root, gas used and
   limit, balance burnt, validator proposals, congestion info and bandwidth requests; the outgoing receipts are
   those of `get_outgoing_receipts_for_shard_from_store` since the last included chunk; transactions come from the
   pool filtered by the validity period and the signer's nonce (an empty list is a valid chunk); `tx_root` and
   `prev_outgoing_receipts_root` are merkle roots; the body is `TransactionReceipt(txs, receipts)` Borsh, Reed-Solomon
   encoded into `num_total_parts` parts (`Chunks.numTotalParts`: the genesis block producer seats, at least 2; data parts
   `(total - 1) / 3`, at least 1; two parts, one of them data, on the two-validator localnet), `encoded_merkle_root` over the parts, header V3 over inner V5 (`DynamicResharding` is on from protocol 85; V4 before), signed. Then `distribute_encoded_chunk`: every part owner (`get_part_owner(epoch, ord)`, part
   `i` goes to block producer `i mod n`) and the next epoch's block producers get a `PartialEncodedChunk` with
   their parts, the receipt proofs for shards they care about and the Merkle path of each part, routed
   `VersionedPartialEncodedChunk` to the account; each part owner forwards the parts it owns
   (`PartialEncodedChunkForward`) to the block producers tracking the shard and to the next chunk producer; the
   chunk is persisted and marked ready for inclusion. It also answers `PartialEncodedChunkRequest` from its
   cache, partial chunk store or chunk store.
4. **Stateless validation, producer side** (`state_witness_producer.rs`, `state_witness.rs`, `partial_witness_actor.rs`).
   After producing a chunk, `create_state_witness` builds `ChunkStateWitness` V2: the main transition (the last
   new chunk's application at its block: `base_state` = trie nodes recorded while applying it, post state root), one
   implicit transition per later block (`apply_old_chunk`: its recorded nodes, post state root), the source receipt
   proofs (one per chunk included between the second-last and the last new chunk), the previous chunk's
   transactions, the `applied_receipts_hash` and the new transactions. If the producer is among the chunk's
   validators it endorses at once. `ChunkContractAccesses` (hashes of contracts called) go to validators first; then
   the witness is Borsh encoded, zstd compressed (`EncodedChunkStateWitness`) and Reed-Solomon encoded for
   `ordered_chunk_validators().len()` parts, 60 % data (`witness_part_length`); part `i` goes as
   `PartialEncodedStateWitness` (signed by the producer, V1) to validator `i`, which forwards it to the other
   validators (not the producer) as `PartialEncodedStateWitnessForward`. Deployed contracts are distributed as
   `PartialEncodedContractDeploys` (only when a contract was deployed; also Reed-Solomon, 60 %).
5. **Stateless validation, validator side** (`partial_witness_tracker.rs`, `chunk_validation_actor.rs`,
   `chunk_validation.rs`, `validate.rs`). A part is checked (`validate_partial_encoded_state_witness`: epoch, the
   node is a validator of the chunk, the producer's signature, part ordinal) and, if the node owns the part,
   forwarded; with enough parts the witness is decoded (Reed-Solomon, zstd, Borsh) and `ChunkStateWitnessAck` goes to
   the producer. A witness whose previous block is missing waits in the orphan pool (heights head + 2 to head + 5).
   `pre_validate_chunk_state_witness`: version, validity of the new transactions for the config, the chain walk back
   to the last two new chunks of the shard, source receipt proofs against the blocks' `prev_outgoing_receipts_root`
   (merkle path, shard ids, no extra proofs), shuffle with the block's salt, the hash of the receipts applied, the
   transactions' root against the block's chunk header, the validity period of each transaction.
   `validate_chunk_state_witness`: apply the last chunk on the recorded storage, compare its post root with the
   witness, apply the implicit transitions in order comparing each post root, then the chunk header against the
   resulting `ChunkExtra` and the outgoing receipts root (`validate_chunk_with_chunk_extra_and_receipts_root`), the
   new transactions' root and the encoded merkle root of the chunk (`validate_chunk_with_encoded_merkle_root`: the
   body is re-encoded with Reed-Solomon). On success the node sends `ChunkEndorsement` V2 (signature over the
   chunk hash with `ChunkEndorsementInner` and metadata) to the block producers of heights `h .. h+4` (unique). The
   block producer's `ChunkEndorsementTracker` validates each endorsement (validator of the chunk, signature, epoch),
   and `collect_chunk_endorsements` yields the state: a chunk header is included in the block only when the endorsing
   stake is above 2/3 of the chunk validators' (`ChunkInclusionTracker`), else the previous chunk header is repeated.
6. **Network duties without which the above cannot reach neard** (`peer_manager`, `network_state/mod.rs`).
   `send_message_to_account` finds the peer of an account from `accounts_data` (`SyncAccountsData`: a
   `SignedAccountData` signed with the validator key, carrying the node's peer id and address) or from announced
   accounts; without it, every approval, chunk part, endorsement and witness part for the node is dropped by `neard`
   as `UnknownAccount`. The node therefore signs and sends its own `AccountData`. Messages in the protocol-86 tiers:
   T1 `BlockApproval`, `VersionedPartialEncodedChunk`, `PartialEncodedChunkForward`, `VersionedChunkEndorsement`,
   `PartialEncodedStateWitness`(`Forward`), `ChunkContractAccesses`, `ContractCodeRequest/Response`,
   `PartialEncodedContractDeploys`; T2 `ChunkStateWitnessAck`, `ForwardTx`; a T1 message falls back to the routed T2
   path over the existing connection when no tier-1 connection exists, which is the localnet case.

   | Step | Message (`Network/Types.lean` `RoutedBody` unless noted) | Present |
   |---|---|---|
   | approvals | `blockApproval` (tag 0), `Approval` and `get_data_for_sig` | yes (M1b, M6) |
   | block | `PeerMessage.block` broadcast | yes |
   | chunk parts | `versionedPartialEncodedChunk` (16), `partialEncodedChunkForward`, request/response (11, 12) | yes (M6 decodes, M7 requests) |
   | witness | `partialEncodedStateWitness` and `Forward`, `versionedPartialEncodedStateWitness*`, `chunkStateWitnessAck`, `chunkContractAccesses`, `contractCode*`, `partialEncodedContractDeploys` | yes (M1c, M6) |
   | endorsement | `versionedChunkEndorsement` | yes |
   | account routing | `SyncAccountsData` with `SignedAccountData` | decoded only; signing and sending to do |
   | transactions | `forwardTx` | yes; a pool is to do |

   Routed messages the node *creates* need the author's signature over the routed hash (`RoutedMessage` signing); the
   node has verified them since M6 but signs only edges, so signing is added.
7. **Epoch assignment** (`EpochManager`): `get_block_producer`, `get_chunk_producer_info(epoch, height, shard)`,
   `get_chunk_validator_assignments(epoch, shard, height)` (the sampler of M1c), `get_part_owner`,
   `get_epoch_block_approvers_ordered`; all already in `NearNode.Epoch` (M5), checked at 46 heights against nearcore.

**Decisions.**

- *Topology.* A new `validator` topology: `neard localnet -v 2 -s 1` (the sharded topology already shows its genesis: two validators with 5e31 yoctoNEAR each, two block producer seats); `node0` stays `neard`, `node1`'s
  `validator_key.json` and `node_key.json` are the Lean node's. The generated genesis gives both validators equal
  stake (50 % each), so neither holds 2/3 alone and the Lean node's approvals, endorsements and blocks are all
  needed (every finality gadget threshold is `> 2/3`). Reuses `generate`/`localnet.py` (`TOPOLOGIES` entry) and the
  M5 chain exporter for the genesis block and its derived `BlockInfo` (a genesis-only corpus), which `Boot.load` reads.
- *Witness production.* The Lean runtime applies a chunk from the whole shard state; it does not record trie
  accesses. The node's witness therefore carries, as `base_state`, **every node and value of the shard's trie** at the
  pre-state root (`Trie.objects`, the function the M5 apply already uses). This is a superset of the recorded proof:
  `Trie::from_recorded_storage` reads the nodes it needs by hash and ignores the others, and the localnet's state is
  a few hundred kilobytes (the witness limit is 64 MiB). Contract code is not put in `base_state` (nearcore's
  recorded proof excludes it) but announced by `ChunkContractAccesses`. The oracle test of M8b checks the claim by
  having nearcore's own `validate_chunk_state_witness` accept such a witness. Exact recording stays an M10 item
  (witness size).
- *Witness validation.* The node tracks every shard of the localnet and has applied the previous blocks, so it validates
  a witness by what nearcore's validation computes: it runs `pre_validate` in full (receipt proofs, hashes, roots), and
  instead of re-executing the chunk on the partial trie it compares the witness' post state roots and the
  resulting `ChunkExtra` and receipts root with its own execution of the same blocks (deterministic runtime, the same
  inputs), then the chunk header, the transactions' root and the encoded merkle root exactly as
  `validate_chunk_state_witness_impl` does. A node that does not track the shard would need the runtime to run on a
  partial trie (deferred; the runtime model takes a whole state).
- *Zstd.* The node decompresses witnesses with its M7 decoder and compresses with a valid frame of raw blocks (a
  conforming zstd stream; the size is irrelevant on the localnet). A real compressor is deferred.
- *Transactions.* The localnet workload sends its transactions to `neard`'s RPC. `neard` forwards them (`ForwardTx`)
  to the chunk producer of the shard, which may be the Lean node: its chunks carry the transactions it receives, so
  the node needs a pool with the validity period and nonce filter (M8c); until then it produces empty chunks, which are
  valid.
- *Forks.* With two producers, a slow producer produces a competing block now and then. M7 follows one chain without
  rollback. The validator needs the fork choice of `Chain::update_head` (highest height, then score) and a rollback of
  the applied state to the fork point; scheduled in M8c, with the rule that the node never approves two blocks at one
  height.
- *Signing.* The M2 note says constant-time signing is open for M8. The localnet run signs with the `Impl` Ed25519 `sign`,
  which is not constant time; this is recorded as the first hardening item, not claimed done.

**Sub-milestones.**

| | Scope | Gate |
|---|---|---|
| M8a | This inventory and the decisions | design document |
| M8b | Reed-Solomon over GF(2^8) (`reed-solomon-erasure` 6.0.0), `EncodedShardChunk` construction with merkle paths and `PartialEncodedChunk`, signatures and constructors of approvals, endorsements, partial witnesses, the account data; witness construction; oracle fixtures from the pinned crates | `just node-conformance-validator` |
| M8c | Doomslug state machine, block production, chunk production, witness and endorsement paths, `AccountData` and routed message signing, pool, fork choice; unit tests and corpus replay (the node produces the blocks of the corpus and Lean's own validation accepts them) | `just node-validator-tests` |
| M8d | `localnet-validator` harness and the acceptance run | `just localnet-validator` |

#### M8b, building blocks (done)

Gate: `just node-conformance-validator` (1856 checks, 0 failures). Sources: `NearNode/Validator/{ReedSolomon,Signer,
Chunk,Messages,Witness,Block}.lean`, `NodeConformance/Validator.lean`, `tools/node-conformance/src/validator_*.rs`
(`validator-fixtures`, `just node-validator-oracle`), fixtures `near-lean/node/fixtures/validator` (5.9 MB; a second
run of the oracle writes the same bytes). The oracle links `near-primitives` `=0.37.4` with `solomon` and `clock`,
`reed-solomon-erasure` `=6.0.0` and `zstd` 0.13.

- **Reed-Solomon.** GF(2^8) with polynomial 29 (tables as `build.rs`; `Gf.mulSpec` by shifting is checked against the
  tables on all 65536 pairs), the systematic matrix `V * (top V)^-1`, `encode`, `reconstruct` (the first `data` shards
  present), and the wrappers of `reed_solomon.rs`. Checked against the crate on every product, quotient and power, `num_data_parts`
  for 0 to 255 parts at 0.6 (the `f64` truncation is reproduced with Lean's `Float`), the parity of random data for 16 code shapes up to
  (171, 84) and (1, 255), 228 reconstructions (from nothing missing to everything missing, with the crate's errors) and 689
  wrapped encodings and decodings (`reed_solomon_decode` with the length one short and one long).
- **Chunks.** `produceChunk` is `ShardChunkWithEncoding::new` for protocol 86 (header V3 over inner V5, signed): 30 chunks
  with two to ten parts, one to a few hundred transactions bytes and receipts of several shard layouts (V0, V1, V2
  boundaries) match the crate byte for byte (shard chunk, encoded chunk, every merkle path, chunk hash), as do the receipt
  proofs (`create_receipts_proofs_from_outgoing_receipts`, whose three functions the oracle transcribes since `near-chain` is not
  linked; the same Lean code already agreed with the roots of 1024 real blocks) and 120 `create_partial_encoded_chunk` results.
  *Found:* the root over the per-shard receipt hashes merklizes them as values (a hash of the hash is the leaf), unlike a
  list of leaf hashes.
- **Signed messages.** `Approval::new` (24, endorsements and skips), `ChunkEndorsement::new` (12), `PartialEncodedStateWitness::new`
  and `generate_state_witness_parts` for 1 to 8 validators and witnesses of 0 to 5000 bytes (32 sets, 144 parts), the
  acknowledgement, all byte for byte. The signatures are Ed25519 of the Lean `Impl`, not constant time.
- **Zstd.** `compressStored` writes frames of raw blocks (window 2^17, no content size, no checksum). The decoder of the node and the
  `zstd` crate (stream decoder, as the witness is decoded) both read the eight frames of `zstd-stored.jsonl` (inputs of 0 to
  131073 bytes), which the node writes and `just node-validator-oracle` re-verifies with the crate.
- **Blocks.** `produceBlock` is `Block::produce` for header V6 and body V2 with the VRF of `get_block_metadata`: 40 blocks over
  1 to 4 shards, skipped heights, new and old chunks, the four clock cases (before, equal, after the previous timestamp), a minted amount,
  a shard split and 0 to 4 approvals match the crate byte for byte, and `Block::check_validity` accepts each.
- **Not in M8b:** the witness itself (`ChunkStateWitness` from the chain), `AccountData` and routed message signing (the network oracle,
  M8c), the Doomslug state machine, the epoch queries.

#### M8c and M8d, production paths and acceptance (done)

Gates: `just node-validator-tests` (49 checks), `just localnet-validator`. Sources: `NearNode/Validator/{Doomslug,Inclusion,
Produce,Wire,State,WitnessMake,Node,Endorse,Follow,Drive,Run}.lean`, the `validator` subcommand of `near-lean-node`,
`tools/localnet/validator_accept.py`.

- **What runs.** The node connects to neard, follows the chain, and as validator `node1` signs approvals, produces blocks
  (`produceBlockOn` reproduces all 1024 corpus blocks) and chunks (one shard, empty chunks: there is no transaction pool),
  distributes the partial chunks, creates the state witness (the full-trie base state, a superset of the recorded proof),
  sends the witness parts, checks the witnesses of neard by recomputing its own skeleton, and sends endorsements. The
  Doomslug timers and thresholds follow the reference; the node signs `AccountData` and routes messages by account.
- **Topology.** Two validators of equal stake, one shard, epoch length 30; only `node0` is `neard`, `node1` is the Lean node.
  Neither can finalize alone, so the run proves that neard needs the Lean node.
- **Found: the kickout thresholds.** neard reads the epoch config from the genesis only for a chain id that starts with
  `test-chain-` (`EpochManager::new_arc_handle`); otherwise it builds the fixed test config (thresholds 90/90/80). A
  validator that missed 12 % of its blocks in an epoch was kicked out by neard while the Lean node (reading thresholds
  of 0 from the genesis) kept it, and neard rejected the next block with `InvalidNextBPHash` and banned the peer. The
  validator topology now uses the chain id `test-chain-safe-near-validator`, thresholds of 0 and the inflation rate 1/40
  (the generated genesis says 1/20, the test config 1/40), so both sides read the same config. Other topologies keep the
  default config, which the Lean `EpochConfig` defaults mirror.
- **Acceptance (last run, 240 s, 11 epochs).**

| Check | Result |
|---|---|
| Blocks produced by Lean, accepted into neard's chain | 181 (neard 159) |
| New chunks by Lean in neard's chain | 187 (neard 152) |
| Blocks applied by Lean with the same hash as neard | 340 of 340 |
| Chunk state roots equal | 334 of 334 |
| Head / final height | 345 / 343 |
| Witnesses of neard checked valid, invalid | 152, 0 |
| Disconnects, failures | 0, none (refused connections before neard listens are retries) |
| Stall test: Lean stopped 12 s | head 333 -> 333 (neard alone cannot finalize), resumed to 345, final 331 -> 343 |

  Three earlier runs after the fix (130 s) also passed; before it, three of the runs I watched were banned at an epoch boundary.
- **Deferred.** Chunks are empty (no transaction pool, no `ForwardTx` use beyond receiving), no fork choice (the node
  follows one chain), no persistence (the node starts from the exported genesis corpus), no `ChunkContractAccesses`,
  inline apply stalls the event loop for a few seconds on heavy blocks (block 75 took 7.5 s in one run; closed by H2), the witness is not
  really compressed (stored zstd frames), the signer is not constant time, and a witness from neard is checked by
  recomputing the node's own skeleton, not by replaying the transitions independently. Kickouts are off in the
  validator genesis, so the kickout path of a Lean validator is exercised only by the conformance corpora.
- **Doubts.** The exporter binary was not rebuilt for the genesis-only chain fix (the harness works around it). The run
  is timing dependent: the Lean node missed a few chunks per epoch in every run, which is why the kickout bug showed.

### M9 RPC and operability

#### M9a, transaction pool (done)

Gates: `just node-validator-tests` (the pool tests), `just localnet-validator` (which now needs transactions in Lean's
chunks). Sources: `NearNode/Validator/{Pool,Prepare}.lean`, `Follow.lean` (`buildChunk`), `Drive.lean` (`processTx`,
`dropIncluded`), reference `chain/pool/src/lib.rs`, `chain/client/src/{rpc_handler,chunk_producer}.rs`,
`chain/chain/src/runtime/mod.rs` (`prepare_transactions_extra`), `chain/chain/src/store/utils.rs`.

- **Pool.** One `Pool` per shard in `VState.pools`: groups by `(signer, public key)` keyed by `hash(borsh(pk) ++ seed ++ account)`,
  visited round robin in key order after the last key used; duplicates by hash; the `transaction_pool_size_limit` (100 MB);
  `remove` for the transactions a block includes; `prepare` is the loop of `prepare_transactions_extra` (gas limit
  `process_tx_limit` of the shard's congestion, the 4 MiB `combined_transactions_size_limit`, the strict-nonce gap rule, the
  reintroduction of the prepared transactions). Not ported: the time limit and the storage proof soft limit, the early
  preparation job, the SPICE queue.
- **Per transaction.** `Prepare.admit` follows `prepare_transactions_extra`: congestion of the receiving shard, validity period
  (`check_transaction_validity_period`), the signer's account and key read from the trie of the previous block's state (the
  node's own trie, no decoding of the shard) with the changes of the earlier transactions of the chunk in an overlay, and the
  runtime's `convertTransaction` (what applying the chunk runs) for nonce, balance, allowance and storage stake. Entering the
  pool (`process_tx_internal`): version, size, actions, signature, validity period and the same check at the tip.
- **Forwarding.** A `ForwardTx` from the peer is processed as `is_forwarded`; a node that is a chunk producer of the shard
  pools it. `forwardTx` sends to the chunk producers of the heights 1 to 3 and 7 after the tip (`tx_routing_height_horizon` 4).
- **Not supported.** Gas-key transactions (the model has no gas keys) and ML-DSA keys are refused at the pool.
- **Acceptance.** `validator_accept.py` reads every transaction of a Lean chunk from neard's `chunk` RPC, asks neard for
  `EXPERIMENTAL_tx_status` and compares the outcome of the transaction and of each receipt (id, gas burnt, tokens burnt, executor,
  status kind, receipt ids) with the outcomes the Lean node computed when it applied the block (`applied.jsonl`), failing if
  there are none or any differ. Last run (100 s): 12 Lean chunks with 46 transactions, 276 outcomes checked, 276 equal; 154 block
  hashes and 152 state roots equal.

#### M9b, JSON-RPC server (done, except the points listed)

`NearNode.Rpc.*`; reference `chain/jsonrpc/src/lib.rs`, `chain/jsonrpc-primitives`, `chain/client/src/view_client_actor.rs`.

- **Server.** HTTP/1.1 over the node's own `Net` listener (keep-alive, chunked bodies, one task per connection, CORS), `POST /` JSON-RPC
  2.0 and `GET /status`, `/health`, `/network_info`. Errors have the shape of `RpcError` (`REQUEST_VALIDATION_ERROR` /
  `HANDLER_ERROR` / `INTERNAL_ERROR`, `cause`, `code`, `data`) and the HTTP status of `rpc_handler`.
- **Methods.** `status`, `health`, `network_info`, `gas_price`, `block`, `chunk`, `query` (`view_account`, `view_code`,
  `view_access_key`, `view_access_key_list`, `view_state`, `call_function` through the node's own `Wasm.Near.run` with a view
  context), `tx` / `EXPERIMENTAL_tx_status` (outcomes with proofs, receipts, `wait_until`), `send_tx`, `broadcast_tx_async`,
  `broadcast_tx_commit`, `validators` (current epoch from the aggregator, finished epochs from their blocks),
  `EXPERIMENTAL_protocol_config`, `EXPERIMENTAL_genesis_config`.
- **Transactions.** The RPC hands a transaction to the node's loop (`Env.txQueue`, drained by `tick`), which runs `processTx`
  (the same entry as a forwarded transaction), so a transaction sent to the Lean node enters its pool, is forwarded to the chunk
  producers and lands in a chunk.
- **Data the RPC needs** is kept in `VState` (`canon` height index, `outcomes`, `txIndex`, `receiptsById`, yielded receipts) and in the
  store (columns `chunkBody`, `outcome`, `receipt`, `txIndex`, `delivered`).
- **Acceptance.** `just node-rpc-conformance` (`tools/localnet/rpc_conformance.py`): brings up neard (node0) and the Lean validator (node1),
  runs the finite workload, sends one request set to both RPCs and compares the answers field by field, then sends transactions
  through the Lean RPC, then kills the Lean validator and starts it again from its store. `serve` only brings the topology up,
  `check` runs the request set against a topology that is up. Head-dependent requests are repeated until both nodes answered at the
  same head. The result is written to `rpc-conformance.json` in the work directory.
- **Normalisation (the whole list).** `status`: `version`, `rpc_addr`, `uptime_sec`, `validator_account_id`, `validator_public_key`,
  `node_public_key`, `node_key`. `network_info`: peers and known producers compared as a count, traffic counters dropped. In every
  response: the `gas_profile` and `contracts` members of an outcome's `metadata` are dropped (the `version` is compared: 1 for a
  transaction, 4 for a receipt); and a `Failure` that the Lean node answers with the string `<unrendered failure>` (an error kind it
  does not map) is taken as equal, and counted per group. Every other failure, rendered by the Lean node as nearcore does
  (`ActionError` with the index and kind), is compared as it is. Kinds rendered: all account, key, stake and delegate-action kinds,
  `FunctionCallError` for host errors, traps and `MethodResolveError`. Not rendered: compilation and link errors, gas-key errors,
  `NewReceiptValidationError`, global-contract errors; no request of the set meets them.
- **Last run** (one full `run`, 492 requests, 492 equal, no unrendered failures): block 79/79, chunk 64/64, `query` 114/114,
  `tx` 150/150, `EXPERIMENTAL_tx_status` 37/37, `gas_price` 6/6, `validators` 4/4, protocol and genesis config 6/6, status,
  health, network_info 3/3, errors 2/2. Transactions through the Lean RPC: `send_tx`, `broadcast_tx_async` and `broadcast_tx_commit`
  one each, all three landed and `tx` at FINAL is equal on both nodes; 8 invalid transactions through `send_tx` and `broadcast_tx_async`
  each, 16/16 same error. Restart: SIGKILL of the Lean validator at final height 353, restart from the store, caught up in 8.5 s, final
  height 362 on both nodes afterwards, 5/5 requests equal after the restart.
- **Not done.** `EXPERIMENTAL_changes` (needs a change log with causes; F3 below), `include_proof` of `view_state`, `view_gas_key_nonces` and the global-contract queries, `light_client_proof`, `next_light_client_block`,
  `maintenance_windows`, `client_config`, `EXPERIMENTAL_receipt`. A request for any of them answers `METHOD_NOT_FOUND`. The gas profile and the
  contracts list of an outcome's metadata are not computed.

#### M9c, persistence and operation (done, except the points listed)

- **Chain store.** The observer's store (blocks, `BlockInfo`, epochs, trie nodes, chunk extras, heads) plus the RPC data above is
  committed with every applied block. `Validator.Persist.resume` rebuilds the `VState` from it.
- **Safety state.** Committed before the act it guards: the largest approval target height (`LARGEST_TARGET_HEIGHT`, as
  `save_largest_target_height`), the last block produced, the chunks produced per (height, shard) and the chunk endorsements. A
  restarted validator never signs a second approval for a height nor produces a second block or chunk for a height.
- **Flags.** `--home DIR` takes `node_key.json`, `validator_key.json`, `genesis.json`, `data/` and, from `config.json`, `rpc.addr`,
  `network.addr` (listen port) and `network.boot_nodes`; a flag on the command line wins. `--log-format text|json` (one JSON object per
  line: `ts`, `uptime_ms`, `level`, `target`, `msg`). `--rpc-addr`, `--genesis-config`, `--store` as before.
- **Shutdown.** SIGTERM and SIGINT (libuv signal handles in `Net.Uv`) end the node like `--stop-file`: the loop leaves, the RPC server stops, the
  store is closed, the report is written.
- **`gc_num_epochs_to_keep` (SAF-8 F1).** `--home` also reads the flattened `GCConfig` key `gc_num_epochs_to_keep` of `config.json`,
  as `ClientConfig::gc_num_epochs_to_keep` uses it: 0 is refused (neard's `config_validate.rs`: "gc config values should all be
  greater than 0") and a smaller value than 3 is raised to `MIN_GC_NUM_EPOCHS_TO_KEEP` (3). `--gc-epochs-to-keep` on the command
  line still wins and keeps its test meanings (1, 2 and 0). `rpc_conformance.py` no longer passes the flag: 492 of 492 requests
  equal with the window read from `node1/config.json` (10000).
- **Not done.** The `config.json` keys other than the four above are ignored; the logs are not per-target levels; there is no
  `neard init`-compatible layout of `data/` (the store is the node's own format).

#### The fork after a pause (M9 acceptance)

`validator_accept.py` stops the Lean node for 12 s (SIGSTOP) and resumes it. On resume both validators have approvals for several target
heights and each produces a block at every height it is producer of on the parent it has: neard produced five blocks 108 to 112 in
12 ms on block 107 (debug logs of `chain`/`client`/`network`, `NEARD_RUST_LOG`), and in another run neard built 104 and 105 on 103
while the Lean node, whose tip was still 103, built 107 on 103 with valid skip approvals; neard received that block, accepted it and
made it its head. The fork choice then orphans the blocks that are not on the chosen chain, whichever node produced them. Nothing
was rejected: every block the Lean node applied was held by neard. The check therefore asks what nearcore guarantees: a block of the Lean
node that is off neard's canonical chain must be held by neard (`block` by hash), and is reported as an orphan; a block neard does not hold
is a problem. Two runs on the final build: 0 orphans, and 4 orphans (107 to 110), both `ok`.

### M10 performance and soak

Gates: `just fastvm-differential`, `just chain-replay-corpus-fast`, `just localnet-follow --lightburst`, `just localnet-soak`.
Sources: `near-lean/fastvm` (`NearFastVM`), `near-lean/runtime/NearRuntime/VmEngine.lean`, `near-lean/node/NearNode/Chain/FastEngine.lean`,
`tools/localnet/soak.py`.

#### M10a, target and profile

**Target (set here, met below).** The node keeps pace with `neard` on the full workload including bursts:

1. `localnet-follow --lightburst` passes its own 240 s catch-up check unchanged on both topologies, and the follower is within
   10 blocks of the head outside the burst;
2. the validator never trails `neard` by more than 10 blocks outside a burst (the 90 s after a burst are excluded; the peak inside
   one is reported), finality advances in every 120 s window, and a one-hour soak shows equal state roots, no disconnect, an
   answering RPC and bounded memory growth;
3. the engine runs at least 100 million Wasm instructions per second on integer loops (the specification ran about 5 million), so
   that a call of 300 Tgas takes seconds, not minutes;
4. a quiet block costs the node under 10 % of the block interval of CPU.

**Before** (the specification interpreter, `main` at 6d53765): block 214 of the full-workload corpus (14 calls of 300 Tgas) took
853 s, 98 % of it in `Near.step`/`runMetered`; under `--lightburst` the follower fell about 250 blocks behind and failed the catch-up
check on both topologies. A quiet single-shard block took 140 ms (36.3 s for 259 blocks): `encode-state` 29 %, `trie-witness` 20 %,
`results` 17 %, `run/interpreter` 9 %, `run/shard-start` 7 %, `run/observe-queues` 8 %, `decode-state` 6 %.

**nearcore's own time for the same work** (`near_apply_chunk_delay_seconds` of the pinned `neard`, scraped from `/metrics` after the
full workload on the single-shard localnet): 379 empty chunks 0.8 ms each; 128 chunks under 100 Tgas 3.4 ms each; the three chunks
of the burst that used 1000 to 1300 Tgas 0.93 s each (2.79 s together); chunks of 600 to 700 Tgas 0.12 and 0.41 s. That is about
1 ms per Tgas where the fast engine needs about 10 ms per Tgas on a pure integer loop (a 300 Tgas `sum_n` call: 2.9 s).

#### M10b, the fast engine (rule 2)

`near-lean/fastvm` (package `NearFastVM`, node-only: `check_node_isolation.py` lists it with `node` and `chain`, and
`check_vm_dependencies.py` forbids the name in `NearVM`'s closure) is the `Impl` of `Wasm.Near.run`. `Wasm.Exec` and
`NearVM.Run` stay the specification, and contract verification keeps using them.

- **Compilation** (`Compile.lean`, lazily, one function at its first call). The body becomes an `Array Ins`: structured control is
  resolved to jumps, the operand stack height is followed statically (the module is validated) so that every operand is addressed by
  its frame slot and a branch knows how many values it carries and where they go. Code after a branch, `return` or `unreachable`
  in the same sequence is not compiled.
- **Execution** (`Exec.lean`, generated by `scripts/gen_exec.py` from the table in `scripts/ops.py`). One self-tail-recursive loop, so
  it is a C loop. A frame is `[locals | operands]` in one `Array UInt32`, a slot being two words (`Float.ofBits` canonicalises
  NaNs, so a `FloatArray` cannot hold an `i64`; an `Array UInt64` allocates). Memory is the `Array ByteArray` of `Wasm.Memory`, so it
  goes to the host functions without a copy; loads and stores touch a page directly, `memory.fill`/`copy` work page by page with
  `ByteArray.copySlice`. Floating point, truncations and conversions go through `Wasm.Numeric` (`Op.cold`).
- **Gas is the specification's, instruction by instruction.** Every instruction carries the charge `nextInstructionGas` gives it
  (`block` and the synthetic jumps none, `loop` and `if` on entry, a branch to a loop twice, memory instructions by their operand,
  a call plus the activation of the callee). The loop keeps the gas spent since the host state was last synchronised in a register and
  the room left before either limit in another; a charge that does not fit is replayed on the host state with `chargeHost`, which is
  what `runMetered` does for each charge, so the error, the burnt gas and the profile are the specification's. The host state is
  synchronised before each host call and at the end.
- **What it does not run, it hands back.** Reference types, tables other than `call_indirect`, `memory.init`, `data.drop`, a module
  with two memories, a gas counter that is already out of range, a free instruction (`minOpCost = 0`), or a caller that fixes the
  interpreter fuel: the run is discarded and `Wasm.Near.run`'s machine runs from the start (a run has no side effect before it
  ends). `NearFastVM.run` has the signature of `Wasm.Near.run`; `Run.lean` repeats `runAttempt` up to the machine (`prepare`) and
  calls `execute` there.
- **Wiring.** `Near.VmEngine` (`runtime/NearRuntime/VmEngine.lean`) is a class with one method, `run`; its default instance (priority
  `low`) is `Wasm.Near.run`. The definitions between `Near.step` and the function-call action take `[VmEngine]` (list in the M10
  report). A theorem that mentions them elaborates the default instance, so no statement changed; the proof of `applyFunctionCall_run`
  uses the new simp lemma `VmEngine.spec_run` (`rfl`). The node imports `NearNode.Chain.FastEngine`, which declares the fast
  instance, so `Near.step` in `ApplyChunk.lean` and the view calls of the RPC run on it. `registered-replay-fast` (package `fastvm`)
  is the corpus replay with the same instance. `ChainReplay.Registered` moved to `RegisteredCore` with a three-line `Registered`
  carrying `main`, because a module that defines `main` cannot be imported by another executable.
- **Differential tests** (`just fastvm-differential`): random well-typed modules (every integer operation with edge operands, loads
  and stores around page and memory ends, bulk memory, structured control with values, `br_table`, direct, indirect and recursive
  calls, floats, and the NEAR host functions with random arguments) run with the gas limits swept over every instruction boundary of
  short runs and a sample of the others, for `prepaid_gas` and for `max_gas_burnt`, comparing every field of the outcome and, for
  the unlimited run, the final machines (memory, globals, gas profile); probes for the cases found while writing it; the wNEAR
  contract of the VM's own test suite through its calls with the gas swept. `chain-replay-corpus-fast` replays the 436 chunks, and
  `chain_apply.py run` (the M5 corpora) runs on the fast engine in the node.
- **Found by the fuzzing, not fixed here.** Host code `Wasm.Near.utf16Units` recurses once per UTF-16 unit and overflows the native
  stack for lengths around a million (`log_utf16` or `abort` with a large length): the process aborts, in either engine. A task has
  been filed; the generator no longer calls these two functions.

Speed: an integer loop of 2.6 million instructions takes 987 ms in the specification and 17 ms in the engine (about 150 million
instructions per second including setup); a 300 Tgas call of `sum_n` takes 2.9 s.

#### M10c, other hot spots

The profile after M10b (single shard, 1000 blocks): `encode-state`, `shard-start` and `results` were conversions between `ByteArray`
and the runtime's `List UInt8` and hashes of contract code, redone for every contract on every block.

- `digestFor`: the encoders are given a digest that does not hash the catalogue's contract bytes again (their label is the SHA-256 of
  exactly those bytes, computed when the code is decoded; the lookup compares the bytes).
- `CodeCache` remembers large byte strings: the label of contract bytes by content (no second SHA-256 when the state is decoded), the
  list of a large value by content (`overlayOf`, `Model.code`) and its inverse for the entries a chunk returns (`results`).
  Cleared at 512 entries.

Quiet single-shard block: 140 ms before, 40 ms after (39.5 s for 1000 blocks including the interpreter time of the light bursts);
`trie-witness` 28 ms to 2.3 ms per block, `observe-queues` 12 ms to 0.7 ms. What remains is `encode-state` (11 ms: `unique` in
`NearRuntime.StateEncoding` compares all keys pairwise, and the runtime is not touched here), `shard-start` (10 ms), `results` (7 ms).
Inline application still blocks the event loop: the full burst (14 calls of 300 Tgas) stops the head for 30 s in the validator
topology (neither validator can progress without the other), everything else is under a second; moving application off the network
thread was done afterwards (H2).

#### M10d, soak (`just localnet-soak`)

`tools/localnet/soak.py` runs the topology of `localnet-validator` for `--duration` seconds (3600 by default) with the full workload
once (host function calls, the 14 calls of 300 Tgas, the 215-block wait for the yield), then light traffic and, every five
minutes, a light burst. It samples every 5 s: heads and final height of `neard`, the Lean node's head over its own RPC (which must
answer `status`, `block`, `gas_price` and a `query`), its RSS and the size of its store; a checker follows `applied.jsonl` and
compares every block hash and every shard's state root with `neard`'s (`prev_state_root` of the next chunk).

| | one hour, 2026-10-25 |
|---|---|
| Duration, blocks | 3597 s, head 3 to 5734 (5813 blocks compared, 5813 hashes equal) |
| State roots | 5712 of 5712 equal |
| Finality | final height 5732 at the end, head minus final at most 10, no 120 s window without progress |
| Lag behind `neard` | at most 2 blocks outside bursts, 1 inside (10 light bursts), median 0 |
| Longest stop of the head | 30 s (the full burst at the start) |
| Disconnects, failures | 0, none; the RPC answered at all 714 samples |
| RSS | 184 MB (first minutes after warm-up) to 277 MB, peak 283 MB; slope 111 MB per hour |
| Store | 20 KB to 34.5 MB, 32 MB per hour |
| Lean blocks / chunks produced | 3337 / 3381, 628 transactions in chunks, 2347 witnesses of `neard` valid, 0 invalid |

Follow with `--lightburst`, default checks (600 s of following, the burst a minute after the node reached the head): single shard
reached the head after 8.3 s, peak lag 5, caught up 6.0 s after the burst (limit 240 s), 1000 state roots equal; four shards 7.3 s,
peak 4, caught up in 5.9 s, 4001 state roots equal; no disconnect on either.

**Not done, doubts.** (The soak used to leave out `sanity_check`, the call that deploys contract code from the memory of a
contract; closed by H1 below.) (Closed by H3 below.) The RSS slope is not flat: the node keeps the trie nodes of its history in memory (the store tables), so memory grows with
the chain (about 3 MB per 100 blocks of this workload); a longer soak needs garbage collection of old state. `encode-state` is still
quadratic in the number of entries. The generator of the differential test covers the integer and control instructions and the
host functions much better than floating point; the engine hands tables, references and `memory.init` back to the specification, so
those are not exercised at all. No equivalence theorem was written; the differential tests are the evidence, as rule 2 allows.

#### Hardening after M10 (SAF-8)

##### H1, code a contract deploys from its own memory

*Cause.* A function call can emit `DeployContract` with bytes it assembled in its memory. The runtime hands its decoder
(`Bytes → ContractCode`) those bytes and keeps only the answer (module, size, hash); the encoders that write the outgoing
receipt then look the bytes up in the chunk's catalogue by hash. The catalogue holds the code of the state and of the incoming
receipts, and of the chunk's own `claimed` outgoing receipts, which a follower reads from the next chunk's body. A validator
applying a block at the head has no next chunk, so the bytes were nowhere and the apply stopped with "code bytes absent from
catalogue" (block 205 of the soak with the full workload, after the `sanity_check` call).

*Fix* (`Chain/ApplyChunk.lean`, `stepLearning`; no runtime definition changed). The decoder is the only place that sees the bytes
and a pure function can return nothing else, so the step runs with `learningCodeOf`: the catalogue's code for bytes it holds, and
for bytes it does not hold a code whose `decodeIssue` carries them as hexadecimal text. A decode issue makes the runtime reject
the whole attempt atomically (`Near.apply` returns the initial state with the issue), so nothing leaks: the node reads the bytes off
the issue, decodes them as `Model.code` decodes the code of an incoming receipt (same label, same module, same decode issue for
bytes that do not decode), adds the entry to the catalogue and the cache and runs the step again, now answering these bytes from
the catalogue. Each rerun gets one distinct deployment further (at most 256 per chunk); a chunk without such a deployment runs
once, as before. The outgoing receipt bytes, the state encoding and every other consumer of the catalogue then see the code.
The cost is one extra run of the part of the chunk up to the deploying receipt per distinct code.

*Evidence.* Before (main, `soak.py --duration 420`, full workload): `block 205: applying the chunks failed: code bytes absent from
catalogue`, node exit. After: the same run passes the call (`sanity-check: ... SuccessValue` at block 212) and ends at block 603 with
613 of 613 block hashes and 595 of 595 state roots equal to neard's. `soak.py` no longer passes `--no-deploy-from-memory` unless
asked to (`--no-deploy-from-memory` is now an option of `soak.py`, off by default). `node-validator-tests` checks the hex text and
the decoder.

##### H2, applying off the event loop

*Cause.* `Env.applyOne` ran `applyBlock` inline in the handler that received the block, so a block of heavy calls (13 to 14 s for
four chunks of 300 Tgas each on the fast engine) kept the loop away from everything else: pings, approvals, RPC state, parts. The
follower already applies on a worker thread (`Network/Apply.lean`); the validator did not.

*Fix* (`Validator/Drive.lean`, following nearcore's split of the client actor from the apply pool). `Env.startApply` snapshots the
chain state and the progress, collects the chunk bodies by shard, and runs `applyBlock` with `IO.asTask` on a dedicated thread; the
`Applying` record (block, bodies, start time, task) is kept in `Env.applying`. `Env.tryApply`, called on every turn of the loop and
whenever a block or chunk arrives, takes the result with `IO.hasFinished` and runs the rest of the former `applyOne` on the loop
(`finishApply`: the new progress into the state, the commit, the applied log), then `onApplied` (Doomslug tip, chunk production,
witnesses that waited) and starts the next block whose parent is applied, so blocks are still applied one after the other and
only the loop thread writes the state. Nothing changes the tip but `onApplied`, so nothing is produced on an unapplied block.

*Found by the first version: the stale tip.* With the loop free, the timers kept running on the tip while the block being applied
was about to replace it. Two things followed in a run of the burst: the node sent `Skip(tip)` approvals for the heights above
the block it was applying, and `tryProduceBlocks` produced blocks with the stale tip as parent (the approvals for it were the
node's own and neard's skips), forking the chain at the block being applied: nine heavy blocks applied instead of four, `neard`
holding none of the extra blocks at their heights, finality stuck for two minutes. In the inline version this could not happen
because the tip moved before the loop looked at the timers. `Env.tipIsStale` is true while a block above the tip is being applied;
then `tick` neither runs `processTimer` (no approval, no `largest_target_height` change) nor produces a block, and counts the turn
(`turnsOnStaleTip`). The timers restart in `setTip` when the block is applied, as after any new head, so there is no burst of skip
approvals afterwards. Approvals are still collected, parts forwarded and served, the RPC answered, transactions pooled.

*Measure* (`Env.noteTurn`: the time between two turns of the loop, which waits at most 20 ms for a message; `loopMaxGapMs` and
`loopStalls`, the turns of a second or more, are in the report). `soak.py --duration 330 --skip hostcalls wait`, the burst of 14
calls of 300 Tgas, the same machine, the same workload:

| | longest turn of the loop | turns of 1 s or more | heavy blocks | roots and hashes equal |
|---|---|---|---|---|
| inline (before) | 13016 ms | 4 | 193, 195, 197 (14.2, 14.1, 13.9 s), 199 (6.7 s) | 453 of 453 |
| thread, tip held while a block is applied | 282 ms | 0 | 185, 187, 189 (12.9, 12.7, 13.8 s), 184, 191 (3.4, 3.3 s) | 448 of 448, no orphan |

The application takes as long as before (the head still waits for the node: with equal stakes neither validator can go on without
the other); what changed is that the loop is not away. A block of quiet traffic costs about 19 % more on the thread (89 ms against
75 ms over 251 blocks: starting a thread, and the objects shared with the loop being reference counted atomically).
`validator_accept.py`: ok, 527 of 527 outcomes equal, the stall test (12 s) stalls and resumes.

##### H3, bounded memory: garbage collection

*Cause.* The node kept everything it had ever applied. The trie nodes the updates replaced were never taken back (`trieDeleteOps`
existed since M4 but nothing called it), and the blocks, their `BlockInfo` and merkle trees, the chunk extras, the receipts in and out,
the chunk bodies, the outcomes and the RPC indexes stayed in `VState`, in the progress and in the store's tables. The census of a
run (`VState.census`, logged every 100 heights) showed all of them growing with the height; a 15 minute soak without collection:
1300 blocks, 10692 trie entries, RSS 150 to 211 MB, slope 193 MB per hour after the first two minutes.

*Fix* (`Validator/Gc.lean`, `Store/Trie.lean`, `Chain/Apply.lean`; the reference is `chain/chain/src/garbage_collection.rs` at
the pin). Every applied block keeps the reference changes of its chunks' tries in the new `TrieChanges` column (`DBCol::TrieChanges`:
insertions and deletions as hash and count). `get_gc_stop_height_impl` is ported (`gcStopHeight`): the first height of the oldest of
the last `gc_num_epochs_to_keep` epochs (default 5, `--gc-epochs-to-keep N`, 0 collects nothing). After each applied block
`collectGarbage` collects the heights from the tail to that stop height, `gc_blocks_limit` (2) at a time and faster when far
behind. For the canonical block `B` at a collected height it applies `B`'s trie deletions (`apply_deletions`: `rcAdd` with the
negative counts, so a node a retained state still references survives) and drops the data of `B`'s parent; for any other block at the
height (a fork, found by walking from the tip) it takes back its insertions (`revert_insertions`) and drops it. Dropping a block
removes its entries in the store (block, header, `BlockInfo`, merkle tree, chunk extras, incoming and outgoing receipts, delivered
receipts, trie changes, chunk bodies, outcomes, receipts and the transaction index) and the same in the chain state, the progress
and the maps of the RPC. One pass is one store commit that also writes `TAIL`, and the same operations go to the progress'
view of the tables, so a restart continues from the tail it finds. It runs between two applications only: an application works on a
snapshot of the state and replaces the progress when it ends, which would undo a collection made meanwhile.

Also: a witness stops keeping its parts once it is rebuilt (they were kept for ever), witnesses and produced chunks below the tail
are forgotten, and the produced-chunk record read back at a restart had its pair in the order the running node does not use
((height, shard) against (shard, height)), so a restarted node could have produced a chunk a second time: fixed.

*Evidence* (census lines and `soak.py`; the one-hour result with the default window is in the acceptance table below).

| run | window | blocks | trie entries at the end | RSS | slope after 120 s |
|---|---|---|---|---|---|
| no collection (the code before) | all | 1300 | 10692 | 150 to 211 MB | 193 MB/h |
| `--gc-epochs-to-keep 2` | about 60 blocks | 1075 | 899 (stays between 700 and 900) | 148 to 174 MB, peak 198 | 54 MB/h over the 10 minutes |

The retained chain state, maps and tables stay at the size of the window (`census: chain 53 blocks ... trie 864 entries` after 1000
heights collected); roots and hashes are equal to neard's throughout (1052 of 1052). Forks: with the window at one epoch and the
Lean node stopped for 12 s at different times (`validator_accept.py --gc-epochs 1 --stall-at N`) the collection took back 1, 4 and 2
fork blocks in three of four runs (orphans 93; 104 to 107; 115, 117), all runs `ok`. Restart: `soak.py --gc-epochs 1 --restart-at 240`
kills the node with SIGKILL after 305 blocks, 235 of which are collected, starts it from the store ("continuing from the store at
height 305"), and ends with 916 of 916 roots equal, the lag bound kept, collection going on (379 heights).

A node with a window of 5 epochs answers `block`, `tx` and the other RPC methods for the heights of the window only, as `neard`
does; older ones are `UNKNOWN_BLOCK` (the RPC conformance run with a one-epoch window compares the old transactions of its
workload against a `neard` that still holds them, which is why that run uses the default).

*Not done.* Blocks that were accepted but never applied (a fork whose chunk bodies never came) are collected with the height but
have no trie changes to take back; state parts, the state-transition data and the witness cache of nearcore do not exist here. The
store's log still grows between compactions (55 MB per hour of this workload at the 64 MiB limit) and the compaction rewrites it
from memory; a disk-resident tier is still not there. Contract code (`CodeCache.byLabel`) is not collected: it grows with the
distinct contracts deployed, not with the height. (Both closed by F2 below, except the disk-resident tier.)

##### Acceptance of the hardening (one run of each, on the final build)

| Run | Result |
|---|---|
| `soak.py`, 3595 s, full workload (`sanity_check` included, no `--no-deploy-from-memory`), default window of 5 epochs | head 3 to 5768, final 5766; 5840 of 5840 block hashes and 5747 of 5747 state roots equal, no orphan; head minus final at most 10, no window without finality; lag at most 2 outside bursts, 1 inside (10 light bursts), median 0; no disconnect, RPC answered at all 714 samples; Lean produced 3406 blocks and 3381 chunks (659 transactions), 2381 witnesses of neard valid, 0 invalid; longest turn of the loop 157 ms; 5642 heights collected; **RSS 167.8 MB after warm-up to 180.8 MB, peak 211.4 MB, slope 11.6 MB/h** (111 MB/h before) |
| `validator_accept.py` (1) | ok: 365 blocks applied, 363 same hash and 2 orphans neard holds, 361 of 361 roots, 537 of 537 outcomes equal, 129 transactions in 50 Lean chunks, 167 witnesses valid, stall test stalled and resumed |
| `validator_accept.py` (2) | ok: 365 applied, 364 same hash and 1 orphan, 359 of 359 roots, 531 of 531 outcomes, 119 transactions in 42 chunks, 157 witnesses valid, stall test ok |
| `follow_accept.py --lightburst --topologies single sharded` | single: head reached after 7.3 s, max lag 8, 1001 of 1001 roots, caught up after the burst; sharded: 7.2 s, max lag 6, 4003 of 4003 roots, caught up; no disconnect; `localnet-follow: all agree` |
| `rpc_conformance.py run` | 491 of 491 requests equal (block 79, chunk 63, tx 150, query 114, ...); the three transactions through the Lean RPC landed; SIGKILL at final height 335, back in 8.5 s, final 343 on both |

In the `validator_accept.py` runs the longest turn of the loop is the 12 s pause the test imposes with SIGSTOP; the outcomes
check lists a few `408` answers of neard's `EXPERIMENTAL_tx_status` for transactions of the last blocks, which cannot be final
once the Lean node (half the stake) has been stopped, and does not count them. `rpc_conformance.py` starts the Lean node with
`--home node1`, so it reads `gc_num_epochs_to_keep` (10000, which `localnet.py` writes for neard) from `config.json` like neard
does, because its requests ask for the first epochs (F1 below).

##### Follow-ups after the hardening (SAF-8 F1 to F5)

Branch `claude/saf-8-node-followups`. F1 is described under M9c (`gc_num_epochs_to_keep` from `config.json`). Reference for F3:
`core/store/src/trie/update.rs`, `core/primitives/src/types.rs` (`StateChangesKinds`), `runtime/runtime/src/{lib,verifier}.rs`,
`core/store/src/utils/mod.rs` (`remove_account`), `chain/jsonrpc/src/lib.rs`.

###### F2, bounded files and bounded code cache

*Store log.* H3 left the store's log growing between the 64 MiB compactions (55 MB an hour of the soak workload). `Options.minLog` and
`logPercent` add a second rule: when the log is longer than `minLog` bytes and longer than `logPercent` percent of the last snapshot,
the next commit compacts. `Options.node` (what the node opens its store with) is 4 MiB and 100 %, so the files stay within a constant
factor of the live data: the snapshot, a log of at most the same size, and the next snapshot while it is written. The store keeps the
snapshot's size in its `info` (`snapSize`); the cap of 64 MiB still applies. `node-store-tests` (`ratioCompaction`): the same 200 keys
are overwritten 3000 times; without the rule the files grow with the commits, with it they stay below three times the live data plus
the minimum log, the store compacts at least five times, and a restart finds the same content and generation.

*Code cache.* `CodeCache.byLabel` (and `labels`, `lists`) grew with the number of distinct contracts ever deployed. `CodeCache.prune`
keeps a code only while a `State` entry with a positive count holds a value of its hash, which is how nearcore holds contract code in
the trie (the `State` column stores it under `sha256(code)`, and garbage collection takes the count back with the last state that held
it). `Env.pruneCodes` runs after garbage collection, between two applications (an application replaces the progress, cache included),
and only when the cache has doubled since the last pruning (at least 32 entries), so the scan of the `State` counts is amortised.
Everything dropped is a cache of work that `Model.code` does again on the next use, so pruning changes no result. The counter
`codesPruned` is in the node's report. Test: `node-validator-tests` (`codePruning`).

###### F3, state changes by kind (`EXPERIMENTAL_changes_in_block`, `block_effects`)

nearcore keeps in `DBCol::StateChanges` one `RawStateChangesWithTrieKey` (the key and a list of `(cause, value)`) for every trie key
that a block's chunks passed to `TrieUpdate::set` or `remove`, and `EXPERIMENTAL_changes_in_block` lists the kind of each account,
contract code, access key and contract data key (`StateChangesKinds::from_changes`, one entry per key, in key order, whatever the
cause). The Lean runtime returns the state after a chunk, not a log of the writes, so the node keeps what it can know.

- *Storage.* New column `stateChanges` (id 20), one record per block and `ShardUId` (the key of `TrieChanges`), written with the
  block's other operations and deleted with the block by garbage collection: the raw keys of the four kinds and whether the entry
  is gone. `Chain/StateChanges.lean`. The RPC reads the records of all shards of the block, sorts the keys as RocksDB would, and
  answers with `account_touched`, `access_key_touched`, `data_touched` and `contract_code_touched`. A block outside the window is
  `UNKNOWN_BLOCK`, as everywhere else.
- *What differs.* The keys whose entry differs between the pre-state and the post-state of the chunk (`diffEntries`, the same
  list the trie update uses).
- *Written without a change, derived as nearcore writes them* (`writtenKeys`): (1) `update_validator_accounts`: `set_account` for
  every account of `stake_info` that exists in the shard and for the protocol treasury when it is not one of them, so the first block
  of every epoch, and block 1, list the validators and the treasury though the values may not change; (2) `verify_and_charge_tx_ephemeral`:
  the signer's account and access key for every transaction of the chunk; (3) `apply_action_receipt`: `set_account` of the receiver
  after the actions of a receipt that succeeded and left its account in place (a failing receipt rolls its writes back, so only
  successful outcomes count, and only when the account exists before and after the chunk); (4) `remove_account` removes `Account`
  and `ContractCode` whether or not the account had code, so a deleted account lists a code key.
- *What it cannot know, and keeps as a diff.* The VM returns the final state of the contract, not its writes. A `storage_write` of the
  value the key held, a `storage_remove` of a key that is not there, a write that a later write of the same chunk restores, and an
  account created and deleted in one chunk are listed by neard and not by the node. In the live data the gap is one key: the `ft`
  contract of the workload removes a 64-byte key of `a` (block 54: neard lists it with the value `None`, and the node's diff has
  no entry, so the key was absent before the chunk, or created and removed in it). The harness classifies a request as a *known gap* only when the Lean list equals neard's list
  with extra `data_touched` entries removed; any other difference stays a failure. Known gaps are reported separately and are not counted
  as equal (`rpc_conformance.py`: `known_gaps` in the table, the `GAP` lines name the block and the account, `rpc-conformance.json`
  lists them).
- *Found with a live neard.* The first version (the diff alone) matched 290 of 304 `changes_in_block` requests. The 14 others, read
  with `EXPERIMENTAL_changes` (which gives the cause of each change) on a neard kept running: block 1 and the epoch starts (validator
  accounts update, 3 and 4 keys, `near`, the validators and a staker whose value did not change), blocks where a receipt wrote the receiver's
  account back unchanged next to a new access key (cause `receipt_processing`), the code key of a deleted account (`remove_account`), and the
  `ft` data key. After the derivation: 299 of 304 equal and the 5 known gaps, with no other difference.
- *Also fixed on the way.* The chunk view rendered a `GlobalContractDistribution` receipt as `null`; it now renders
  `ReceiptEnumView::GlobalContractDistribution` (the hash of the code, the nonce only for version 2). A run whose sampled chunk held
  such a receipt had shown the difference.
- *Result* (`rpc_conformance.py run`, final build): **783 of 789 requests equal, 6 known gaps, 0 other differences**. The 6 gaps are
  `EXPERIMENTAL_changes_in_block` of blocks 54, 60, 65, 71, 73 and block 54 again by hash, each with one `data_touched` of `ft.node0`
  that neard lists and the node does not. 291 of the 297 `changes_in_block` requests (every block of the run by height, a sample by hash,
  `final`, `optimistic`, `near-final`, `block_effects`, the error cases) are equal.
- *Deferred: `EXPERIMENTAL_changes`.* It returns the values with their causes (transaction hash, receipt hash, `action_receipt_gas_reward`,
  `validator_accounts_update`, ...), several per key in the order they happened. That needs a change log in the runtime (each write with
  the cause that led to it), which the model does not have and which is not added here. It answers `METHOD_NOT_FOUND`.

###### F4, gas profile of outcomes: not done here (done in R3 below)

The metadata of an outcome (`gas_profile`, and the list of contracts) is not computed and the conformance harness removes both from
the comparison. The runtime's `ExecutionOutcome` has no profile and the VM's profile lacks the split by action (`ActionCosts`) that
nearcore's `ProfileDataV3` carries, so filling it needs a change in `near-lean/runtime` and `near-lean/vm`, which this work does not
change. Left as it is.

###### F5, `utf16Units` without recursion

`Wasm.Near.utf16Units` (the host's decoding of `log_utf16` and `abort` messages) recursed once per code unit and overflowed the native
stack at around a million units (3 M units: the process aborts, in either engine). It is now `utf16UnitsLoop` with an accumulator
(tail recursive, a loop in compiled code), and the recursive definition stays as `utf16UnitsOld`, the specification, with
`utf16UnitsLoop_eq_old` and `utf16Units_eq_old` proving the two equal on every input (axioms: `propext`, `Quot.sound`). It is the only
change in `near-lean/vm`: no other definition, statement or proof moved, and `LogRead.lean` (the one user) is untouched. With 10 M
units the new function runs. Builds with `--wfail`: `near-lean/{vm,runtime,chain,fastvm,node}`, and `contracts/w-near/verification`
(`Model`, `Spec`, `runtime-adapter-tests` pass with `--wfail`; `Proofs` builds, with the one `sorry` it already has,
`refines_wnear_exported`; it is the only package of `contracts/*` that requires the runtime). `vm-tests`: 193 passed. The differential
generator calls `abort` again: `fastvm-differential`, 200 programs, 42037 outcome comparisons, **0 mismatches**.
`near-lean/vm/NearVM/Utf.lean` is not reformatted: the formatter would rewrite definitions that F5 does not touch, and the rule for
shared packages is that F5 is the only change.

###### Acceptance of the follow-ups (one run of each, on the final build)

| Run | Result |
|---|---|
| `rpc_conformance.py run` | **783 of 789 requests equal, 6 known gaps (the `data_touched` of F3), 0 other differences**; block 78/78, chunk 65/65, `tx` 150/150, `EXPERIMENTAL_tx_status` 37/37, `EXPERIMENTAL_changes_in_block` 291 equal + 6 gaps of 297; the three transactions through the Lean RPC landed; SIGKILL at final height 329, back in 8.5 s, final 338 on both |
| `validator_accept.py` | ok: 365 blocks applied, 364 same hash and 1 orphan (348), 360 of 360 state roots, 512 of 512 outcomes equal (3 `408` answers of `EXPERIMENTAL_tx_status` for transactions of the last blocks, not counted), 113 transactions in 41 Lean chunks, 155 witnesses valid, stall test (12 s) stalled and resumed |
| `soak.py --duration 2400`, full workload | `localnet-soak: all agree`: head 3 to 3835, final 3833; 3892 of 3892 block hashes and 3825 of 3825 state roots equal, no orphan, 6 light bursts; head minus final at most 10; lag at most 2 outside bursts, 1 inside, median 0; no disconnect, the RPC answered at every sample; **RSS 163.9 MB at the start, 158.1 MB at the end, peak 194.2 MB, slope 8.4 MB/h; store 21 KB at the start, 2.1 MB at the end, between 1.4 and 6.7 MB after the first window** |

The soak series from `soak.json` (mean and maximum RSS and the range of the store size over each five minutes, with the head at the end of the window):

| seconds | RSS mean / max (MB) | store min .. max (MB) | head |
|---|---|---|---|
| 0 | 156.4 / 194.2 | 0.02 .. 4.05 | 411 |
| 300 | 166.3 / 182.0 | 1.68 .. 6.67 | 906 |
| 600 | 160.7 / 186.1 | 1.45 .. 5.85 | 1390 |
| 900 | 163.4 / 186.1 | 2.10 .. 5.34 | 1882 |
| 1200 | 162.7 / 186.2 | 1.43 .. 5.55 | 2365 |
| 1500 | 165.7 / 186.2 | 1.69 .. 5.61 | 2857 |
| 1800 | 163.0 / 186.3 | 1.50 .. 5.83 | 3341 |
| 2100 | 164.8 / 185.7 | 1.49 .. 5.65 | 3835 |

Both are flat after the first minutes: the store falls back at each compaction (the sawtooth between 1.4 and 6 MB) where H3's soak
grew by 32 MB an hour (55 MB an hour of log before F2), and the RSS stays at 160 to 166 MB. The window is 40 minutes, not the hour
of H3 (the slope of 8.4 MB/h is the harness's fit after its warm-up of 600 s, against 11.6 MB/h in H3's hour).
One first start of `validator_accept.py` failed at "neard did not start": the driver script had removed the topology directory
while the previous run was shutting down; nothing of the node ran. The result above is the one complete run.

#### Logs from the VM and the runtime (SAF-8 R1 to R3)

Branch `claude/saf-8-node-runtime-logs`. F3 and F4 above left three gaps that need something the VM and the runtime do not return: the
keys a contract wrote without changing them (`changes_in_block`), the values with their causes (`EXPERIMENTAL_changes`) and the gas
profile of an outcome. They are closed by **output fields that are observational only**: each has a default; it is computed beside the
existing results from what the call or the receipt did; nothing in `near-lean/vm` or `near-lean/runtime` reads it back, so no existing
field, definition behaviour or theorem statement moved. Where a proof broke only because a structure gained a field it was fixed
mechanically (listed per item). The fast engine produces the same fields (it runs the same host functions), and its differential test
compares them.

##### R1, the storage-write log: the 6 gaps of `changes_in_block` are closed

- *VM.* `Wasm.StorageWrite { key, existed, value }` (the key, whether it held a value just before, the value after, `none` for a removal),
  `NearState.storageLog` (newest first), written by `updateStorageUsage`, the post-processing that every `storage_write` and `storage_remove`
  passes on success (so a write of the value the key held and a removal of a key that is absent are logged, as `RuntimeExt::storage_set` and
  `storage_remove` hand each call to `TrieUpdate`), and `VMOutcome.storageWrites` (call order; empty for a failed call, whose storage is
  restored). Changed definitions: `updateStorageUsage` (one more field in the state it returns), `outcomeOfExecution` and
  `VMOutcome.graphIssue` (one more field each).
- *Runtime.* `ExecutionOutcome.changes`, the commits that a transaction or a receipt made to the exposed kinds of trie key (account,
  access key, gas key nonce, contract code, contract data), each `{ cause, key, value }`, `ApplyResult.changes` gathering them in the order
  `Runtime::apply` makes them. `ChangeLog.lean` derives them as nearcore commits them: `TransactionProcessing` (the signer's key and account),
  `ReceiptProcessing` of a receipt that succeeded (a receipt that fails rolls back: no commit) with the receiver's account, the keys its
  actions wrote (`actionKeys`: deploy, add and delete key with the nonce rows of a gas key, implicit account creation, allowance refunds,
  `UseGlobalContract` removing local code, gas key funding and withdrawal, the delegate's nonce, and for `DeleteAccount` everything
  `remove_account` removes: the account, the code, every access key, nonce row and data key) and the VM's storage calls, then
  `ActionReceiptGasReward` (the receiver's account with the reward, when positive), and `ValidatorAccountsUpdate` (`Epoch.lean`). The value
  of a commit is what the state holds for the key at that point; a key written twice before a commit is one entry (`TrieUpdate::commit`).
  `ActionReceiptProcessingStarted`, `PostponedReceipt`, `UpdatedDelayedReceipts`, `Migration` and the bandwidth scheduler commit only
  keys that `StateChangesExt::from_changes` drops (received data, postponed receipts, queues), so they have no entry.
  Added: `Exec.dataWrites`, `Processed.execs` (each receipt that ran, with its result), `ExecutionOutcome.changes`,
  `ApplyResult.changes` (a function of the outcomes), and the functions of `ChangeLog.lean`; changed: `Exec.recordVMOutcome` (one more
  field), `runActionReceipt` / `processedExecOutput` (one more field), `Processed.append`, `applyAttempt` (the outcomes of a receipt
  and of a transaction carry their commits).
- *Node.* The record of a block and shard (`stateChanges` column) is the set of keys the log lists, with whether the last value is a removal;
  `changes_in_block` lists their kinds. Any entry that differs between the pre-state and the post-state and that the log did not list is still
  listed and reported on stderr (`warning: the state change log of shard ... missed ...`): the entries are authoritative, and a miss is a bug of
  the derivation. The `writtenKeys` derivation of F3 (from transactions and outcomes) is gone.
- *Mechanical proof fixes.* `ProcessedFunding.lean` (`processedExecOutput`, the definition the proofs compare `runActionReceipt` with, sets
  the new `execs` field), `BlockStages.lean` (the mirror of the loops of `applyAttempt`: the transaction outcome carries its commit and the
  outcomes of a receipt come from `outcomesWithChanges`); nothing else in `near-lean/{vm,runtime}` changed. No theorem statement changed.
- *Result* (`rpc_conformance.py run`): 788 of 788 requests equal, **0 known gaps** (the category is gone from the harness), 296 of 296
  `EXPERIMENTAL_changes_in_block` requests equal; no `missed` warning in the node's log. A first run with the derivation reading the state
  after the receipt instead of before it reported 3 misses (an implicit account created by a transfer, a deleted account's 30 data keys): the
  warning is what found it.

##### R2, the state change log with causes: `EXPERIMENTAL_changes` for every `changes_type`

- *Runtime.* Nothing new: R1's `ExecutionOutcome.changes` already carries `{ cause, key, value }` for every commit, in the order of
  `Runtime::apply`; R2 reads it.
- *Node.* The record of a block and shard in the `StateChanges` column is now what nearcore keeps: the Borsh
  `Vec<RawStateChangesWithTrieKey>` of the exposed kinds, for each trie key the chunk's commits touched the `(cause, value)` list in the
  order of the commits (`Chain/StateChanges.lean`: `rawChanges`, `causeOf`, `valueBytes`). The runtime's logical receipt ids are mapped to
  native hashes through the chunk's `context.receipts` and `txHashes`; values are encoded as the trie stores them (account with its code
  hash and storage usage, access key, gas key nonce as 8 bytes LE, code bytes, data). The record stays in the store for the GC window.
  `changes_in_block` lists the kinds of the keys of the record (`StateChangesKinds::from_changes`: gas key nonce rows are not a kind).
- *RPC.* `EXPERIMENTAL_changes` (and `changes`) for `account_changes`, `single_access_key_changes`, `all_access_key_changes`,
  `contract_code_changes` and `data_changes` (with `key_prefix_base64`), rendered as `StateChangeWithCauseView` (`StateChanges::from_changes`,
  gas key nonce updates appearing among the access key changes). `single_gas_key_changes` does not exist at protocol 86. Request parsing
  reproduces serde's messages, including a `changes_type` given as the index of the variant (0 to 4).
- *Harness.* `rpc_conformance.py` asks for each kind of change at every block that touched it (by height and by hash), `finality`,
  `sync_checkpoint`, key prefixes, unknown accounts and the malformed requests. *Result* (`rpc_conformance.py run`): 1101 of 1101 requests
  equal, 0 known gaps, 0 other differences.

##### R3, the gas profile of outcomes: `metadata.gas_profile` and `contracts` as nearcore renders them

- *VM.* `NearState.actionProfile` (name and burnt gas of each `ActionCosts` entry) and `VMOutcome.actionProfile`; `gasProfile.actionBurnt`
  is their sum, which the fastvm differential test checks on every run. `applyCharge` adds the gas a charge burnt to the entry the
  charge pays: a charge names its fee by a selector (`ActionFees -> Fee`), and `costProbe` (a fee table whose entry number k has the send
  fee 2^k) reads the selector's answer to tell the entry without changing how charges are written (`actionCostName`: `transfer` when
  the selector includes the transfer fee, as nearcore profiles the whole payment of a transfer under it). `newReceipt` is profiled under
  `new_action_receipt` (nearcore pays the data receipts' base fees together with it), `burn` under `new_data_receipt_byte`, `pay` under
  `gas_key_byte`. Added: `actionCostNames`, `costProbe`, `actionCostName`, `addActionCost`, `NearState.profileAction`; changed:
  `applyCharge` (each branch also updates the profile; the gas counter and every field it set before are as they were), `outcomeOfExecution`
  and `graphIssue` (one more field each). The host function costs and the Wasm gas were already in `VMOutcome.gasProfile`.
- *Runtime.* `GasProfileSplit` (action costs, host function costs, Wasm gas) and `ContractRef`; `ExecutionOutcome.profile` is the sum of the
  profiles of the receipt's VM calls (nearcore profiles only what the VM burnt: the fees of non-VM actions are not in `gas_profile`, which
  is `[]` for such a receipt, as the localnet shows), and `ExecutionOutcome.contracts` the contract of the receiver before each action
  (`receiptContracts`: an account that does not exist yet has none, a deploy, `UseGlobalContract` or a deletion changes it for the actions
  after it, an action after the failed one gets none). Added: `Exec.profile`, `processedContracts`, `Account.contractRef`,
  `receiptContracts`; changed: `Exec.recordVMOutcome`, `outcomeOf`, `outcomesWithChanges` (one more field each).
- *Node.* `Chain/GasProfile.lean` turns the split into `ProfileDataV3` (the arrays indexed by the `ActionCosts` and `ExtCosts`
  discriminants) and the contracts into `AccountContract`; a transaction's outcome has `ExecutionMetadata::V1`, a receipt's `V4`, and
  the metadata is stored with the outcome (it is not part of the outcome hash). `Rpc/Views.lean` renders it from the stored metadata:
  `gas_profile` is `null` for `V1`, otherwise the costs that burnt gas as `{ cost_category, cost, gas_used }` (`ACTION_COST`, then
  `WASM_HOST_COST` with `WASM_INSTRUCTION`, each sorted by name), `contracts` only for `V4` (`null`, `{"local": hash}`,
  `{"global_hash": hash}`, `{"global_account_id": id}`).
- *Mechanical proof fixes.* `ChargeReservations.lean`: the five `simpa only [applyCharge, ...]` calls of
  `applyCharge_success_reservation` gained `NearState.profileAction` in their simp set (`applyCharge` now wraps the state in it). No theorem
  statement changed.
- *Result* (`rpc_conformance.py run`): all requests equal, 0 known gaps; the `gas_profile` and `contracts` normalisation of the harness is
  gone, so every outcome of the run (`tx`, `EXPERIMENTAL_tx_status`, the legacy form) compares the profile of each receipt.

##### Acceptance of R1 to R3 (one run of each, on the final build)

`--wfail` builds of `near-lean/{vm,runtime,chain,fastvm,node}` and of `contracts/w-near/verification` (`Model`, `Spec`, `runtime-adapter-tests`);
`Proofs` builds without `--wfail`, with the one `sorry` it already has. Cold build of `Model`, `Spec` and `runtime-adapter-tests` (build
directory removed, packages built): 70 s and 39 s before (commit `bee7dd6`), 47 s and 40 s after; the whole `NearRuntime` (with `NearVM`)
from scratch at `bee7dd6`: 893 s.

| Run | Result |
| --- | --- |
| `rpc_conformance.py run` | 1094 of 1094 requests equal, 0 known gaps, 0 other differences |
| `validator_accept.py` | `ok: true`, 449 of 449 outcomes equal, finality advanced after the stall |
| `soak.py --duration 1800` (full workload) | all nine checks ok, 2843 blocks applied |
| `fastvm-differential` | 200 programs, 42037 comparisons, 0 mismatches; storage probe as expected; wNEAR 3458 comparisons, 0 mismatches |
| `vm-tests` | 193 passed, 0 failed |
| `registered-replay-fast` (`replay_corpus.py`) | 436 pass, 0 fail, 0 unsupported |

#### V1 and V2: the validator on four shards, global contracts (SAF-8)

Sources: `tools/localnet/{localnet,validator_accept,soak,rpc_conformance,workload}.py`, `NearNode/Rpc/{Query,StateViews,Views}.lean`,
`NearNode/Chain/ApplyChunk.lean`, `NearNode/Validator/Drive.lean`.

##### V1, the validator topology on four shards

- **Topology.** `validator-sharded` (`localnet.py`): `neard localnet -v 2 -s 4` as `sharded` (boundary accounts `test1`, `test2`,
  `test3`, shard ids 3, 1, 0, 2 in layout order), chain id `test-chain-safe-near-validator-4s` (so `neard` reads the epoch config
  from the genesis, as for `validator`), kickout thresholds 0, inflation 1/40; only `node0` runs as `neard`, `node1`'s keys are the
  Lean node's. Two validators of equal stake: neither holds two thirds, so `neard` cannot finalize, produce an endorsed chunk
  or approve a block alone. `validator_accept.py`, `soak.py` and `rpc_conformance.py` take `--topology validator|validator-sharded`.
- **What had to change in the node: almost nothing.** The M8 code was already written per shard (`produceChunks` walks the
  layout's shards and asks `chunkProducerAfter` for each; `distributeChunk`, `distributeWitness` and the endorsements are per
  chunk; `Inclusion` waits for every shard; `Apply.applyBlock` applies all shards with the bandwidth scheduler and the congestion
  control of M3c, and builds each shard's incoming receipts with their proofs from the previous chunks). The first run on the new
  topology was accepted by `neard`, and the acceptance now fails unless this holds per shard (below). The one change that
  follows nearcore more exactly: an applied block's transactions leave the pool *before* the next chunks are prepared
  (`reconcile_transaction_pool` runs before `produce_chunks` in `on_block_accepted_with_optional_chunk_produce`); the node did it
  after, so every included transaction was prepared once more and dropped as an invalid nonce (`txsRejected` counted them; it is
  now 0). The chunk content was the same.
- **Assignment.** `get_chunk_producer_info_db`/`chunkProducerAfter` and `get_chunk_validator_assignments` are the M1c samplers,
  checked against nearcore at 46 heights; with two validators, one of them produces the chunk of a shard for a stretch of heights and
  both validate (one shard's producer endorses its own chunk). On the run below the Lean node produced new chunks on all four shards
  (the producers of shards 0 and 3 were mostly the Lean node, those of 1 and 2 mostly `neard`, changing with the epochs).
- **Tracking.** The node tracks every shard (it applies all of them, as the M8 decision says), which is a superset of the shards
  nearcore requires a validator to track; `neard` tracks its assigned shards. Hence the node validates a witness by comparing with its own
  execution rather than by re-executing on the recorded partial trie, and `ChunkExtra` of every shard is at hand for chunk
  production. Not done: a node that tracks only the shards it is assigned, with state sync at epoch changes and witness-only
  validation of the others.
- **Acceptance** (`validator_accept.py --topology validator-sharded`, besides the single-shard criteria): the Lean node produced new
  chunks on at least two shards, every shard has state roots checked and all equal, and at least one receipt outcome executed on
  another shard than its transaction's signer (a cross-shard receipt, with its proof, applied by `neard` and by the Lean node) is
  equal on both sides.

##### V2, global contracts

- **Workload.** `workload.py` `global_contracts` (it existed with three rounds; now twelve): `DeployGlobalContract` by code hash
  (from two shards) and by account id, users of both kinds on each of the four shards, calls (also across shards and through
  promises), an update of a by-account deployment (a new code and nonce reach every shard; users call the new code), switches
  (local to global by hash, global to global by account, global to local), the failures (`UseGlobalContract` of a hash and of an
  account that were never deployed: `GlobalContractDoesNotExist`; a deployment the account cannot pay: `LackBalanceForState`), a
  deployment of code that exists, and the deletion of an account that uses one.
- **RPC** (`neard` 2.13.4 serves both at protocol 86: `QueryRequest::ViewGlobalContractCode { code_hash }` and
  `ViewGlobalContractCodeByAccountId { account_id }`, answered from the first shard of the layout, `query_shard_uid`):
  `view_global_contract_code`, `view_global_contract_code_by_account_id` (`code_base64`, `hash`; the hash of the code for the by-account
  form), `NO_GLOBAL_CONTRACT_CODE` for code never distributed (`identifier` as `{hash}` or `{account_id}` and the Rust `Debug` text,
  `AccountId(AccountId("x"))`), and `view_code` of an account that uses a global contract (it was `NO_CONTRACT_CODE`; now the shared
  code, as `view_account_contract_code` resolves it). `GlobalContractDoesNotExist` is rendered in failures (it was
  `<unrendered failure>`).
- **Conformance.** 1602 requests on the single-shard topology (1725 on four shards), all equal, 0 known gaps, including 40 `call_function`, 133 `view_code`,
  96 + 95 global code queries and the state changes of every block; the run fails if the answers of `neard` do not contain the global
  cases (`metadata.contracts` entries `global_hash` and `global_account_id`, the four actions, `GlobalContractDoesNotExist`, and on
  several shards `GlobalContractDistribution` receipts) or if any failure is unrendered.

##### Acceptance of V1 and V2 (one run of each, on the final build)

| Run | Result |
| --- | --- |
| `validator_accept.py --topology validator-sharded --duration 520` (1) | ok: 799 blocks applied, 799 same hash (2 orphans neard holds), 3154 of 3154 state roots equal (shard 0: 766, 1: 796, 2: 796, 3: 796); Lean produced new chunks on all four shards (619, 149, 179, 649) and 471 blocks; 677 of 677 outcomes equal, 126 of them receipts that ran on another shard than the signer's; 173 transactions in 128 Lean chunks; 1570 witnesses of `neard` valid; stall test: head 784 -> 784 while stopped, 803 after, final 782 -> 801 |
| the same (2) | ok: 798 applied, 798 same hash, 3150 of 3150 roots, 688 of 688 outcomes (128 cross-shard), 1566 witnesses valid, stall test ok |
| `validator_accept.py --duration 360` (single shard) | ok: 559 applied, 559 same hash, 557 of 557 roots, 659 of 659 outcomes, 156 transactions in 56 Lean chunks, stall test ok |
| `soak.py --topology validator-sharded --duration 1800` (full workload, global contracts included) | all nine checks ok: 2802 blocks compared, 2802 hashes equal, 11046 of 11046 state roots equal over four shards, head 3 to 2779, final 2777, head minus final at most 13, no window without finality, lag at most 2 outside bursts and 1 inside (4 light bursts), median 0, no disconnect, RPC answered at every sample, longest turn of the loop 567 ms, 5526 witnesses valid, RSS 182 MB to 201 MB (peak 229 MB; the slope of 45 MB/h is a 30 minute estimate) |
| `rpc_conformance.py run` (single shard) | 1602 of 1602 requests equal, 0 known gaps, 0 other differences; restart from the store: caught up in seconds, final height equal afterwards |
| `rpc_conformance.py run --topology validator-sharded` | 1725 of 1725 equal, 0 known gaps, a `GlobalContractDistribution` receipt among the answers |
| `follow_accept.py --lightburst` | single: head reached after 2.2 s, max lag 8, 1015 of 1015 roots, caught up after the burst; sharded: 7.3 s, max lag 5, 4006 of 4006 roots, caught up; no disconnect; `localnet-follow: all agree` |

Not run: `fastvm-differential`, `vm-tests`, `registered-replay-fast`, the unit and conformance gates of the packages (nothing under
`near-lean/{vm,runtime,chain,fastvm,wasm,interface,crypto}` or `contracts/` changed), and any soak longer than 30 minutes.

## Open points

- Numeric performance target for M10, measured against nearcore: set and met in M10a above (M2's and M4's are proposed above).
- Whether crypto host functions in `NearVM` slow contract verification. If they
  do, `NearVM` takes host crypto as a parameter and the node supplies it. Today the VM takes its
  digests, `ed25519Verify` and `ecrecover` as parameters; `NearCrypto` is a separate package it can import later.
  Resolved in M3e: the VM takes a `HostCrypto` through the runtime configuration and the chain package supplies it.
