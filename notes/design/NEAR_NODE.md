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

`NearNode` depends on `NearChain`, `NearRuntime` and `NearVM`. Nothing depends on
`NearNode`.

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
  verification package requires the node, chain or runtime packages, even
  transitively; only the node requires the node; no `@[extern]` /
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
JSON report. The first benchmarks time the existing `Near.Sha256.hash`, which
is the starting point for M2. The Rust oracle `tools/node-conformance` is
created in M1, when there are types to compare.

## Open points

- Numeric performance targets for M2, M4 and M10, measured against nearcore.
- Whether crypto host functions in `NearVM` slow contract verification. If they
  do, `NearVM` takes host crypto as a parameter and the node supplies it.
