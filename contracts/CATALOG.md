# Catalog of relevant NEAR contracts

Working list of contracts worth formalizing, grouped by upstream repository.
"Entry" links to a folder in this dataset; "pending" means we still have to pin
the source commit that produced the on-chain binary, or (for "build mismatch")
the commit is known but no toolchain tried so far reproduces the binary. Code hashes and block
heights were read from mainnet on 2026-10-15.

Legend for *pinned by*: see `contracts/README.md`.

## Dataset entries (status as of 2026-10-15)

| Entry | Mainnet account(s) | Deploy block(s) | Build | Rust | Reproduced |
|---|---|---|---|---|---|
| [aurora-engine](aurora-engine/) | `aurora` | 218961590 | docker-script | 1.99.0 | **exact** |
| [eth2-client](eth2-client/) | `client-eth2.bridge.near` | 193402297 | cargo-near-reproducible | 1.86.0 | **exact** |
| [intents-defuse](intents-defuse/) | `intents.near` | 218982375 | cargo-near-reproducible | 1.97.1 | **exact** |
| [linkdrop](linkdrop/) | `near` | 163297127 | cargo-near-reproducible | 1.86.0 | **exact** |
| [mpc-contract](mpc-contract/) | `v1.signer` | 217179197 | cargo-near-reproducible | 1.97.1 | **exact** |
| [omni-bridge](omni-bridge/) | `omni.bridge.near` | 216369342 | cargo-near-reproducible | 1.96.0 | **exact** |
| [ref-farming](ref-farming/) | `v2.ref-farming.near` | 81183973 | docker-script | 1.56.1 | **exact** |
| [skyward](skyward/) | `skyward.near` | 40785914 | docker-script | 1.51.0 | **exact** |
| [sputnik-dao-factory](sputnik-dao-factory/) | `sputnik-dao.near` | 187622594 | cargo-near-reproducible | 1.86.0 | **exact** |
| [sputnikdao2-v3.2](sputnikdao2-v3.2/) | (factory blob) |  | cargo-near-reproducible | 1.86.0 | **exact** |
| [w-near](w-near/) | `wrap.near` | 35438886 | docker-script | 1.51.0 | **exact** |

`exact` means `tools/verify_build.sh` rebuilt a byte-identical binary. Only
entries that reproduce exactly are kept in the dataset. Entries whose source
builds but whose hash differs from the on-chain one were removed on 2026-10-15
and are listed below as *pending (build mismatch)*, with the toolchain tried and
the hash obtained, so the work can be resumed.

### Removed: source pinned but binary not reproduced

| Contract | Mainnet account(s) | Deploy block(s) | Source commit | Toolchains tried | Hash obtained |
|---|---|---|---|---|---|
| core-contracts whitelist | `lockup-whitelist.near` | 13470017 | `498a7a33` | rust 1.43.1 | `G17wd6M3s4G5G1ZMo9cqqY6NNMqNmN8ennjsHMMmEvQV` |
| core-contracts staking-pool-factory | `poolv1.near` | 13470023 | `1cacc9db` | rust 1.45.0 | `H2XG5AXRaN2xzQYzhJsZHNnmVi84QaE854DtTHWdauUZ` |
| core-contracts staking-pool v0.4.0 | `zavodil.poolv1.near`, `astro-stakers.poolv1.near`, `aurora.poolv1.near` | 14713227, 16781232, 46292100 | `1cacc9db` | rust 1.45.0 | `9oeRF2xmAJhHjz6QdPAvMGjwLvrMfnbQ78n4bTgg2bFC` |
| core-contracts multisig (v1) | `aurora.near` | 16065524 | `f93c146d` | rust 1.46.0 | `DUagmD8x4Lz6YD9tzmRU8tY6EGa4KU7b6TrFHe6xJxtE` |
| core-contracts lockup-factory | `lockup.near` | 81149275 | `dad58eb5` | contract-builder + stable-2020-10-08, rust 1.47.0 | `6buNZ4n1YSaM1PJdN3xCgUcrgBuvFy3hMCbG2XnSre9Z` (the factory embeds a `lockup_contract.wasm` that matches no committed blob) |
| sputnikdao2 v2.0 | `near.sputnik-dao.near`, `aurora.sputnik-dao.near` | 59914831, 44791625 | `c2cf1553` (factory metadata; blob first committed at `d2819811`) | rust 1.50.0, 1.51.0, 1.52.1, 1.53.0 | all differ |
| sputnikdao2 v3.1 (crate 2.3.1) | `ref-finance.sputnik-dao.near`, `burrow.sputnik-dao.near` | 129764834, 135379496 | `3d568f95` | rust 1.77.2, 1.78.0, 1.79.0, 1.80.1, 1.81.0, 1.82.0 | all differ (1.81.0: 495672 bytes vs 539647 on chain) |
| rainbow-bridge eth-client | `client.bridge.near` | 67843198 | `25793907` | rust 1.47.0, contract-builder + stable-2020-10-08 | `3rhaWYsQGnmLKiJ1f48eQAWispwrR8QRsK2gCVnGKDhQ` |
| rainbow-bridge eth-prover v2.0.0 | `prover.bridge.near` | 114343967 | `6620a56e` | rust 1.68.0, contract-builder:latest | `9qagR6Qbxt8B3nCddKS4nnn3VVJn98rV6AEksQjiiPEn` |

For all of these the on-chain binary was found as a committed `*.wasm` blob in
the upstream repository (or, for sputnikdao2 v2.0, named by the factory
metadata), so the source commit is known; what is missing is the exact
toolchain (rustc / wasm-opt / profile) that produced the committed blob.

## near/core-contracts (https://github.com/near/core-contracts)

| Contract | Mainnet account(s) | Code hash | Entry | Pinned by |
|---|---|---|---|---|
| w-near | `wrap.near` | `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1` | [w-near](w-near/) | wasm in git history |
| whitelist | `lockup-whitelist.near` | `HBt2PRRoMTaipV1E9k5jrETRntz7dyZHLE847yJzoCG5` | pending (build mismatch) | wasm in git history |
| staking-pool-factory | `poolv1.near` | `FjtxkkaKDKCW1F6HgsuYvnQ9GMxrzhnkQwCm52G9gYuA` | pending (build mismatch) | wasm in git history |
| staking-pool | every `*.poolv1.near` | `J1arLz48fgXcGyCPVckFwLnewNH6j1uw79thsvwqGYTY` | pending (build mismatch) | wasm in git history |
| lockup-factory | `lockup.near` | `5R7Lnqvyggga6YAn81M64UvQcGGmzrUQiCCsMeoryP33` | pending (build mismatch) | wasm in git history |
| lockup | `*.lockup.near` instances | several versions in use | pending | need to sample instances and match against `lockup/res/lockup_contract.wasm` history |
| multisig (v1) | `aurora.near` (and many personal multisigs) | `55E7imniT2uuYrECn17qJAk9fLcwQW4ftNSwmCJL5Di` | pending (build mismatch) | wasm in git history |
| multisig2 | unknown instances | - | pending | find instances |
| voting | `vote.near` has no code today | - | not deployed | - |
| multisig-factory, lockup (v2/v3), state-manipulation | - | - | pending | find instances |

## near/near-linkdrop (not in the initial list, but the `near` top-level account)

| Contract | Account | Code hash | Entry | Pinned by |
|---|---|---|---|---|
| linkdrop | `near` | `HiyC5tB1gBDpgR4x1guEp1orBde5PXqUYGoWaZfX3JGX` | [linkdrop](linkdrop/) | NEP-330 metadata |
| registrar-opener (houseofstake/tla-contracts) | `registrar` | `DGpi3vGXeiJJ6gps8t5CDcDr5DbuzWXTMc6CVWcdWCXt` | pending | NEP-330 metadata available (commit `c33edd7a`) |

## Ref Finance / Rhea Finance

The original `ref-finance/ref-contracts` repository returns 404 on GitHub (removed or made private).
Public forks exist; `DevOfCredit/ref-contracts` contains the exact `v2.ref-farming.near` binary in its history.
None of the Ref/Rhea contracts expose NEP-330 metadata.

| Contract | Account | Version (view) | Code hash | Entry | Status |
|---|---|---|---|---|---|
| ref-exchange | `v2.ref-finance.near` | 1.9.20 | `25eNFdfK76NUEZn4cDgq1xQYKjxKCuzgXmPB3SHBRW4Y` | pending | not found in the fork's history (fork last pushed 2026-01); need a source for 1.9.20 |
| ref-farming | `v2.ref-farming.near` | 1.1.0 | `dp5BqcBKtpqEUTx5jF3fQKjUZ1gghEHo54oRLJ8uXZ4` | [ref-farming](ref-farming/) | wasm in fork history |
| boost-farming | `boostfarm.ref-labs.near` | 0.5.0 | `Dpwz7Ju2n8cTfKsFTyNsoptUaHzzGRZrffab8WGh7ybh` | pending | repo `ref-finance/boost-farming`? not located yet |
| DCL swap (v2) | `dclv2.ref-labs.near` | 2.3.15 | `8FYiayAinMQr5aTLmYuPYNReqeLeLmrz3ceUXgdsuHgE` | pending | repo not located yet |
| Burrow (burrowland) | `contract.main.burrow.near` | 0.16.2 | `6Nek1MZ8cwJJ2xMQAUWup9V5AToYS9rkTxJfwo6BCpFa` | pending | repo `ref-finance/burrowland` cloned; no committed wasm matches, need to build from the 0.16.2 tag/commit |
| REF token | `token.v2.ref-finance.near` | - | `HagtKcVnSk6eJrg9e4X4Rpvw4ACCrpJjkrdWavLNtggZ` | pending | `ref-finance/ref-token` |
| xREF | `xtoken.ref-finance.near` | - | `5g2CDRuEV1s3UpVfuaNgGiiX4vwHaaLBwZ7ygnePDPPE` | pending | `ref-finance/ref-ve`? |
| rNEAR (Rhea liquid staking) | tbd | - | - | pending | `ref-finance/rnear-contract` |
| Rhea org (`rhea-finance`) | - | - | - | - | only SDKs/frontends, no contract repos as of 2026-10-15 |

## near/intents (https://github.com/near/intents/tree/main/contracts)

| Contract | Account | Version | Code hash | Entry | Pinned by |
|---|---|---|---|---|---|
| defuse (verifier) | `intents.near` | 0.4.5 | `BtA1BEFNS619KkvXFsgcpQ21Tb5yMm32aaUkn7xNothk` | [intents-defuse](intents-defuse/) | NEP-330 metadata |
| poa-factory, poa-token | tbd (bridged `*.omft.near` tokens) | - | - | pending | find accounts |
| escrow-swap, treasury-logger, wallet, global-deployer, outlayer | tbd | - | - | pending | check which are on mainnet |

## near/mpc (https://github.com/near/mpc)

| Contract | Account | Version | Code hash | Entry | Pinned by |
|---|---|---|---|---|---|
| mpc-contract | `v1.signer` | 3.16.0 | `BqN6GrovBmBD7g41p5GvXMVUJcLgipuVGXF6ps6hQgBy` | [mpc-contract](mpc-contract/) | NEP-330 metadata |
| tee-verifier, chain-gateway | tbd | - | - | pending | check deployments |

## Near-One/rainbow-bridge (https://github.com/Near-One/rainbow-bridge)

| Contract | Account | Code hash | Entry | Pinned by |
|---|---|---|---|---|
| eth-client (PoW light client) | `client.bridge.near` | `34xWsAeyJxHrHg3UPd8Kg4Kq2sc48z1pioV1YZDkfiry` | pending (build mismatch) | wasm in git history |
| eth2-client | `client-eth2.bridge.near` | `C34bk5hjnmVQRD8f5YTiwPzh8A64iKe3wkTNaaxPhUts` | [eth2-client](eth2-client/) | NEP-330 metadata |
| eth-prover | `prover.bridge.near` | `EW9ru3nBhTzfHAbAfKfAKfm1KkZvyvZgT1nvXFh8yDAy` | pending (build mismatch) | wasm in git history |
| bridge token factory (rainbow-token-connector) | `factory.bridge.near` | `CC9dZfmmnYtYCtPzwEdgBmT1wpWYTAL5nNvK4RHEUgAg` | pending | lives in `Near-One/rainbow-token-connector`, not scanned yet |

## Near-One/omni-bridge (https://github.com/Near-One/omni-bridge)

| Contract | Account | Version | Code hash | Entry | Pinned by |
|---|---|---|---|---|---|
| omni-bridge | `omni.bridge.near` | 0.4.16 | `FpsHmvso6geZzLc3Re1skvMAvssMSgKwofk9281Uafhz` | [omni-bridge](omni-bridge/) | NEP-330 metadata |
| omni-token, token-deployer, evm-prover, wormhole-omni-prover-proxy, mpc-omni-prover | tbd | - | - | pending | find accounts (likely `*.omni.bridge.near` / `*.omdep.near`) |

## skyward-finance/contracts

| Contract | Account | Code hash | Entry | Pinned by |
|---|---|---|---|---|
| skyward | `skyward.near` | `G9NQfb8SpWysM29Ngbu5azci28JfobJqrtUVpQdiDkL8` | [skyward](skyward/) | wasm in git history |
| skyward lockup, permissions | tbd | - | pending | - |

## Meta Pool

The on-chain `get_contract_info` points at `github.com/Meta-Pool/liquid-staking-contract` (not the `Narwallets/meta-pool` repo from the list).

| Contract | Account | Version | Code hash | Entry | Status |
|---|---|---|---|---|---|
| metapool | `meta-pool.near` | 2.0.0 | `J6pS9R23vzbwxGB8eMq4qrn8UhciEYHsVbR9UJPyLNxh` | pending | no committed wasm matches in either repo; need to build 2.0.0 |
| meta-token | `meta-token.near` | - | `FAwQjv4expf9L2r5EngGqJRFYAvkc4A4NkWQbWLj185k` | pending | same |

## aurora-is-near/aurora-engine

| Contract | Account | Version | Code hash | Entry | Pinned by |
|---|---|---|---|---|---|
| aurora-engine | `aurora` | 3.11.1 | `HrtBWvCMmVXRLG9vsYAFT7LfJ6mZtCSNTvYnXMF6fwzT` | [aurora-engine](aurora-engine/) | release asset digest |
| xcc-router | deployed per-account under `aurora` | - | - | pending | release asset `aurora-xcc-router.wasm` |
| `aurora.near` (owner) | `aurora.near` | - | `55E7imniT2uuYrECn17qJAk9fLcwQW4ftNSwmCJL5Di` | pending (build mismatch) | core-contracts multisig v1 |

## vgrichina/web4

| Contract | Account | Code hash | Entry | Status |
|---|---|---|---|---|
| web4 (AssemblyScript) | `web4.near` | `2oVhrAkXEBS8nT8bTw95BiB9Digo7bBfnVmaA7P3bkCM` | pending | AssemblyScript build, no NEP-330; source commit not pinned |

## frol/near-dns

| Contract | Account | Code hash | Entry | Status |
|---|---|---|---|---|
| dns-contract | `near-dns.near` | `8pwS1Kf9n7W7MYnkCHqSai16nA8evAwX418sj8Gf3WyX` | pending | NEP-330 says built from fork `kmjayadeep/near-dns` @ `1134e0a9`; `dns.near` has no code |

## near-daos/sputnik-dao-contract

| Contract | Account(s) | Code hash | Entry | Pinned by |
|---|---|---|---|---|
| sputnikdao-factory2 | `sputnik-dao.near` | `BXd5idTXSnC7WRfxHmi7z4crw2F5WXQJ6MZUEv8DfnnY` | [sputnik-dao-factory](sputnik-dao-factory/) | NEP-330 metadata |
| sputnikdao2 v2.0 | `near.sputnik-dao.near`, `aurora.sputnik-dao.near` | `8RMeZ5cXDap6TENxaJKtigRYf3n139iHmTRe8ZUNey6N` | pending (build mismatch) | factory metadata + wasm in git |
| sputnikdao2 v2.1 | tbd | `8jmhwSkNeAWCRqsr2KoD7d8BzDYorEz3a3iHuM9Gykrg` | pending | factory says `UNOFFICIAL_SCRIPT_DATA`, no commit |
| sputnikdao2 v3.0 | `marketing.`, `devhub.`, `build.sputnik-dao.near` | `2Zof1Tyy4pMeJM48mDSi5ww2QQhTz97b9S8h6W6r4HnK` | pending | factory commit `86cc77a0` is not in the repo; binary is committed as `sputnikdao2_v_3_0.wasm` |
| sputnikdao2 v3.1 | `ref-finance.`, `burrow.sputnik-dao.near` | `4zSoHkLjJWZm34Psd4Eq2WUXHELt6LxtKmUXpsZWAECp` | pending (build mismatch) | wasm in git history |
| sputnikdao2 v3.2 | none found yet (factory default) | `DtHZA1mUmGYeScEaUoUZYQGGFHSMpnjMCvkr5U9hJXuF` | [sputnikdao2-v3.2](sputnikdao2-v3.2/) | factory metadata |
| sputnik-staking | tbd | - | pending | find instances |

## How the pinning was done

- NEP-330: `tools/near_rpc.py metadata <account>`.
- Git history: every `*.wasm` blob in every commit of the upstream repo was hashed
  (base58 sha256) and compared with the on-chain `code_hash`; the entry is pinned to
  the first commit that introduced the matching blob.
- Deploy block: `tools/near_rpc.py deploy-block <account>` binary-searches the
  archival RPC for the first block at which the account carries the current hash.
  Cross-checked with NearBlocks for `wrap.near` and `intents.near`.
