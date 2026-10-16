# NEAR contracts dataset

One folder per contract binary that is (or was) deployed on NEAR mainnet. Each
folder is self-contained and pins everything needed to rebuild the exact
on-chain binary (layout from `notes/PROJECT_STRUCTURE.md`):

```
contracts/<name>/
    README.md        What the contract is, where it is deployed, how it was pinned
    contract.toml    Machine-readable version of the same (schema below)
    contract.wasm    Binary fetched from chain (view_code), byte-for-byte
    hash.txt         base58(sha256(contract.wasm)) == NEAR `code_hash` of the account
    build.sh         Rebuilds contract.wasm from source/ into build/contract.wasm
    source/          git submodule: the upstream repository pinned at the exact commit
    verification/    (later) LEAN project with model/, spec/ and proofs/
```

`source/` is a git submodule so that the commit is pinned by git itself and the
full history is stored locally once the submodule is initialised:

```
git submodule update --init contracts/<name>/source
```

Two contracts built from the same repository at different commits get two
submodules (two folders). This duplicates clones but keeps every entry
independent, as described in `notes/design/SMART_CONTRACTS.md`.

## contract.toml

```toml
name = "sputnik-dao-factory"
title = "Sputnik DAO factory (sputnikdao-factory2)"
description = "..."
code_hash = "BXd5idTXSnC7WRfxHmi7z4crw2F5WXQJ6MZUEv8DfnnY"   # base58 sha256, as NEAR reports it

[source]
repo = "https://github.com/near-daos/sputnik-dao-contract"
commit = "2b0f34a3860460f285307ec2ccf36345acbe05a2"
path = "sputnikdao-factory2"        # crate directory inside the repo
version = "0.2.1"                   # Cargo package version at that commit
pinned_by = "nep330-metadata"       # how we know this commit produced the binary (see below)

[build]
method = "cargo-near-reproducible"  # or "docker-script"
rust = "1.86.0"
near_sdk = "5.24"
image = "sourcescan/cargo-near:0.19.0-rust-1.86.0"
image_digest = "sha256:..."
command = ["cargo", "near", "build", "non-reproducible-wasm", "--locked"]
output_wasm_path = "target/near/sputnikdao_factory2/sputnikdao_factory2.wasm"
reproduced = "exact"                # "exact" | "mismatch" | "failed" | "untested"
reproduced_hash = "BXd5..."         # hash obtained by the last verify_build.sh run
reproduced_at = "2026-10-15"

[[deployments]]
network = "mainnet"
account_id = "sputnik-dao.near"
deploy_block_height = 187622594     # first block at which the account has this code_hash
deploy_block_hash = "..."
code_hash_before = "..."            # code_hash at deploy_block_height - 1
verified_block_height = 220076000   # block at which contract.wasm was fetched
verified_block_hash = "..."
```

`source.pinned_by` values:

- `nep330-metadata`: the contract exposes `contract_source_metadata` (NEP-330)
  with the commit, docker image and build command. Strong evidence, and the
  build can be replayed with `cargo near build reproducible-wasm`.
- `wasm-in-git-history`: a `.wasm` blob committed to the upstream repository
  has exactly the on-chain hash; the pinned commit is the first commit that
  introduced the blob. The source at that commit is *presumed* to be what
  produced it. Rebuilding is best effort for pre-2023 toolchains.
- `release-asset`: a GitHub release asset has exactly the on-chain hash; the
  pinned commit is the release tag.
- `factory-metadata`: a factory contract stores the code together with the
  commit id (Sputnik DAO factory `get_contracts_metadata`).

`build.reproduced == "exact"` means `build.sh` has been run and produced a
binary with the same hash. Anything else is recorded honestly so the trust
level of each entry is explicit.

`build.sh` needs docker (and cargo-near for `cargo-near-reproducible` entries).
It clones `source/` into a temporary directory outside this repository (cargo-near
walks up to the top-level git repository it finds), checks out the pinned commit
and builds inside the pinned image. For `docker-script` entries the environment
variables `SAFE_NEAR_IMAGE`, `SAFE_NEAR_TOOLCHAIN` and `SAFE_NEAR_PLATFORM`
override the image, rustup toolchain and docker platform for experiments.

## Tools

- `tools/near_rpc.py` fetches code, computes NEAR code hashes, reads NEP-330
  metadata and binary-searches the archival RPC for the deploy block.
- `tools/fetch_binary.py contracts/<name>` fills `contract.wasm`, `hash.txt`
  and the deployment block fields for every deployment in `contract.toml`.
- `tools/verify_build.sh contracts/<name>` runs `build.sh`, reports whether the
  result matches `hash.txt` and records it in `contract.toml`.
- `tools/contract_toml.py` is the tiny TOML reader/writer the tools use (stdlib only).

See `contracts/CATALOG.md` for the list of contracts, including those not yet
turned into an entry.
