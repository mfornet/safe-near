# Smart contracts

The first goal is to formalize critical NEAR contracts. That starts with a
dataset: for each deployed binary, its source at the exact commit and a
reproducible build. A proof only applies to a deployed contract if we can
rebuild that binary from source.

Different deployed versions of the same contract (e.g. multisig, DAO) are
separate entries, even if their proofs end up sharing work.

## Layout

```text
contracts/<name>/
    source/         -- Upstream source, pinned as a git submodule
    contract.toml   -- Provenance, toolchain and expected code hash
    contract.wasm   -- On-chain binary
    hash.txt        -- NEAR code hash of that binary
    build.sh        -- Rebuilds build/contract.wasm from source/
    verification/   -- Lean model, specs and proofs, where they exist
```

`just reproduce <name>` rebuilds and compares hashes. The list of contracts is
in [contracts/CATALOG.md](../../contracts/CATALOG.md).

## Scope

1. Critical contracts in the NEAR ecosystem, picked by hand.
2. Contracts with significant recent usage.
3. Every contract ever deployed.

For each contract, try to find a contact who can review the formal statements.
