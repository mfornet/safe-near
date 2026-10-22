# Sputnik DAO v3.2 (sputnikdao2)

Sputnik DAO contract, version 3.2 as stored in the factory (`get_contracts_metadata`, default code). DAO instances upgrade to it through the factory. No deployed instance with this hash was identified yet.

- Code hash: `DtHZA1mUmGYeScEaUoUZYQGGFHSMpnjMCvkr5U9hJXuF`
- Source: https://github.com/near-daos/sputnik-dao-contract @ `2b0f34a3860460f285307ec2ccf36345acbe05a2`, crate `sputnikdao2` v2.3.1
- Pinned by: factory-metadata
- Build: cargo-near-reproducible, Rust 1.86.0, near-sdk 5.24, image `sourcescan/cargo-near:0.19.0-rust-1.86.0`
- Stored in: `sputnik-dao.near` (factory code blob, version [3,2], commit_id from get_contracts_metadata)
- Reproduced: exact

## Mainnet deployments

- none identified yet

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/sputnikdao2-v3.2
```

## Formalization in progress

[verification/](verification/README.md) contains checked source models for
policy, authorization, proposal and bounty paths, delegation, migration,
upgrade and blob storage, with a source-specific proof plan. A full
entry-point model and concrete runtime refinement remain open.
