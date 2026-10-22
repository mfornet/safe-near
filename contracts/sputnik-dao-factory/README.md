# Sputnik DAO factory (sputnikdao-factory2)

Factory that creates Sputnik DAO instances (`*.sputnik-dao.near`) and stores the versioned DAO code blobs used for creation and upgrades.

- Code hash: `BXd5idTXSnC7WRfxHmi7z4crw2F5WXQJ6MZUEv8DfnnY`
- Source: https://github.com/near-daos/sputnik-dao-contract @ `2b0f34a3860460f285307ec2ccf36345acbe05a2`, crate `sputnikdao-factory2` v0.2.1
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.86.0, near-sdk 5.24, image `sourcescan/cargo-near:0.19.0-rust-1.86.0`
- Reproduced: exact

## Mainnet deployments

- `sputnik-dao.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/sputnik-dao-factory
```

## Formalization in progress

[verification/](verification/README.md) contains the 18-method source model,
checked raw-storage and storage-projection proofs, and explicit remaining
runtime obligations. Concrete deployed refinement remains open.
