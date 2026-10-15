# Wrapped NEAR (wNEAR)

The wNEAR fungible token (`wrap.near`), NEP-141 implementation from core-contracts.

- Code hash: `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`
- Source: https://github.com/near/core-contracts @ `54f8267436058567b66efdaba3e790394f7f1529`, crate `w-near` v1.0.0
- Pinned by: wasm-in-git-history (`w-near/res/w_near.wasm`)
- Build: docker-script, Rust 1.51.0, near-sdk 3.1.0, image `rust:1.51.0`
- Rust version basis: rust-toolchain file at commit = stable-2021-03-25 (Rust 1.51.0); commit message says 'Rebuild with contract builder'
- Reproduced: exact

## Mainnet deployments

- `wrap.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/w-near
```
