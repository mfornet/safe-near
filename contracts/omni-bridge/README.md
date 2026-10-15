# Omni Bridge (NEAR side)

Omni Bridge locker/controller contract on NEAR (`omni.bridge.near`): token transfers between NEAR and other chains verified by provers.

- Code hash: `FpsHmvso6geZzLc3Re1skvMAvssMSgKwofk9281Uafhz`
- Source: https://github.com/Near-One/omni-bridge @ `3124f85f7b02c45ad4517b059525963d53a7aab9`, crate `near/omni-bridge` v0.4.16
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.96.0, near-sdk 5.28.1, image `sourcescan/cargo-near:0.21.1-rust-1.96.0`
- Reproduced: exact

## Mainnet deployments

- `omni.bridge.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/omni-bridge
```
