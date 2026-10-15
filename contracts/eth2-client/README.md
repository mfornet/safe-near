# Rainbow Bridge Ethereum 2 light client

Ethereum beacon-chain light client on NEAR used by the Rainbow Bridge after the Merge (`client-eth2.bridge.near`).

- Code hash: `C34bk5hjnmVQRD8f5YTiwPzh8A64iKe3wkTNaaxPhUts`
- Source: https://github.com/Near-One/rainbow-bridge @ `9783ca494c2cea62512d7396274087b487af0805`, crate `contracts/near/eth2-client` v0.7.1
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.86.0, near-sdk 5.24.1, image `sourcescan/cargo-near:0.16.0-rust-1.86.0`
- Reproduced: exact

## Mainnet deployments

- `client-eth2.bridge.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/eth2-client
```
