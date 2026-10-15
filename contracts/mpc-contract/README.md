# NEAR MPC / Chain Signatures contract

Coordinates the MPC network: signature requests, key resharing, participant and TEE attestation management (`v1.signer`).

- Code hash: `BqN6GrovBmBD7g41p5GvXMVUJcLgipuVGXF6ps6hQgBy`
- Source: https://github.com/near/mpc @ `3499a2a44207df89699c9791e21623613a365a16`, crate `crates/contract` v3.16.0
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.97.1, near-sdk 5.29.0, image `sourcescan/cargo-near:0.22.0-rust-1.97.1`
- Reproduced: exact

## Mainnet deployments

- `v1.signer`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/mpc-contract
```
