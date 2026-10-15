# Aurora Engine (EVM on NEAR)

Aurora EVM engine contract (`aurora`), release 3.11.1. The on-chain binary equals the `aurora-engine.wasm` asset of the GitHub release.

- Code hash: `HrtBWvCMmVXRLG9vsYAFT7LfJ6mZtCSNTvYnXMF6fwzT`
- Source: https://github.com/aurora-is-near/aurora-engine @ `f296f06ab618468dff58cbef81732b1d0ee1782e` (tag `3.11.1`), crate `engine` v3.11.1
- Pinned by: release-asset
- Build: docker-script, Rust 1.99.0, image `nearprotocol/contract-builder:master-13430592a7be246dd5a29439791f4081e0107ff3-amd64`
- Rust version basis: rust-toolchain at tag 3.11.1; Makefile.toml task build-docker pins the builder image
- Reproduced: exact

## Mainnet deployments

- `aurora`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/aurora-engine
```
