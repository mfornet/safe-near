# Skyward Finance

Skyward Finance token sale / IDO platform contract (`skyward.near`).

- Code hash: `G9NQfb8SpWysM29Ngbu5azci28JfobJqrtUVpQdiDkL8`
- Source: https://github.com/skyward-finance/contracts @ `a814cbd3a0fbdf7a90180c8959b1f49aea247f84`, crate `skyward` v0.1.0
- Pinned by: wasm-in-git-history (`release/skyward.wasm`)
- Build: docker-script, Rust 1.51.0, near-sdk 3.1.0, image `rust:1.51.0`
- Rust version basis: Dockerfile added to the repo shortly after this commit uses rust:1.51.0; docker_build.sh compares against release/skyward.wasm
- Reproduced: exact

## Mainnet deployments

- `skyward.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/skyward
```
