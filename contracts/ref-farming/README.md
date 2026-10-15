# Ref Finance farming v1.1.0

Ref Finance farming contract (`v2.ref-farming.near`). The upstream repo `ref-finance/ref-contracts` was removed from GitHub; the source is pinned through a public fork whose history contains the exact release binary.

- Code hash: `dp5BqcBKtpqEUTx5jF3fQKjUZ1gghEHo54oRLJ8uXZ4`
- Source: https://github.com/DevOfCredit/ref-contracts @ `fc34dd82bcfbc216d1461145679b28a05e1dc56a`, crate `ref-farming` v1.1.0
- Pinned by: wasm-in-git-history (`releases/ref_farming_release.wasm`)
- Build: docker-script, Rust 1.56.1, near-sdk 3.1.0, image `rust:1.56.1`
- Upstream repo: https://github.com/ref-finance/ref-contracts (404 as of 2026-10-15)
- Rust version basis: Dockerfile at commit: FROM rust:1.56.1; _rust_setup.sh installs stable-2021-11-01 (= 1.56.1)
- Reproduced: exact

## Mainnet deployments

- `v2.ref-farming.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/ref-farming
```
