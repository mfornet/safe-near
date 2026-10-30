# Top-level account contract (linkdrop) on `near`

Contract deployed on the `near` top-level account: creates `*.near` accounts and implements linkdrops. Not in the initial list but every `.near` account creation goes through it.

- Code hash: `HiyC5tB1gBDpgR4x1guEp1orBde5PXqUYGoWaZfX3JGX`
- Source: https://github.com/near/near-linkdrop @ `9a6bb316f6b7c83b504ce9c94a80c37178097655`, crate `.` v0.1.1
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.86.0, near-sdk 5.17.0, image `sourcescan/cargo-near:0.16.0-rust-1.86.0`
- Reproduced: exact

## Mainnet deployments

- `near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/linkdrop
```

## Formalization

No verification project yet. near-lean runs this binary (weighted callbacks,
global-contract use), so a `ContractModel` instance can be built on it.

## Binary availability

The binary is omitted pending redistribution permission. Metadata, hashes and
source references remain available for local reproduction. A locally obtained
`contract.wasm` is ignored by Git and must not be committed.
